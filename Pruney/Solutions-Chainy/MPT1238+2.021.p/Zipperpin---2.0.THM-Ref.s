%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kSBpwuSq5X

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:59 EST 2020

% Result     : Theorem 3.12s
% Output     : Refutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 140 expanded)
%              Number of leaves         :   25 (  49 expanded)
%              Depth                    :   10
%              Number of atoms          :  744 (2024 expanded)
%              Number of equality atoms :   15 (  23 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t49_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( r1_tarski @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) @ ( k1_tops_1 @ A @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( r1_tarski @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) @ ( k1_tops_1 @ A @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t49_tops_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) @ ( k1_tops_1 @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) )
      | ( ( k4_subset_1 @ X24 @ X23 @ X25 )
        = ( k2_xboole_0 @ X23 @ X25 ) ) ) ),
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
    ~ ( r1_tarski @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('8',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X26 @ X27 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('9',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X26 @ X27 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('14',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) )
      | ( ( k4_subset_1 @ X24 @ X23 @ X25 )
        = ( k2_xboole_0 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
        = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) )
    = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','18'])).

thf('20',plain,(
    ~ ( r1_tarski @ ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['6','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('23',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X21 @ X20 @ X22 ) @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('27',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('29',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( r1_tarski @ X28 @ X30 )
      | ( r1_tarski @ ( k1_tops_1 @ X29 @ X28 ) @ ( k1_tops_1 @ X29 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['34'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('36',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X3 @ ( k2_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['33','37'])).

thf('39',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( r1_tarski @ X28 @ X30 )
      | ( r1_tarski @ ( k1_tops_1 @ X29 @ X28 ) @ ( k1_tops_1 @ X29 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('46',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('47',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('49',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_tarski @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('51',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['45','52'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('54',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_tarski @ X15 @ X14 )
      | ( r1_tarski @ ( k2_xboole_0 @ X13 @ X15 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) )
      | ~ ( r1_tarski @ X0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['38','55'])).

thf('57',plain,(
    $false ),
    inference(demod,[status(thm)],['20','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kSBpwuSq5X
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:38:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 3.12/3.36  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.12/3.36  % Solved by: fo/fo7.sh
% 3.12/3.36  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.12/3.36  % done 2642 iterations in 2.936s
% 3.12/3.36  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.12/3.36  % SZS output start Refutation
% 3.12/3.36  thf(sk_A_type, type, sk_A: $i).
% 3.12/3.36  thf(sk_B_type, type, sk_B: $i).
% 3.12/3.36  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 3.12/3.36  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.12/3.36  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 3.12/3.36  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.12/3.36  thf(sk_C_type, type, sk_C: $i).
% 3.12/3.36  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.12/3.36  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 3.12/3.36  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.12/3.36  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.12/3.36  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.12/3.36  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.12/3.36  thf(t49_tops_1, conjecture,
% 3.12/3.36    (![A:$i]:
% 3.12/3.36     ( ( l1_pre_topc @ A ) =>
% 3.12/3.36       ( ![B:$i]:
% 3.12/3.36         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.12/3.36           ( ![C:$i]:
% 3.12/3.36             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.12/3.36               ( r1_tarski @
% 3.12/3.36                 ( k4_subset_1 @
% 3.12/3.36                   ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ 
% 3.12/3.36                   ( k1_tops_1 @ A @ C ) ) @ 
% 3.12/3.36                 ( k1_tops_1 @
% 3.12/3.36                   A @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ) ))).
% 3.12/3.36  thf(zf_stmt_0, negated_conjecture,
% 3.12/3.36    (~( ![A:$i]:
% 3.12/3.36        ( ( l1_pre_topc @ A ) =>
% 3.12/3.36          ( ![B:$i]:
% 3.12/3.36            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.12/3.36              ( ![C:$i]:
% 3.12/3.36                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.12/3.36                  ( r1_tarski @
% 3.12/3.36                    ( k4_subset_1 @
% 3.12/3.36                      ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ 
% 3.12/3.36                      ( k1_tops_1 @ A @ C ) ) @ 
% 3.12/3.36                    ( k1_tops_1 @
% 3.12/3.36                      A @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ) ) )),
% 3.12/3.36    inference('cnf.neg', [status(esa)], [t49_tops_1])).
% 3.12/3.36  thf('0', plain,
% 3.12/3.36      (~ (r1_tarski @ 
% 3.12/3.36          (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 3.12/3.36           (k1_tops_1 @ sk_A @ sk_C)) @ 
% 3.12/3.36          (k1_tops_1 @ sk_A @ 
% 3.12/3.36           (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)))),
% 3.12/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.36  thf('1', plain,
% 3.12/3.36      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.12/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.36  thf('2', plain,
% 3.12/3.36      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.12/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.36  thf(redefinition_k4_subset_1, axiom,
% 3.12/3.36    (![A:$i,B:$i,C:$i]:
% 3.12/3.36     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 3.12/3.36         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 3.12/3.36       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 3.12/3.36  thf('3', plain,
% 3.12/3.36      (![X23 : $i, X24 : $i, X25 : $i]:
% 3.12/3.36         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 3.12/3.36          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24))
% 3.12/3.36          | ((k4_subset_1 @ X24 @ X23 @ X25) = (k2_xboole_0 @ X23 @ X25)))),
% 3.12/3.36      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 3.12/3.36  thf('4', plain,
% 3.12/3.36      (![X0 : $i]:
% 3.12/3.36         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 3.12/3.36            = (k2_xboole_0 @ sk_B @ X0))
% 3.12/3.36          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.12/3.36      inference('sup-', [status(thm)], ['2', '3'])).
% 3.12/3.36  thf('5', plain,
% 3.12/3.36      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)
% 3.12/3.36         = (k2_xboole_0 @ sk_B @ sk_C))),
% 3.12/3.36      inference('sup-', [status(thm)], ['1', '4'])).
% 3.12/3.36  thf('6', plain,
% 3.12/3.36      (~ (r1_tarski @ 
% 3.12/3.36          (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 3.12/3.36           (k1_tops_1 @ sk_A @ sk_C)) @ 
% 3.12/3.36          (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 3.12/3.36      inference('demod', [status(thm)], ['0', '5'])).
% 3.12/3.36  thf('7', plain,
% 3.12/3.36      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.12/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.36  thf(dt_k1_tops_1, axiom,
% 3.12/3.36    (![A:$i,B:$i]:
% 3.12/3.36     ( ( ( l1_pre_topc @ A ) & 
% 3.12/3.36         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.12/3.36       ( m1_subset_1 @
% 3.12/3.36         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 3.12/3.36  thf('8', plain,
% 3.12/3.36      (![X26 : $i, X27 : $i]:
% 3.12/3.36         (~ (l1_pre_topc @ X26)
% 3.12/3.36          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 3.12/3.36          | (m1_subset_1 @ (k1_tops_1 @ X26 @ X27) @ 
% 3.12/3.36             (k1_zfmisc_1 @ (u1_struct_0 @ X26))))),
% 3.12/3.36      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 3.12/3.36  thf('9', plain,
% 3.12/3.36      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 3.12/3.36         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.12/3.36        | ~ (l1_pre_topc @ sk_A))),
% 3.12/3.36      inference('sup-', [status(thm)], ['7', '8'])).
% 3.12/3.36  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 3.12/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.36  thf('11', plain,
% 3.12/3.36      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 3.12/3.36        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.12/3.36      inference('demod', [status(thm)], ['9', '10'])).
% 3.12/3.36  thf('12', plain,
% 3.12/3.36      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.12/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.36  thf('13', plain,
% 3.12/3.36      (![X26 : $i, X27 : $i]:
% 3.12/3.36         (~ (l1_pre_topc @ X26)
% 3.12/3.36          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 3.12/3.36          | (m1_subset_1 @ (k1_tops_1 @ X26 @ X27) @ 
% 3.12/3.36             (k1_zfmisc_1 @ (u1_struct_0 @ X26))))),
% 3.12/3.36      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 3.12/3.36  thf('14', plain,
% 3.12/3.36      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 3.12/3.36         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.12/3.36        | ~ (l1_pre_topc @ sk_A))),
% 3.12/3.36      inference('sup-', [status(thm)], ['12', '13'])).
% 3.12/3.36  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 3.12/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.36  thf('16', plain,
% 3.12/3.36      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 3.12/3.36        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.12/3.36      inference('demod', [status(thm)], ['14', '15'])).
% 3.12/3.36  thf('17', plain,
% 3.12/3.36      (![X23 : $i, X24 : $i, X25 : $i]:
% 3.12/3.36         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 3.12/3.36          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24))
% 3.12/3.36          | ((k4_subset_1 @ X24 @ X23 @ X25) = (k2_xboole_0 @ X23 @ X25)))),
% 3.12/3.36      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 3.12/3.36  thf('18', plain,
% 3.12/3.36      (![X0 : $i]:
% 3.12/3.36         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 3.12/3.36            = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0))
% 3.12/3.36          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.12/3.36      inference('sup-', [status(thm)], ['16', '17'])).
% 3.12/3.36  thf('19', plain,
% 3.12/3.36      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 3.12/3.36         (k1_tops_1 @ sk_A @ sk_C))
% 3.12/3.36         = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)))),
% 3.12/3.36      inference('sup-', [status(thm)], ['11', '18'])).
% 3.12/3.36  thf('20', plain,
% 3.12/3.36      (~ (r1_tarski @ 
% 3.12/3.36          (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)) @ 
% 3.12/3.36          (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 3.12/3.36      inference('demod', [status(thm)], ['6', '19'])).
% 3.12/3.36  thf('21', plain,
% 3.12/3.36      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.12/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.36  thf('22', plain,
% 3.12/3.36      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.12/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.36  thf(dt_k4_subset_1, axiom,
% 3.12/3.36    (![A:$i,B:$i,C:$i]:
% 3.12/3.36     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 3.12/3.36         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 3.12/3.36       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 3.12/3.36  thf('23', plain,
% 3.12/3.36      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.12/3.36         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 3.12/3.36          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21))
% 3.12/3.36          | (m1_subset_1 @ (k4_subset_1 @ X21 @ X20 @ X22) @ 
% 3.12/3.36             (k1_zfmisc_1 @ X21)))),
% 3.12/3.36      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 3.12/3.36  thf('24', plain,
% 3.12/3.36      (![X0 : $i]:
% 3.12/3.36         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 3.12/3.36           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.12/3.36          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 3.12/3.36      inference('sup-', [status(thm)], ['22', '23'])).
% 3.12/3.36  thf('25', plain,
% 3.12/3.36      ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 3.12/3.36        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.12/3.36      inference('sup-', [status(thm)], ['21', '24'])).
% 3.12/3.36  thf('26', plain,
% 3.12/3.36      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)
% 3.12/3.36         = (k2_xboole_0 @ sk_B @ sk_C))),
% 3.12/3.36      inference('sup-', [status(thm)], ['1', '4'])).
% 3.12/3.36  thf('27', plain,
% 3.12/3.36      ((m1_subset_1 @ (k2_xboole_0 @ sk_B @ sk_C) @ 
% 3.12/3.36        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.12/3.36      inference('demod', [status(thm)], ['25', '26'])).
% 3.12/3.36  thf('28', plain,
% 3.12/3.36      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.12/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.36  thf(t48_tops_1, axiom,
% 3.12/3.36    (![A:$i]:
% 3.12/3.36     ( ( l1_pre_topc @ A ) =>
% 3.12/3.36       ( ![B:$i]:
% 3.12/3.36         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.12/3.36           ( ![C:$i]:
% 3.12/3.36             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.12/3.36               ( ( r1_tarski @ B @ C ) =>
% 3.12/3.36                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 3.12/3.36  thf('29', plain,
% 3.12/3.36      (![X28 : $i, X29 : $i, X30 : $i]:
% 3.12/3.36         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 3.12/3.36          | ~ (r1_tarski @ X28 @ X30)
% 3.12/3.36          | (r1_tarski @ (k1_tops_1 @ X29 @ X28) @ (k1_tops_1 @ X29 @ X30))
% 3.12/3.36          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 3.12/3.36          | ~ (l1_pre_topc @ X29))),
% 3.12/3.36      inference('cnf', [status(esa)], [t48_tops_1])).
% 3.12/3.36  thf('30', plain,
% 3.12/3.36      (![X0 : $i]:
% 3.12/3.36         (~ (l1_pre_topc @ sk_A)
% 3.12/3.36          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.12/3.36          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ X0))
% 3.12/3.36          | ~ (r1_tarski @ sk_C @ X0))),
% 3.12/3.36      inference('sup-', [status(thm)], ['28', '29'])).
% 3.12/3.36  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 3.12/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.36  thf('32', plain,
% 3.12/3.36      (![X0 : $i]:
% 3.12/3.36         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.12/3.36          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ X0))
% 3.12/3.36          | ~ (r1_tarski @ sk_C @ X0))),
% 3.12/3.36      inference('demod', [status(thm)], ['30', '31'])).
% 3.12/3.36  thf('33', plain,
% 3.12/3.36      ((~ (r1_tarski @ sk_C @ (k2_xboole_0 @ sk_B @ sk_C))
% 3.12/3.36        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 3.12/3.36           (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 3.12/3.36      inference('sup-', [status(thm)], ['27', '32'])).
% 3.12/3.36  thf(d10_xboole_0, axiom,
% 3.12/3.36    (![A:$i,B:$i]:
% 3.12/3.36     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.12/3.36  thf('34', plain,
% 3.12/3.36      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 3.12/3.36      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.12/3.36  thf('35', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.12/3.36      inference('simplify', [status(thm)], ['34'])).
% 3.12/3.36  thf(t10_xboole_1, axiom,
% 3.12/3.36    (![A:$i,B:$i,C:$i]:
% 3.12/3.36     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 3.12/3.36  thf('36', plain,
% 3.12/3.36      (![X3 : $i, X4 : $i, X5 : $i]:
% 3.12/3.36         (~ (r1_tarski @ X3 @ X4) | (r1_tarski @ X3 @ (k2_xboole_0 @ X5 @ X4)))),
% 3.12/3.36      inference('cnf', [status(esa)], [t10_xboole_1])).
% 3.12/3.36  thf('37', plain,
% 3.12/3.36      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 3.12/3.36      inference('sup-', [status(thm)], ['35', '36'])).
% 3.12/3.36  thf('38', plain,
% 3.12/3.36      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 3.12/3.36        (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 3.12/3.36      inference('demod', [status(thm)], ['33', '37'])).
% 3.12/3.36  thf('39', plain,
% 3.12/3.36      ((m1_subset_1 @ (k2_xboole_0 @ sk_B @ sk_C) @ 
% 3.12/3.36        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.12/3.36      inference('demod', [status(thm)], ['25', '26'])).
% 3.12/3.36  thf('40', plain,
% 3.12/3.36      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.12/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.36  thf('41', plain,
% 3.12/3.36      (![X28 : $i, X29 : $i, X30 : $i]:
% 3.12/3.36         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 3.12/3.36          | ~ (r1_tarski @ X28 @ X30)
% 3.12/3.36          | (r1_tarski @ (k1_tops_1 @ X29 @ X28) @ (k1_tops_1 @ X29 @ X30))
% 3.12/3.36          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 3.12/3.36          | ~ (l1_pre_topc @ X29))),
% 3.12/3.36      inference('cnf', [status(esa)], [t48_tops_1])).
% 3.12/3.36  thf('42', plain,
% 3.12/3.36      (![X0 : $i]:
% 3.12/3.36         (~ (l1_pre_topc @ sk_A)
% 3.12/3.36          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.12/3.36          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 3.12/3.36          | ~ (r1_tarski @ sk_B @ X0))),
% 3.12/3.36      inference('sup-', [status(thm)], ['40', '41'])).
% 3.12/3.36  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 3.12/3.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.12/3.36  thf('44', plain,
% 3.12/3.36      (![X0 : $i]:
% 3.12/3.36         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.12/3.36          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 3.12/3.36          | ~ (r1_tarski @ sk_B @ X0))),
% 3.12/3.36      inference('demod', [status(thm)], ['42', '43'])).
% 3.12/3.36  thf('45', plain,
% 3.12/3.36      ((~ (r1_tarski @ sk_B @ (k2_xboole_0 @ sk_B @ sk_C))
% 3.12/3.36        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 3.12/3.36           (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 3.12/3.36      inference('sup-', [status(thm)], ['39', '44'])).
% 3.12/3.36  thf(t1_boole, axiom,
% 3.12/3.36    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 3.12/3.36  thf('46', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 3.12/3.36      inference('cnf', [status(esa)], [t1_boole])).
% 3.12/3.36  thf(t46_xboole_1, axiom,
% 3.12/3.36    (![A:$i,B:$i]:
% 3.12/3.36     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 3.12/3.36  thf('47', plain,
% 3.12/3.36      (![X11 : $i, X12 : $i]:
% 3.12/3.36         ((k4_xboole_0 @ X11 @ (k2_xboole_0 @ X11 @ X12)) = (k1_xboole_0))),
% 3.12/3.36      inference('cnf', [status(esa)], [t46_xboole_1])).
% 3.12/3.36  thf('48', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.12/3.36      inference('sup+', [status(thm)], ['46', '47'])).
% 3.12/3.36  thf(t44_xboole_1, axiom,
% 3.12/3.36    (![A:$i,B:$i,C:$i]:
% 3.12/3.36     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 3.12/3.36       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 3.12/3.36  thf('49', plain,
% 3.12/3.36      (![X8 : $i, X9 : $i, X10 : $i]:
% 3.12/3.36         ((r1_tarski @ X8 @ (k2_xboole_0 @ X9 @ X10))
% 3.12/3.36          | ~ (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X10))),
% 3.12/3.36      inference('cnf', [status(esa)], [t44_xboole_1])).
% 3.12/3.36  thf('50', plain,
% 3.12/3.36      (![X0 : $i, X1 : $i]:
% 3.12/3.36         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 3.12/3.36          | (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 3.12/3.36      inference('sup-', [status(thm)], ['48', '49'])).
% 3.12/3.36  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 3.12/3.36  thf('51', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 3.12/3.36      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.12/3.36  thf('52', plain,
% 3.12/3.36      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 3.12/3.36      inference('demod', [status(thm)], ['50', '51'])).
% 3.12/3.36  thf('53', plain,
% 3.12/3.36      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 3.12/3.36        (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 3.12/3.36      inference('demod', [status(thm)], ['45', '52'])).
% 3.12/3.36  thf(t8_xboole_1, axiom,
% 3.12/3.36    (![A:$i,B:$i,C:$i]:
% 3.12/3.36     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 3.12/3.36       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 3.12/3.36  thf('54', plain,
% 3.12/3.36      (![X13 : $i, X14 : $i, X15 : $i]:
% 3.12/3.36         (~ (r1_tarski @ X13 @ X14)
% 3.12/3.36          | ~ (r1_tarski @ X15 @ X14)
% 3.12/3.36          | (r1_tarski @ (k2_xboole_0 @ X13 @ X15) @ X14))),
% 3.12/3.36      inference('cnf', [status(esa)], [t8_xboole_1])).
% 3.12/3.36  thf('55', plain,
% 3.12/3.36      (![X0 : $i]:
% 3.12/3.36         ((r1_tarski @ (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0) @ 
% 3.12/3.36           (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 3.12/3.36          | ~ (r1_tarski @ X0 @ 
% 3.12/3.36               (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 3.12/3.36      inference('sup-', [status(thm)], ['53', '54'])).
% 3.12/3.36  thf('56', plain,
% 3.12/3.36      ((r1_tarski @ 
% 3.12/3.36        (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)) @ 
% 3.12/3.36        (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 3.12/3.36      inference('sup-', [status(thm)], ['38', '55'])).
% 3.12/3.36  thf('57', plain, ($false), inference('demod', [status(thm)], ['20', '56'])).
% 3.12/3.36  
% 3.12/3.36  % SZS output end Refutation
% 3.12/3.36  
% 3.12/3.37  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
