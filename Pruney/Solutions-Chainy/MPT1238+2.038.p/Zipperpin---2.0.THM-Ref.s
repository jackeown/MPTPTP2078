%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.W9iN7pQvvg

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:00 EST 2020

% Result     : Theorem 44.43s
% Output     : Refutation 44.43s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 159 expanded)
%              Number of leaves         :   33 (  58 expanded)
%              Depth                    :   11
%              Number of atoms          :  876 (2159 expanded)
%              Number of equality atoms :   24 (  32 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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
    ~ ( r1_tarski @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C_2 ) ) @ ( k1_tops_1 @ sk_A @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X30 ) )
      | ( ( k4_subset_1 @ X30 @ X29 @ X31 )
        = ( k2_xboole_0 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_2 )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ~ ( r1_tarski @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C_2 ) ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('8',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( l1_pre_topc @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X39 @ X40 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('9',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( l1_pre_topc @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X39 @ X40 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X30 ) )
      | ( ( k4_subset_1 @ X30 @ X29 @ X31 )
        = ( k2_xboole_0 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
        = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C_2 ) )
    = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['11','18'])).

thf('20',plain,(
    ~ ( r1_tarski @ ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C_2 ) ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['6','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X27 @ X26 @ X28 ) @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_2 )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('27',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( r1_tarski @ X41 @ X43 )
      | ( r1_tarski @ ( k1_tops_1 @ X42 @ X41 ) @ ( k1_tops_1 @ X42 @ X43 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( l1_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_2 ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_C_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_2 ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_C_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( r1_tarski @ sk_C_2 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_2 ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('34',plain,(
    ! [X9: $i] :
      ( r1_tarski @ k1_xboole_0 @ X9 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t9_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('35',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ X23 @ X24 )
      | ( r1_tarski @ ( k2_xboole_0 @ X23 @ X25 ) @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t9_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('37',plain,(
    ! [X13: $i] :
      ( r1_xboole_0 @ X13 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('38',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t72_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( ( k2_xboole_0 @ A @ B )
          = ( k2_xboole_0 @ C @ D ) )
        & ( r1_xboole_0 @ C @ A )
        & ( r1_xboole_0 @ D @ B ) )
     => ( C = B ) ) )).

thf('39',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X15 = X14 )
      | ~ ( r1_xboole_0 @ X15 @ X16 )
      | ( ( k2_xboole_0 @ X16 @ X14 )
       != ( k2_xboole_0 @ X15 @ X17 ) )
      | ~ ( r1_xboole_0 @ X17 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t72_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_xboole_0 @ X2 @ X1 )
       != X0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_xboole_0 @ X2 @ X1 )
        = X1 )
      | ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X2 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X13: $i] :
      ( r1_xboole_0 @ X13 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('44',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('45',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X12 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('47',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['43','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['42','49'])).

thf('51',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_xboole_0 @ X2 @ X1 )
        = X1 )
      | ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['41','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['37','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['36','52'])).

thf('54',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_2 ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['33','53'])).

thf('55',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('56',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( r1_tarski @ X41 @ X43 )
      | ( r1_tarski @ ( k1_tops_1 @ X42 @ X41 ) @ ( k1_tops_1 @ X42 @ X43 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( l1_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['55','60'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('62',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('63',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('64',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ X20 @ X21 )
      | ~ ( r1_tarski @ X22 @ X21 )
      | ( r1_tarski @ ( k2_xboole_0 @ X20 @ X22 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) )
      | ~ ( r1_tarski @ X0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C_2 ) ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['54','65'])).

thf('67',plain,(
    $false ),
    inference(demod,[status(thm)],['20','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.W9iN7pQvvg
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:20:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 44.43/44.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 44.43/44.65  % Solved by: fo/fo7.sh
% 44.43/44.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 44.43/44.65  % done 15942 iterations in 44.170s
% 44.43/44.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 44.43/44.65  % SZS output start Refutation
% 44.43/44.65  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 44.43/44.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 44.43/44.65  thf(sk_B_type, type, sk_B: $i).
% 44.43/44.65  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 44.43/44.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 44.43/44.65  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 44.43/44.65  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 44.43/44.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 44.43/44.65  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 44.43/44.65  thf(sk_C_2_type, type, sk_C_2: $i).
% 44.43/44.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 44.43/44.65  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 44.43/44.65  thf(sk_A_type, type, sk_A: $i).
% 44.43/44.65  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 44.43/44.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 44.43/44.65  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 44.43/44.65  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 44.43/44.65  thf(t49_tops_1, conjecture,
% 44.43/44.65    (![A:$i]:
% 44.43/44.65     ( ( l1_pre_topc @ A ) =>
% 44.43/44.65       ( ![B:$i]:
% 44.43/44.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 44.43/44.65           ( ![C:$i]:
% 44.43/44.65             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 44.43/44.65               ( r1_tarski @
% 44.43/44.65                 ( k4_subset_1 @
% 44.43/44.65                   ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ 
% 44.43/44.65                   ( k1_tops_1 @ A @ C ) ) @ 
% 44.43/44.65                 ( k1_tops_1 @
% 44.43/44.65                   A @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ) ))).
% 44.43/44.65  thf(zf_stmt_0, negated_conjecture,
% 44.43/44.65    (~( ![A:$i]:
% 44.43/44.65        ( ( l1_pre_topc @ A ) =>
% 44.43/44.65          ( ![B:$i]:
% 44.43/44.65            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 44.43/44.65              ( ![C:$i]:
% 44.43/44.65                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 44.43/44.65                  ( r1_tarski @
% 44.43/44.65                    ( k4_subset_1 @
% 44.43/44.65                      ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ 
% 44.43/44.65                      ( k1_tops_1 @ A @ C ) ) @ 
% 44.43/44.65                    ( k1_tops_1 @
% 44.43/44.65                      A @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ) ) )),
% 44.43/44.65    inference('cnf.neg', [status(esa)], [t49_tops_1])).
% 44.43/44.65  thf('0', plain,
% 44.43/44.65      (~ (r1_tarski @ 
% 44.43/44.65          (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 44.43/44.65           (k1_tops_1 @ sk_A @ sk_C_2)) @ 
% 44.43/44.65          (k1_tops_1 @ sk_A @ 
% 44.43/44.65           (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C_2)))),
% 44.43/44.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.43/44.65  thf('1', plain,
% 44.43/44.65      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 44.43/44.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.43/44.65  thf('2', plain,
% 44.43/44.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 44.43/44.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.43/44.65  thf(redefinition_k4_subset_1, axiom,
% 44.43/44.65    (![A:$i,B:$i,C:$i]:
% 44.43/44.65     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 44.43/44.65         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 44.43/44.65       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 44.43/44.65  thf('3', plain,
% 44.43/44.65      (![X29 : $i, X30 : $i, X31 : $i]:
% 44.43/44.65         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30))
% 44.43/44.65          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X30))
% 44.43/44.65          | ((k4_subset_1 @ X30 @ X29 @ X31) = (k2_xboole_0 @ X29 @ X31)))),
% 44.43/44.65      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 44.43/44.65  thf('4', plain,
% 44.43/44.65      (![X0 : $i]:
% 44.43/44.65         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 44.43/44.65            = (k2_xboole_0 @ sk_B @ X0))
% 44.43/44.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 44.43/44.65      inference('sup-', [status(thm)], ['2', '3'])).
% 44.43/44.65  thf('5', plain,
% 44.43/44.65      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C_2)
% 44.43/44.65         = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 44.43/44.65      inference('sup-', [status(thm)], ['1', '4'])).
% 44.43/44.65  thf('6', plain,
% 44.43/44.65      (~ (r1_tarski @ 
% 44.43/44.65          (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 44.43/44.65           (k1_tops_1 @ sk_A @ sk_C_2)) @ 
% 44.43/44.65          (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2)))),
% 44.43/44.65      inference('demod', [status(thm)], ['0', '5'])).
% 44.43/44.65  thf('7', plain,
% 44.43/44.65      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 44.43/44.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.43/44.65  thf(dt_k1_tops_1, axiom,
% 44.43/44.65    (![A:$i,B:$i]:
% 44.43/44.65     ( ( ( l1_pre_topc @ A ) & 
% 44.43/44.65         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 44.43/44.65       ( m1_subset_1 @
% 44.43/44.65         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 44.43/44.65  thf('8', plain,
% 44.43/44.65      (![X39 : $i, X40 : $i]:
% 44.43/44.65         (~ (l1_pre_topc @ X39)
% 44.43/44.65          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 44.43/44.65          | (m1_subset_1 @ (k1_tops_1 @ X39 @ X40) @ 
% 44.43/44.65             (k1_zfmisc_1 @ (u1_struct_0 @ X39))))),
% 44.43/44.65      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 44.43/44.65  thf('9', plain,
% 44.43/44.65      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C_2) @ 
% 44.43/44.65         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 44.43/44.65        | ~ (l1_pre_topc @ sk_A))),
% 44.43/44.65      inference('sup-', [status(thm)], ['7', '8'])).
% 44.43/44.65  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 44.43/44.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.43/44.65  thf('11', plain,
% 44.43/44.65      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C_2) @ 
% 44.43/44.65        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 44.43/44.65      inference('demod', [status(thm)], ['9', '10'])).
% 44.43/44.65  thf('12', plain,
% 44.43/44.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 44.43/44.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.43/44.65  thf('13', plain,
% 44.43/44.65      (![X39 : $i, X40 : $i]:
% 44.43/44.65         (~ (l1_pre_topc @ X39)
% 44.43/44.65          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 44.43/44.65          | (m1_subset_1 @ (k1_tops_1 @ X39 @ X40) @ 
% 44.43/44.65             (k1_zfmisc_1 @ (u1_struct_0 @ X39))))),
% 44.43/44.65      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 44.43/44.65  thf('14', plain,
% 44.43/44.65      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 44.43/44.65         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 44.43/44.65        | ~ (l1_pre_topc @ sk_A))),
% 44.43/44.65      inference('sup-', [status(thm)], ['12', '13'])).
% 44.43/44.65  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 44.43/44.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.43/44.65  thf('16', plain,
% 44.43/44.65      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 44.43/44.65        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 44.43/44.65      inference('demod', [status(thm)], ['14', '15'])).
% 44.43/44.65  thf('17', plain,
% 44.43/44.65      (![X29 : $i, X30 : $i, X31 : $i]:
% 44.43/44.65         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30))
% 44.43/44.65          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X30))
% 44.43/44.65          | ((k4_subset_1 @ X30 @ X29 @ X31) = (k2_xboole_0 @ X29 @ X31)))),
% 44.43/44.65      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 44.43/44.65  thf('18', plain,
% 44.43/44.65      (![X0 : $i]:
% 44.43/44.65         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 44.43/44.65            = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0))
% 44.43/44.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 44.43/44.65      inference('sup-', [status(thm)], ['16', '17'])).
% 44.43/44.65  thf('19', plain,
% 44.43/44.65      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 44.43/44.65         (k1_tops_1 @ sk_A @ sk_C_2))
% 44.43/44.65         = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 44.43/44.65            (k1_tops_1 @ sk_A @ sk_C_2)))),
% 44.43/44.65      inference('sup-', [status(thm)], ['11', '18'])).
% 44.43/44.65  thf('20', plain,
% 44.43/44.65      (~ (r1_tarski @ 
% 44.43/44.65          (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 44.43/44.65           (k1_tops_1 @ sk_A @ sk_C_2)) @ 
% 44.43/44.65          (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2)))),
% 44.43/44.65      inference('demod', [status(thm)], ['6', '19'])).
% 44.43/44.65  thf('21', plain,
% 44.43/44.65      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 44.43/44.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.43/44.65  thf('22', plain,
% 44.43/44.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 44.43/44.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.43/44.65  thf(dt_k4_subset_1, axiom,
% 44.43/44.65    (![A:$i,B:$i,C:$i]:
% 44.43/44.65     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 44.43/44.65         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 44.43/44.65       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 44.43/44.65  thf('23', plain,
% 44.43/44.65      (![X26 : $i, X27 : $i, X28 : $i]:
% 44.43/44.65         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27))
% 44.43/44.65          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27))
% 44.43/44.65          | (m1_subset_1 @ (k4_subset_1 @ X27 @ X26 @ X28) @ 
% 44.43/44.65             (k1_zfmisc_1 @ X27)))),
% 44.43/44.65      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 44.43/44.65  thf('24', plain,
% 44.43/44.65      (![X0 : $i]:
% 44.43/44.65         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 44.43/44.65           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 44.43/44.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 44.43/44.65      inference('sup-', [status(thm)], ['22', '23'])).
% 44.43/44.65  thf('25', plain,
% 44.43/44.65      ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C_2) @ 
% 44.43/44.65        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 44.43/44.65      inference('sup-', [status(thm)], ['21', '24'])).
% 44.43/44.65  thf('26', plain,
% 44.43/44.65      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C_2)
% 44.43/44.65         = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 44.43/44.65      inference('sup-', [status(thm)], ['1', '4'])).
% 44.43/44.65  thf('27', plain,
% 44.43/44.65      ((m1_subset_1 @ (k2_xboole_0 @ sk_B @ sk_C_2) @ 
% 44.43/44.65        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 44.43/44.65      inference('demod', [status(thm)], ['25', '26'])).
% 44.43/44.65  thf('28', plain,
% 44.43/44.65      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 44.43/44.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.43/44.65  thf(t48_tops_1, axiom,
% 44.43/44.65    (![A:$i]:
% 44.43/44.65     ( ( l1_pre_topc @ A ) =>
% 44.43/44.65       ( ![B:$i]:
% 44.43/44.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 44.43/44.65           ( ![C:$i]:
% 44.43/44.65             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 44.43/44.65               ( ( r1_tarski @ B @ C ) =>
% 44.43/44.65                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 44.43/44.65  thf('29', plain,
% 44.43/44.65      (![X41 : $i, X42 : $i, X43 : $i]:
% 44.43/44.65         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 44.43/44.65          | ~ (r1_tarski @ X41 @ X43)
% 44.43/44.65          | (r1_tarski @ (k1_tops_1 @ X42 @ X41) @ (k1_tops_1 @ X42 @ X43))
% 44.43/44.65          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 44.43/44.65          | ~ (l1_pre_topc @ X42))),
% 44.43/44.65      inference('cnf', [status(esa)], [t48_tops_1])).
% 44.43/44.65  thf('30', plain,
% 44.43/44.65      (![X0 : $i]:
% 44.43/44.65         (~ (l1_pre_topc @ sk_A)
% 44.43/44.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 44.43/44.65          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_2) @ (k1_tops_1 @ sk_A @ X0))
% 44.43/44.65          | ~ (r1_tarski @ sk_C_2 @ X0))),
% 44.43/44.65      inference('sup-', [status(thm)], ['28', '29'])).
% 44.43/44.65  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 44.43/44.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.43/44.65  thf('32', plain,
% 44.43/44.65      (![X0 : $i]:
% 44.43/44.65         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 44.43/44.65          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_2) @ (k1_tops_1 @ sk_A @ X0))
% 44.43/44.65          | ~ (r1_tarski @ sk_C_2 @ X0))),
% 44.43/44.65      inference('demod', [status(thm)], ['30', '31'])).
% 44.43/44.65  thf('33', plain,
% 44.43/44.65      ((~ (r1_tarski @ sk_C_2 @ (k2_xboole_0 @ sk_B @ sk_C_2))
% 44.43/44.65        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_2) @ 
% 44.43/44.65           (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))))),
% 44.43/44.65      inference('sup-', [status(thm)], ['27', '32'])).
% 44.43/44.65  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 44.43/44.65  thf('34', plain, (![X9 : $i]: (r1_tarski @ k1_xboole_0 @ X9)),
% 44.43/44.65      inference('cnf', [status(esa)], [t2_xboole_1])).
% 44.43/44.65  thf(t9_xboole_1, axiom,
% 44.43/44.65    (![A:$i,B:$i,C:$i]:
% 44.43/44.65     ( ( r1_tarski @ A @ B ) =>
% 44.43/44.65       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ C ) ) ))).
% 44.43/44.65  thf('35', plain,
% 44.43/44.65      (![X23 : $i, X24 : $i, X25 : $i]:
% 44.43/44.65         (~ (r1_tarski @ X23 @ X24)
% 44.43/44.65          | (r1_tarski @ (k2_xboole_0 @ X23 @ X25) @ (k2_xboole_0 @ X24 @ X25)))),
% 44.43/44.65      inference('cnf', [status(esa)], [t9_xboole_1])).
% 44.43/44.65  thf('36', plain,
% 44.43/44.65      (![X0 : $i, X1 : $i]:
% 44.43/44.65         (r1_tarski @ (k2_xboole_0 @ k1_xboole_0 @ X1) @ 
% 44.43/44.65          (k2_xboole_0 @ X0 @ X1))),
% 44.43/44.65      inference('sup-', [status(thm)], ['34', '35'])).
% 44.43/44.65  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 44.43/44.65  thf('37', plain, (![X13 : $i]: (r1_xboole_0 @ X13 @ k1_xboole_0)),
% 44.43/44.65      inference('cnf', [status(esa)], [t65_xboole_1])).
% 44.43/44.65  thf(t1_boole, axiom,
% 44.43/44.65    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 44.43/44.65  thf('38', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 44.43/44.65      inference('cnf', [status(esa)], [t1_boole])).
% 44.43/44.65  thf(t72_xboole_1, axiom,
% 44.43/44.65    (![A:$i,B:$i,C:$i,D:$i]:
% 44.43/44.65     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 44.43/44.65         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 44.43/44.65       ( ( C ) = ( B ) ) ))).
% 44.43/44.65  thf('39', plain,
% 44.43/44.65      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 44.43/44.65         (((X15) = (X14))
% 44.43/44.65          | ~ (r1_xboole_0 @ X15 @ X16)
% 44.43/44.65          | ((k2_xboole_0 @ X16 @ X14) != (k2_xboole_0 @ X15 @ X17))
% 44.43/44.65          | ~ (r1_xboole_0 @ X17 @ X14))),
% 44.43/44.65      inference('cnf', [status(esa)], [t72_xboole_1])).
% 44.43/44.65  thf('40', plain,
% 44.43/44.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 44.43/44.65         (((k2_xboole_0 @ X2 @ X1) != (X0))
% 44.43/44.65          | ~ (r1_xboole_0 @ k1_xboole_0 @ X1)
% 44.43/44.65          | ~ (r1_xboole_0 @ X0 @ X2)
% 44.43/44.65          | ((X0) = (X1)))),
% 44.43/44.65      inference('sup-', [status(thm)], ['38', '39'])).
% 44.43/44.65  thf('41', plain,
% 44.43/44.65      (![X1 : $i, X2 : $i]:
% 44.43/44.65         (((k2_xboole_0 @ X2 @ X1) = (X1))
% 44.43/44.65          | ~ (r1_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X2)
% 44.43/44.65          | ~ (r1_xboole_0 @ k1_xboole_0 @ X1))),
% 44.43/44.65      inference('simplify', [status(thm)], ['40'])).
% 44.43/44.65  thf('42', plain, (![X13 : $i]: (r1_xboole_0 @ X13 @ k1_xboole_0)),
% 44.43/44.65      inference('cnf', [status(esa)], [t65_xboole_1])).
% 44.43/44.65  thf(t3_xboole_0, axiom,
% 44.43/44.65    (![A:$i,B:$i]:
% 44.43/44.65     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 44.43/44.65            ( r1_xboole_0 @ A @ B ) ) ) & 
% 44.43/44.65       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 44.43/44.65            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 44.43/44.65  thf('43', plain,
% 44.43/44.65      (![X0 : $i, X1 : $i]:
% 44.43/44.65         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 44.43/44.65      inference('cnf', [status(esa)], [t3_xboole_0])).
% 44.43/44.65  thf(t48_xboole_1, axiom,
% 44.43/44.65    (![A:$i,B:$i]:
% 44.43/44.65     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 44.43/44.65  thf('44', plain,
% 44.43/44.65      (![X10 : $i, X11 : $i]:
% 44.43/44.65         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 44.43/44.65           = (k3_xboole_0 @ X10 @ X11))),
% 44.43/44.65      inference('cnf', [status(esa)], [t48_xboole_1])).
% 44.43/44.65  thf(t4_boole, axiom,
% 44.43/44.65    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 44.43/44.65  thf('45', plain,
% 44.43/44.65      (![X12 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X12) = (k1_xboole_0))),
% 44.43/44.65      inference('cnf', [status(esa)], [t4_boole])).
% 44.43/44.65  thf('46', plain,
% 44.43/44.65      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 44.43/44.65      inference('sup+', [status(thm)], ['44', '45'])).
% 44.43/44.65  thf(t4_xboole_0, axiom,
% 44.43/44.65    (![A:$i,B:$i]:
% 44.43/44.65     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 44.43/44.65            ( r1_xboole_0 @ A @ B ) ) ) & 
% 44.43/44.65       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 44.43/44.65            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 44.43/44.65  thf('47', plain,
% 44.43/44.65      (![X4 : $i, X6 : $i, X7 : $i]:
% 44.43/44.65         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 44.43/44.65          | ~ (r1_xboole_0 @ X4 @ X7))),
% 44.43/44.65      inference('cnf', [status(esa)], [t4_xboole_0])).
% 44.43/44.65  thf('48', plain,
% 44.43/44.65      (![X0 : $i, X1 : $i]:
% 44.43/44.65         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 44.43/44.65      inference('sup-', [status(thm)], ['46', '47'])).
% 44.43/44.65  thf('49', plain,
% 44.43/44.65      (![X0 : $i, X1 : $i]:
% 44.43/44.65         ((r1_xboole_0 @ k1_xboole_0 @ X0) | ~ (r1_xboole_0 @ k1_xboole_0 @ X1))),
% 44.43/44.65      inference('sup-', [status(thm)], ['43', '48'])).
% 44.43/44.65  thf('50', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 44.43/44.65      inference('sup-', [status(thm)], ['42', '49'])).
% 44.43/44.65  thf('51', plain,
% 44.43/44.65      (![X1 : $i, X2 : $i]:
% 44.43/44.65         (((k2_xboole_0 @ X2 @ X1) = (X1))
% 44.43/44.65          | ~ (r1_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X2))),
% 44.43/44.65      inference('demod', [status(thm)], ['41', '50'])).
% 44.43/44.65  thf('52', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 44.43/44.65      inference('sup-', [status(thm)], ['37', '51'])).
% 44.43/44.65  thf('53', plain,
% 44.43/44.65      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ X1))),
% 44.43/44.65      inference('demod', [status(thm)], ['36', '52'])).
% 44.43/44.65  thf('54', plain,
% 44.43/44.65      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_2) @ 
% 44.43/44.65        (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2)))),
% 44.43/44.65      inference('demod', [status(thm)], ['33', '53'])).
% 44.43/44.65  thf('55', plain,
% 44.43/44.65      ((m1_subset_1 @ (k2_xboole_0 @ sk_B @ sk_C_2) @ 
% 44.43/44.65        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 44.43/44.65      inference('demod', [status(thm)], ['25', '26'])).
% 44.43/44.65  thf('56', plain,
% 44.43/44.65      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 44.43/44.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.43/44.65  thf('57', plain,
% 44.43/44.65      (![X41 : $i, X42 : $i, X43 : $i]:
% 44.43/44.65         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 44.43/44.65          | ~ (r1_tarski @ X41 @ X43)
% 44.43/44.65          | (r1_tarski @ (k1_tops_1 @ X42 @ X41) @ (k1_tops_1 @ X42 @ X43))
% 44.43/44.65          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 44.43/44.65          | ~ (l1_pre_topc @ X42))),
% 44.43/44.65      inference('cnf', [status(esa)], [t48_tops_1])).
% 44.43/44.65  thf('58', plain,
% 44.43/44.65      (![X0 : $i]:
% 44.43/44.65         (~ (l1_pre_topc @ sk_A)
% 44.43/44.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 44.43/44.65          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 44.43/44.65          | ~ (r1_tarski @ sk_B @ X0))),
% 44.43/44.65      inference('sup-', [status(thm)], ['56', '57'])).
% 44.43/44.65  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 44.43/44.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 44.43/44.65  thf('60', plain,
% 44.43/44.65      (![X0 : $i]:
% 44.43/44.65         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 44.43/44.65          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 44.43/44.65          | ~ (r1_tarski @ sk_B @ X0))),
% 44.43/44.65      inference('demod', [status(thm)], ['58', '59'])).
% 44.43/44.65  thf('61', plain,
% 44.43/44.65      ((~ (r1_tarski @ sk_B @ (k2_xboole_0 @ sk_B @ sk_C_2))
% 44.43/44.65        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 44.43/44.65           (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))))),
% 44.43/44.65      inference('sup-', [status(thm)], ['55', '60'])).
% 44.43/44.65  thf(t7_xboole_1, axiom,
% 44.43/44.65    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 44.43/44.65  thf('62', plain,
% 44.43/44.65      (![X18 : $i, X19 : $i]: (r1_tarski @ X18 @ (k2_xboole_0 @ X18 @ X19))),
% 44.43/44.65      inference('cnf', [status(esa)], [t7_xboole_1])).
% 44.43/44.65  thf('63', plain,
% 44.43/44.65      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 44.43/44.65        (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2)))),
% 44.43/44.65      inference('demod', [status(thm)], ['61', '62'])).
% 44.43/44.65  thf(t8_xboole_1, axiom,
% 44.43/44.65    (![A:$i,B:$i,C:$i]:
% 44.43/44.65     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 44.43/44.65       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 44.43/44.65  thf('64', plain,
% 44.43/44.65      (![X20 : $i, X21 : $i, X22 : $i]:
% 44.43/44.65         (~ (r1_tarski @ X20 @ X21)
% 44.43/44.65          | ~ (r1_tarski @ X22 @ X21)
% 44.43/44.65          | (r1_tarski @ (k2_xboole_0 @ X20 @ X22) @ X21))),
% 44.43/44.65      inference('cnf', [status(esa)], [t8_xboole_1])).
% 44.43/44.65  thf('65', plain,
% 44.43/44.65      (![X0 : $i]:
% 44.43/44.65         ((r1_tarski @ (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0) @ 
% 44.43/44.65           (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2)))
% 44.43/44.65          | ~ (r1_tarski @ X0 @ 
% 44.43/44.65               (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2))))),
% 44.43/44.65      inference('sup-', [status(thm)], ['63', '64'])).
% 44.43/44.65  thf('66', plain,
% 44.43/44.65      ((r1_tarski @ 
% 44.43/44.65        (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C_2)) @ 
% 44.43/44.65        (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C_2)))),
% 44.43/44.65      inference('sup-', [status(thm)], ['54', '65'])).
% 44.43/44.65  thf('67', plain, ($false), inference('demod', [status(thm)], ['20', '66'])).
% 44.43/44.65  
% 44.43/44.65  % SZS output end Refutation
% 44.43/44.65  
% 44.43/44.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
