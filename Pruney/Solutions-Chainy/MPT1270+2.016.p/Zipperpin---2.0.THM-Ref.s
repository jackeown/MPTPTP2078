%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AeoCU9TzhR

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:27 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 147 expanded)
%              Number of leaves         :   34 (  54 expanded)
%              Depth                    :   12
%              Number of atoms          :  736 (1353 expanded)
%              Number of equality atoms :   26 (  27 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

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
    ( ~ ( r1_tarski @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
    | ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v2_tops_1 @ sk_B_1 @ sk_A )
   <= ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t84_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( ( k1_tops_1 @ A @ B )
              = k1_xboole_0 ) ) ) ) )).

thf('5',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( v2_tops_1 @ X30 @ X31 )
      | ( ( k1_tops_1 @ X31 @ X30 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('11',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( ( k2_tops_1 @ X25 @ X24 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X25 ) @ ( k2_pre_topc @ X25 @ X24 ) @ ( k1_tops_1 @ X25 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('15',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X20 @ X21 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('16',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('19',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( ( k7_subset_1 @ X9 @ X8 @ X10 )
        = ( k4_xboole_0 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['12','13','20'])).

thf('22',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ k1_xboole_0 ) )
   <= ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['9','21'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('23',plain,(
    ! [X3: $i] :
      ( ( k4_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('24',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B_1 )
      = ( k2_pre_topc @ sk_A @ sk_B_1 ) )
   <= ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('26',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( r1_tarski @ X22 @ ( k2_pre_topc @ X23 @ X22 ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('27',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    r1_tarski @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['24','29'])).

thf('31',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
    | ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('34',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( r1_tarski @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('35',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('36',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X27 @ X26 ) @ X26 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('37',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['37','38'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ X0 )
      | ~ ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( r1_tarski @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['34','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t73_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_xboole_0 @ ( k1_tops_1 @ A @ B ) @ ( k2_tops_1 @ A @ B ) ) ) ) )).

thf('44',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( r1_xboole_0 @ ( k1_tops_1 @ X29 @ X28 ) @ ( k2_tops_1 @ X29 @ X28 ) )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t73_tops_1])).

thf('45',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('48',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('49',plain,
    ( ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
   <= ( r1_tarski @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['42','49'])).

thf(t6_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i,G: $i] :
                  ( ( ( r2_hidden @ C @ D )
                    & ( r2_hidden @ D @ E )
                    & ( r2_hidden @ E @ F )
                    & ( r2_hidden @ F @ G )
                    & ( r2_hidden @ G @ B ) )
                 => ( r1_xboole_0 @ C @ A ) ) ) ) )).

thf('51',plain,(
    ! [X14: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('52',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X7 ) @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('53',plain,(
    ! [X6: $i] :
      ( ( k2_subset_1 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('54',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('55',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ( r1_tarski @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['50','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( ( k1_tops_1 @ X31 @ X30 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X30 @ X31 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('61',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B_1 @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v2_tops_1 @ sk_B_1 @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_tops_1 @ sk_B_1 @ sk_A ) )
   <= ( r1_tarski @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['58','63'])).

thf('65',plain,
    ( ( v2_tops_1 @ sk_B_1 @ sk_A )
   <= ( r1_tarski @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ~ ( v2_tops_1 @ sk_B_1 @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('67',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k2_tops_1 @ sk_A @ sk_B_1 ) )
    | ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','32','33','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AeoCU9TzhR
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:47:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.46/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.65  % Solved by: fo/fo7.sh
% 0.46/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.65  % done 171 iterations in 0.163s
% 0.46/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.65  % SZS output start Refutation
% 0.46/0.65  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.65  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.46/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.65  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.46/0.65  thf(sk_B_type, type, sk_B: $i > $i).
% 0.46/0.65  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.46/0.65  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.46/0.65  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.46/0.65  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.65  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.46/0.65  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.65  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.46/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.65  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.46/0.65  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.46/0.65  thf(t88_tops_1, conjecture,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( l1_pre_topc @ A ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.65           ( ( v2_tops_1 @ B @ A ) <=>
% 0.46/0.65             ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.46/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.65    (~( ![A:$i]:
% 0.46/0.65        ( ( l1_pre_topc @ A ) =>
% 0.46/0.65          ( ![B:$i]:
% 0.46/0.65            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.65              ( ( v2_tops_1 @ B @ A ) <=>
% 0.46/0.65                ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ) )),
% 0.46/0.65    inference('cnf.neg', [status(esa)], [t88_tops_1])).
% 0.46/0.65  thf('0', plain,
% 0.46/0.65      ((~ (r1_tarski @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1))
% 0.46/0.65        | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('1', plain,
% 0.46/0.65      (~ ((r1_tarski @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1))) | 
% 0.46/0.65       ~ ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.46/0.65      inference('split', [status(esa)], ['0'])).
% 0.46/0.65  thf('2', plain,
% 0.46/0.65      (((r1_tarski @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1))
% 0.46/0.65        | (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('3', plain,
% 0.46/0.65      (((v2_tops_1 @ sk_B_1 @ sk_A)) <= (((v2_tops_1 @ sk_B_1 @ sk_A)))),
% 0.46/0.65      inference('split', [status(esa)], ['2'])).
% 0.46/0.65  thf('4', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(t84_tops_1, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( l1_pre_topc @ A ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.65           ( ( v2_tops_1 @ B @ A ) <=>
% 0.46/0.65             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.46/0.65  thf('5', plain,
% 0.46/0.65      (![X30 : $i, X31 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.46/0.65          | ~ (v2_tops_1 @ X30 @ X31)
% 0.46/0.65          | ((k1_tops_1 @ X31 @ X30) = (k1_xboole_0))
% 0.46/0.65          | ~ (l1_pre_topc @ X31))),
% 0.46/0.65      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.46/0.65  thf('6', plain,
% 0.46/0.65      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.65        | ((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.46/0.65        | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['4', '5'])).
% 0.46/0.65  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('8', plain,
% 0.46/0.65      ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.46/0.65        | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['6', '7'])).
% 0.46/0.65  thf('9', plain,
% 0.46/0.65      ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 0.46/0.65         <= (((v2_tops_1 @ sk_B_1 @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['3', '8'])).
% 0.46/0.65  thf('10', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(l78_tops_1, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( l1_pre_topc @ A ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.65           ( ( k2_tops_1 @ A @ B ) =
% 0.46/0.65             ( k7_subset_1 @
% 0.46/0.65               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.46/0.65               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.46/0.65  thf('11', plain,
% 0.46/0.65      (![X24 : $i, X25 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.46/0.65          | ((k2_tops_1 @ X25 @ X24)
% 0.46/0.65              = (k7_subset_1 @ (u1_struct_0 @ X25) @ 
% 0.46/0.65                 (k2_pre_topc @ X25 @ X24) @ (k1_tops_1 @ X25 @ X24)))
% 0.46/0.65          | ~ (l1_pre_topc @ X25))),
% 0.46/0.65      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.46/0.65  thf('12', plain,
% 0.46/0.65      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.65        | ((k2_tops_1 @ sk_A @ sk_B_1)
% 0.46/0.65            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.65               (k2_pre_topc @ sk_A @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_B_1))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['10', '11'])).
% 0.46/0.65  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('14', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(dt_k2_pre_topc, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( l1_pre_topc @ A ) & 
% 0.46/0.65         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.65       ( m1_subset_1 @
% 0.46/0.65         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.46/0.65  thf('15', plain,
% 0.46/0.65      (![X20 : $i, X21 : $i]:
% 0.46/0.65         (~ (l1_pre_topc @ X20)
% 0.46/0.65          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.46/0.65          | (m1_subset_1 @ (k2_pre_topc @ X20 @ X21) @ 
% 0.46/0.65             (k1_zfmisc_1 @ (u1_struct_0 @ X20))))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.46/0.65  thf('16', plain,
% 0.46/0.65      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 0.46/0.65         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.65        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['14', '15'])).
% 0.46/0.65  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('18', plain,
% 0.46/0.65      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 0.46/0.65        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('demod', [status(thm)], ['16', '17'])).
% 0.46/0.65  thf(redefinition_k7_subset_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.65       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.46/0.65  thf('19', plain,
% 0.46/0.65      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.46/0.65          | ((k7_subset_1 @ X9 @ X8 @ X10) = (k4_xboole_0 @ X8 @ X10)))),
% 0.46/0.65      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.46/0.65  thf('20', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.65           (k2_pre_topc @ sk_A @ sk_B_1) @ X0)
% 0.46/0.65           = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['18', '19'])).
% 0.46/0.65  thf('21', plain,
% 0.46/0.65      (((k2_tops_1 @ sk_A @ sk_B_1)
% 0.46/0.65         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 0.46/0.65            (k1_tops_1 @ sk_A @ sk_B_1)))),
% 0.46/0.65      inference('demod', [status(thm)], ['12', '13', '20'])).
% 0.46/0.65  thf('22', plain,
% 0.46/0.65      ((((k2_tops_1 @ sk_A @ sk_B_1)
% 0.46/0.65          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B_1) @ k1_xboole_0)))
% 0.46/0.65         <= (((v2_tops_1 @ sk_B_1 @ sk_A)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['9', '21'])).
% 0.46/0.65  thf(t3_boole, axiom,
% 0.46/0.65    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.46/0.65  thf('23', plain, (![X3 : $i]: ((k4_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 0.46/0.65      inference('cnf', [status(esa)], [t3_boole])).
% 0.46/0.65  thf('24', plain,
% 0.46/0.65      ((((k2_tops_1 @ sk_A @ sk_B_1) = (k2_pre_topc @ sk_A @ sk_B_1)))
% 0.46/0.65         <= (((v2_tops_1 @ sk_B_1 @ sk_A)))),
% 0.46/0.65      inference('demod', [status(thm)], ['22', '23'])).
% 0.46/0.65  thf('25', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(t48_pre_topc, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( l1_pre_topc @ A ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.65           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.46/0.65  thf('26', plain,
% 0.46/0.65      (![X22 : $i, X23 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.46/0.65          | (r1_tarski @ X22 @ (k2_pre_topc @ X23 @ X22))
% 0.46/0.65          | ~ (l1_pre_topc @ X23))),
% 0.46/0.65      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.46/0.65  thf('27', plain,
% 0.46/0.65      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.65        | (r1_tarski @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['25', '26'])).
% 0.46/0.65  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('29', plain, ((r1_tarski @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1))),
% 0.46/0.65      inference('demod', [status(thm)], ['27', '28'])).
% 0.46/0.65  thf('30', plain,
% 0.46/0.65      (((r1_tarski @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))
% 0.46/0.65         <= (((v2_tops_1 @ sk_B_1 @ sk_A)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['24', '29'])).
% 0.46/0.65  thf('31', plain,
% 0.46/0.65      ((~ (r1_tarski @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))
% 0.46/0.65         <= (~ ((r1_tarski @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1))))),
% 0.46/0.65      inference('split', [status(esa)], ['0'])).
% 0.46/0.65  thf('32', plain,
% 0.46/0.65      (((r1_tarski @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1))) | 
% 0.46/0.65       ~ ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['30', '31'])).
% 0.46/0.65  thf('33', plain,
% 0.46/0.65      (((r1_tarski @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1))) | 
% 0.46/0.65       ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.46/0.65      inference('split', [status(esa)], ['2'])).
% 0.46/0.65  thf('34', plain,
% 0.46/0.65      (((r1_tarski @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1)))
% 0.46/0.65         <= (((r1_tarski @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1))))),
% 0.46/0.65      inference('split', [status(esa)], ['2'])).
% 0.46/0.65  thf('35', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(t44_tops_1, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( l1_pre_topc @ A ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.65           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.46/0.65  thf('36', plain,
% 0.46/0.65      (![X26 : $i, X27 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.46/0.65          | (r1_tarski @ (k1_tops_1 @ X27 @ X26) @ X26)
% 0.46/0.65          | ~ (l1_pre_topc @ X27))),
% 0.46/0.65      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.46/0.65  thf('37', plain,
% 0.46/0.65      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.65        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1))),
% 0.46/0.65      inference('sup-', [status(thm)], ['35', '36'])).
% 0.46/0.65  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('39', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1)),
% 0.46/0.65      inference('demod', [status(thm)], ['37', '38'])).
% 0.46/0.65  thf(t1_xboole_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.46/0.65       ( r1_tarski @ A @ C ) ))).
% 0.46/0.65  thf('40', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.65         (~ (r1_tarski @ X0 @ X1)
% 0.46/0.65          | ~ (r1_tarski @ X1 @ X2)
% 0.46/0.65          | (r1_tarski @ X0 @ X2))),
% 0.46/0.65      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.46/0.65  thf('41', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ X0)
% 0.46/0.65          | ~ (r1_tarski @ sk_B_1 @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['39', '40'])).
% 0.46/0.65  thf('42', plain,
% 0.46/0.65      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ (k2_tops_1 @ sk_A @ sk_B_1)))
% 0.46/0.65         <= (((r1_tarski @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['34', '41'])).
% 0.46/0.65  thf('43', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(t73_tops_1, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( l1_pre_topc @ A ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.65           ( r1_xboole_0 @ ( k1_tops_1 @ A @ B ) @ ( k2_tops_1 @ A @ B ) ) ) ) ))).
% 0.46/0.65  thf('44', plain,
% 0.46/0.65      (![X28 : $i, X29 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.46/0.65          | (r1_xboole_0 @ (k1_tops_1 @ X29 @ X28) @ (k2_tops_1 @ X29 @ X28))
% 0.46/0.65          | ~ (l1_pre_topc @ X29))),
% 0.46/0.65      inference('cnf', [status(esa)], [t73_tops_1])).
% 0.46/0.65  thf('45', plain,
% 0.46/0.65      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.65        | (r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B_1) @ 
% 0.46/0.65           (k2_tops_1 @ sk_A @ sk_B_1)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['43', '44'])).
% 0.46/0.65  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('47', plain,
% 0.46/0.65      ((r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B_1) @ (k2_tops_1 @ sk_A @ sk_B_1))),
% 0.46/0.65      inference('demod', [status(thm)], ['45', '46'])).
% 0.46/0.65  thf(t69_xboole_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.46/0.65       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.46/0.65  thf('48', plain,
% 0.46/0.65      (![X4 : $i, X5 : $i]:
% 0.46/0.65         (~ (r1_xboole_0 @ X4 @ X5)
% 0.46/0.65          | ~ (r1_tarski @ X4 @ X5)
% 0.46/0.65          | (v1_xboole_0 @ X4))),
% 0.46/0.65      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.46/0.65  thf('49', plain,
% 0.46/0.65      (((v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 0.46/0.65        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ 
% 0.46/0.65             (k2_tops_1 @ sk_A @ sk_B_1)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['47', '48'])).
% 0.46/0.65  thf('50', plain,
% 0.46/0.65      (((v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B_1)))
% 0.46/0.65         <= (((r1_tarski @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['42', '49'])).
% 0.46/0.65  thf(t6_mcart_1, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.46/0.65          ( ![B:$i]:
% 0.46/0.65            ( ~( ( r2_hidden @ B @ A ) & 
% 0.46/0.65                 ( ![C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.46/0.65                   ( ( ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ E ) & 
% 0.46/0.65                       ( r2_hidden @ E @ F ) & ( r2_hidden @ F @ G ) & 
% 0.46/0.65                       ( r2_hidden @ G @ B ) ) =>
% 0.46/0.65                     ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 0.46/0.65  thf('51', plain,
% 0.46/0.65      (![X14 : $i]:
% 0.46/0.65         (((X14) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X14) @ X14))),
% 0.46/0.65      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.46/0.65  thf(dt_k2_subset_1, axiom,
% 0.46/0.65    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.46/0.65  thf('52', plain,
% 0.46/0.65      (![X7 : $i]: (m1_subset_1 @ (k2_subset_1 @ X7) @ (k1_zfmisc_1 @ X7))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.46/0.65  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.46/0.65  thf('53', plain, (![X6 : $i]: ((k2_subset_1 @ X6) = (X6))),
% 0.46/0.65      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.46/0.65  thf('54', plain, (![X7 : $i]: (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X7))),
% 0.46/0.65      inference('demod', [status(thm)], ['52', '53'])).
% 0.46/0.65  thf(t5_subset, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.46/0.65          ( v1_xboole_0 @ C ) ) ))).
% 0.46/0.65  thf('55', plain,
% 0.46/0.65      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X11 @ X12)
% 0.46/0.65          | ~ (v1_xboole_0 @ X13)
% 0.46/0.65          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t5_subset])).
% 0.46/0.65  thf('56', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['54', '55'])).
% 0.46/0.65  thf('57', plain,
% 0.46/0.65      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['51', '56'])).
% 0.46/0.65  thf('58', plain,
% 0.46/0.65      ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 0.46/0.65         <= (((r1_tarski @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['50', '57'])).
% 0.46/0.65  thf('59', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('60', plain,
% 0.46/0.65      (![X30 : $i, X31 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.46/0.65          | ((k1_tops_1 @ X31 @ X30) != (k1_xboole_0))
% 0.46/0.65          | (v2_tops_1 @ X30 @ X31)
% 0.46/0.65          | ~ (l1_pre_topc @ X31))),
% 0.46/0.66      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.46/0.66  thf('61', plain,
% 0.46/0.66      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.66        | (v2_tops_1 @ sk_B_1 @ sk_A)
% 0.46/0.66        | ((k1_tops_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['59', '60'])).
% 0.46/0.66  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('63', plain,
% 0.46/0.66      (((v2_tops_1 @ sk_B_1 @ sk_A)
% 0.46/0.66        | ((k1_tops_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 0.46/0.66      inference('demod', [status(thm)], ['61', '62'])).
% 0.46/0.66  thf('64', plain,
% 0.46/0.66      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B_1 @ sk_A)))
% 0.46/0.66         <= (((r1_tarski @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['58', '63'])).
% 0.46/0.66  thf('65', plain,
% 0.46/0.66      (((v2_tops_1 @ sk_B_1 @ sk_A))
% 0.46/0.66         <= (((r1_tarski @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1))))),
% 0.46/0.66      inference('simplify', [status(thm)], ['64'])).
% 0.46/0.66  thf('66', plain,
% 0.46/0.66      ((~ (v2_tops_1 @ sk_B_1 @ sk_A)) <= (~ ((v2_tops_1 @ sk_B_1 @ sk_A)))),
% 0.46/0.66      inference('split', [status(esa)], ['0'])).
% 0.46/0.66  thf('67', plain,
% 0.46/0.66      (~ ((r1_tarski @ sk_B_1 @ (k2_tops_1 @ sk_A @ sk_B_1))) | 
% 0.46/0.66       ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['65', '66'])).
% 0.46/0.66  thf('68', plain, ($false),
% 0.46/0.66      inference('sat_resolution*', [status(thm)], ['1', '32', '33', '67'])).
% 0.46/0.66  
% 0.46/0.66  % SZS output end Refutation
% 0.46/0.66  
% 0.46/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
