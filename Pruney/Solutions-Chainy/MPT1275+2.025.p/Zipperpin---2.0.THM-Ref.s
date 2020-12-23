%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.73fq18X9fQ

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:36 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 176 expanded)
%              Number of leaves         :   29 (  61 expanded)
%              Depth                    :   13
%              Number of atoms          :  746 (1862 expanded)
%              Number of equality atoms :   39 ( 100 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(t94_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( ( v3_tops_1 @ B @ A )
            <=> ( B
                = ( k2_tops_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
             => ( ( v3_tops_1 @ B @ A )
              <=> ( B
                  = ( k2_tops_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t94_tops_1])).

thf('0',plain,
    ( ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) )
    | ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t92_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
           => ( v2_tops_1 @ B @ A ) ) ) ) )).

thf('5',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( v2_tops_1 @ X26 @ X27 )
      | ~ ( v3_tops_1 @ X26 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t92_tops_1])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tops_1 @ sk_B @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ~ ( v3_tops_1 @ sk_B @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t88_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('11',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( v2_tops_1 @ X24 @ X25 )
      | ( r1_tarski @ X24 @ ( k2_tops_1 @ X25 @ X24 ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t88_tops_1])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('17',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X23 @ X22 ) @ X22 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('18',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['18','19'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('21',plain,(
    ! [X13: $i,X15: $i] :
      ( ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('22',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('23',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X8 @ X9 ) @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('24',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_B ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('28',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_subset_1 @ X6 @ X7 )
        = ( k4_xboole_0 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('29',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('31',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( ( k2_tops_1 @ X21 @ X20 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X21 ) @ ( k2_pre_topc @ X21 @ X20 ) @ ( k1_tops_1 @ X21 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('32',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
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

thf('35',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v4_pre_topc @ X16 @ X17 )
      | ( ( k2_pre_topc @ X17 @ X16 )
        = X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('36',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('41',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( ( k7_subset_1 @ X11 @ X10 @ X12 )
        = ( k4_xboole_0 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','33','39','42'])).

thf('44',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['29','43'])).

thf('45',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['26','44'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('46',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('47',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['15','47'])).

thf('49',plain,
    ( ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('50',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B
       != ( k2_tops_1 @ sk_A @ sk_B ) )
      & ( v3_tops_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) )
    | ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('53',plain,
    ( ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('54',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( r1_tarski @ X24 @ ( k2_tops_1 @ X25 @ X24 ) )
      | ( v2_tops_1 @ X24 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t88_tops_1])).

thf('56',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ~ ( r1_tarski @ sk_B @ sk_B )
      | ( v2_tops_1 @ sk_B @ sk_A ) )
   <= ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('61',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['59','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
          <=> ( v2_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) )).

thf('64',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v2_tops_1 @ ( k2_pre_topc @ X19 @ X18 ) @ X19 )
      | ( v3_tops_1 @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_1])).

thf('65',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tops_1 @ sk_B @ sk_A )
    | ~ ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('68',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
   <= ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['62','68'])).

thf('70',plain,
    ( ~ ( v3_tops_1 @ sk_B @ sk_A )
   <= ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('71',plain,
    ( ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) )
    | ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','51','52','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.73fq18X9fQ
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:47:36 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.37/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.61  % Solved by: fo/fo7.sh
% 0.37/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.61  % done 211 iterations in 0.143s
% 0.37/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.61  % SZS output start Refutation
% 0.37/0.61  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.37/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.61  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.37/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.61  thf(v3_tops_1_type, type, v3_tops_1: $i > $i > $o).
% 0.37/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.61  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.37/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.61  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.37/0.61  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.37/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.61  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.37/0.61  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.37/0.61  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.37/0.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.61  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.37/0.61  thf(t94_tops_1, conjecture,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( l1_pre_topc @ A ) =>
% 0.37/0.61       ( ![B:$i]:
% 0.37/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.61           ( ( v4_pre_topc @ B @ A ) =>
% 0.37/0.61             ( ( v3_tops_1 @ B @ A ) <=> ( ( B ) = ( k2_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.37/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.61    (~( ![A:$i]:
% 0.37/0.61        ( ( l1_pre_topc @ A ) =>
% 0.37/0.61          ( ![B:$i]:
% 0.37/0.61            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.61              ( ( v4_pre_topc @ B @ A ) =>
% 0.37/0.61                ( ( v3_tops_1 @ B @ A ) <=> ( ( B ) = ( k2_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.37/0.61    inference('cnf.neg', [status(esa)], [t94_tops_1])).
% 0.37/0.61  thf('0', plain,
% 0.37/0.61      ((((sk_B) != (k2_tops_1 @ sk_A @ sk_B)) | ~ (v3_tops_1 @ sk_B @ sk_A))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('1', plain,
% 0.37/0.61      (~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B))) | ~ ((v3_tops_1 @ sk_B @ sk_A))),
% 0.37/0.61      inference('split', [status(esa)], ['0'])).
% 0.37/0.61  thf('2', plain,
% 0.37/0.61      ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B)) | (v3_tops_1 @ sk_B @ sk_A))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('3', plain,
% 0.37/0.61      (((v3_tops_1 @ sk_B @ sk_A)) <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 0.37/0.61      inference('split', [status(esa)], ['2'])).
% 0.37/0.61  thf('4', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(t92_tops_1, axiom,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( l1_pre_topc @ A ) =>
% 0.37/0.61       ( ![B:$i]:
% 0.37/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.61           ( ( v3_tops_1 @ B @ A ) => ( v2_tops_1 @ B @ A ) ) ) ) ))).
% 0.37/0.61  thf('5', plain,
% 0.37/0.61      (![X26 : $i, X27 : $i]:
% 0.37/0.61         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.37/0.61          | (v2_tops_1 @ X26 @ X27)
% 0.37/0.61          | ~ (v3_tops_1 @ X26 @ X27)
% 0.37/0.61          | ~ (l1_pre_topc @ X27))),
% 0.37/0.61      inference('cnf', [status(esa)], [t92_tops_1])).
% 0.37/0.61  thf('6', plain,
% 0.37/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.61        | ~ (v3_tops_1 @ sk_B @ sk_A)
% 0.37/0.61        | (v2_tops_1 @ sk_B @ sk_A))),
% 0.37/0.61      inference('sup-', [status(thm)], ['4', '5'])).
% 0.37/0.61  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('8', plain, ((~ (v3_tops_1 @ sk_B @ sk_A) | (v2_tops_1 @ sk_B @ sk_A))),
% 0.37/0.61      inference('demod', [status(thm)], ['6', '7'])).
% 0.37/0.61  thf('9', plain,
% 0.37/0.61      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['3', '8'])).
% 0.37/0.61  thf('10', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(t88_tops_1, axiom,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( l1_pre_topc @ A ) =>
% 0.37/0.61       ( ![B:$i]:
% 0.37/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.61           ( ( v2_tops_1 @ B @ A ) <=>
% 0.37/0.61             ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.37/0.61  thf('11', plain,
% 0.37/0.61      (![X24 : $i, X25 : $i]:
% 0.37/0.61         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.37/0.61          | ~ (v2_tops_1 @ X24 @ X25)
% 0.37/0.61          | (r1_tarski @ X24 @ (k2_tops_1 @ X25 @ X24))
% 0.37/0.61          | ~ (l1_pre_topc @ X25))),
% 0.37/0.61      inference('cnf', [status(esa)], [t88_tops_1])).
% 0.37/0.61  thf('12', plain,
% 0.37/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.61        | (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.37/0.61        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.37/0.61      inference('sup-', [status(thm)], ['10', '11'])).
% 0.37/0.61  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('14', plain,
% 0.37/0.61      (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.37/0.61        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.37/0.61      inference('demod', [status(thm)], ['12', '13'])).
% 0.37/0.61  thf('15', plain,
% 0.37/0.61      (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.37/0.61         <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['9', '14'])).
% 0.37/0.61  thf('16', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(t44_tops_1, axiom,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( l1_pre_topc @ A ) =>
% 0.37/0.61       ( ![B:$i]:
% 0.37/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.61           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.37/0.61  thf('17', plain,
% 0.37/0.61      (![X22 : $i, X23 : $i]:
% 0.37/0.61         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.37/0.61          | (r1_tarski @ (k1_tops_1 @ X23 @ X22) @ X22)
% 0.37/0.61          | ~ (l1_pre_topc @ X23))),
% 0.37/0.61      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.37/0.61  thf('18', plain,
% 0.37/0.61      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.37/0.61      inference('sup-', [status(thm)], ['16', '17'])).
% 0.37/0.61  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('20', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.37/0.61      inference('demod', [status(thm)], ['18', '19'])).
% 0.37/0.61  thf(t3_subset, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.37/0.61  thf('21', plain,
% 0.37/0.61      (![X13 : $i, X15 : $i]:
% 0.37/0.61         ((m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X13 @ X15))),
% 0.37/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.61  thf('22', plain,
% 0.37/0.61      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 0.37/0.61      inference('sup-', [status(thm)], ['20', '21'])).
% 0.37/0.61  thf(dt_k3_subset_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.61       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.37/0.61  thf('23', plain,
% 0.37/0.61      (![X8 : $i, X9 : $i]:
% 0.37/0.61         ((m1_subset_1 @ (k3_subset_1 @ X8 @ X9) @ (k1_zfmisc_1 @ X8))
% 0.37/0.61          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.37/0.61      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.37/0.61  thf('24', plain,
% 0.37/0.61      ((m1_subset_1 @ (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.37/0.61        (k1_zfmisc_1 @ sk_B))),
% 0.37/0.61      inference('sup-', [status(thm)], ['22', '23'])).
% 0.37/0.61  thf('25', plain,
% 0.37/0.61      (![X13 : $i, X14 : $i]:
% 0.37/0.61         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.37/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.61  thf('26', plain,
% 0.37/0.61      ((r1_tarski @ (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_B)),
% 0.37/0.61      inference('sup-', [status(thm)], ['24', '25'])).
% 0.37/0.61  thf('27', plain,
% 0.37/0.61      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 0.37/0.61      inference('sup-', [status(thm)], ['20', '21'])).
% 0.37/0.61  thf(d5_subset_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.61       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.37/0.61  thf('28', plain,
% 0.37/0.61      (![X6 : $i, X7 : $i]:
% 0.37/0.61         (((k3_subset_1 @ X6 @ X7) = (k4_xboole_0 @ X6 @ X7))
% 0.37/0.61          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.37/0.61      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.37/0.61  thf('29', plain,
% 0.37/0.61      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.37/0.61         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['27', '28'])).
% 0.37/0.61  thf('30', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(l78_tops_1, axiom,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( l1_pre_topc @ A ) =>
% 0.37/0.61       ( ![B:$i]:
% 0.37/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.61           ( ( k2_tops_1 @ A @ B ) =
% 0.37/0.61             ( k7_subset_1 @
% 0.37/0.61               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.37/0.61               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.37/0.61  thf('31', plain,
% 0.37/0.61      (![X20 : $i, X21 : $i]:
% 0.37/0.61         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.37/0.61          | ((k2_tops_1 @ X21 @ X20)
% 0.37/0.61              = (k7_subset_1 @ (u1_struct_0 @ X21) @ 
% 0.37/0.61                 (k2_pre_topc @ X21 @ X20) @ (k1_tops_1 @ X21 @ X20)))
% 0.37/0.61          | ~ (l1_pre_topc @ X21))),
% 0.37/0.61      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.37/0.61  thf('32', plain,
% 0.37/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.61        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.61            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.61               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.37/0.61      inference('sup-', [status(thm)], ['30', '31'])).
% 0.37/0.61  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('34', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(t52_pre_topc, axiom,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( l1_pre_topc @ A ) =>
% 0.37/0.61       ( ![B:$i]:
% 0.37/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.61           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.37/0.61             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.37/0.61               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.37/0.61  thf('35', plain,
% 0.37/0.61      (![X16 : $i, X17 : $i]:
% 0.37/0.61         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.37/0.61          | ~ (v4_pre_topc @ X16 @ X17)
% 0.37/0.61          | ((k2_pre_topc @ X17 @ X16) = (X16))
% 0.37/0.61          | ~ (l1_pre_topc @ X17))),
% 0.37/0.61      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.37/0.61  thf('36', plain,
% 0.37/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.61        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.37/0.61        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.37/0.61      inference('sup-', [status(thm)], ['34', '35'])).
% 0.37/0.61  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('38', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('39', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.37/0.61      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.37/0.61  thf('40', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(redefinition_k7_subset_1, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i]:
% 0.37/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.61       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.37/0.61  thf('41', plain,
% 0.37/0.61      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.37/0.61         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.37/0.61          | ((k7_subset_1 @ X11 @ X10 @ X12) = (k4_xboole_0 @ X10 @ X12)))),
% 0.37/0.61      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.37/0.61  thf('42', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.37/0.61           = (k4_xboole_0 @ sk_B @ X0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['40', '41'])).
% 0.37/0.61  thf('43', plain,
% 0.37/0.61      (((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.61         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.37/0.61      inference('demod', [status(thm)], ['32', '33', '39', '42'])).
% 0.37/0.61  thf('44', plain,
% 0.37/0.61      (((k2_tops_1 @ sk_A @ sk_B)
% 0.37/0.61         = (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.37/0.61      inference('sup+', [status(thm)], ['29', '43'])).
% 0.37/0.61  thf('45', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.37/0.61      inference('demod', [status(thm)], ['26', '44'])).
% 0.37/0.61  thf(d10_xboole_0, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.61  thf('46', plain,
% 0.37/0.61      (![X0 : $i, X2 : $i]:
% 0.37/0.61         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.37/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.61  thf('47', plain,
% 0.37/0.61      ((~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.37/0.61        | ((sk_B) = (k2_tops_1 @ sk_A @ sk_B)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['45', '46'])).
% 0.37/0.61  thf('48', plain,
% 0.37/0.61      ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))) <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['15', '47'])).
% 0.37/0.61  thf('49', plain,
% 0.37/0.61      ((((sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.37/0.61         <= (~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 0.37/0.61      inference('split', [status(esa)], ['0'])).
% 0.37/0.61  thf('50', plain,
% 0.37/0.61      ((((sk_B) != (sk_B)))
% 0.37/0.61         <= (~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B))) & 
% 0.37/0.61             ((v3_tops_1 @ sk_B @ sk_A)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['48', '49'])).
% 0.37/0.61  thf('51', plain,
% 0.37/0.61      ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))) | ~ ((v3_tops_1 @ sk_B @ sk_A))),
% 0.37/0.61      inference('simplify', [status(thm)], ['50'])).
% 0.37/0.61  thf('52', plain,
% 0.37/0.61      ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))) | ((v3_tops_1 @ sk_B @ sk_A))),
% 0.37/0.61      inference('split', [status(esa)], ['2'])).
% 0.37/0.61  thf('53', plain,
% 0.37/0.61      ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B)))
% 0.37/0.61         <= ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 0.37/0.61      inference('split', [status(esa)], ['2'])).
% 0.37/0.61  thf('54', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('55', plain,
% 0.37/0.61      (![X24 : $i, X25 : $i]:
% 0.37/0.61         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.37/0.61          | ~ (r1_tarski @ X24 @ (k2_tops_1 @ X25 @ X24))
% 0.37/0.61          | (v2_tops_1 @ X24 @ X25)
% 0.37/0.61          | ~ (l1_pre_topc @ X25))),
% 0.37/0.61      inference('cnf', [status(esa)], [t88_tops_1])).
% 0.37/0.61  thf('56', plain,
% 0.37/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.61        | (v2_tops_1 @ sk_B @ sk_A)
% 0.37/0.61        | ~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['54', '55'])).
% 0.37/0.61  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('58', plain,
% 0.37/0.61      (((v2_tops_1 @ sk_B @ sk_A)
% 0.37/0.61        | ~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.37/0.61      inference('demod', [status(thm)], ['56', '57'])).
% 0.37/0.61  thf('59', plain,
% 0.37/0.61      (((~ (r1_tarski @ sk_B @ sk_B) | (v2_tops_1 @ sk_B @ sk_A)))
% 0.37/0.61         <= ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 0.37/0.61      inference('sup-', [status(thm)], ['53', '58'])).
% 0.37/0.61  thf('60', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.37/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.61  thf('61', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.37/0.61      inference('simplify', [status(thm)], ['60'])).
% 0.37/0.61  thf('62', plain,
% 0.37/0.61      (((v2_tops_1 @ sk_B @ sk_A)) <= ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 0.37/0.61      inference('demod', [status(thm)], ['59', '61'])).
% 0.37/0.61  thf('63', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(d5_tops_1, axiom,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( l1_pre_topc @ A ) =>
% 0.37/0.61       ( ![B:$i]:
% 0.37/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.61           ( ( v3_tops_1 @ B @ A ) <=>
% 0.37/0.61             ( v2_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) ))).
% 0.37/0.61  thf('64', plain,
% 0.37/0.61      (![X18 : $i, X19 : $i]:
% 0.37/0.61         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.37/0.61          | ~ (v2_tops_1 @ (k2_pre_topc @ X19 @ X18) @ X19)
% 0.37/0.61          | (v3_tops_1 @ X18 @ X19)
% 0.37/0.61          | ~ (l1_pre_topc @ X19))),
% 0.37/0.61      inference('cnf', [status(esa)], [d5_tops_1])).
% 0.37/0.61  thf('65', plain,
% 0.37/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.61        | (v3_tops_1 @ sk_B @ sk_A)
% 0.37/0.61        | ~ (v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A))),
% 0.37/0.61      inference('sup-', [status(thm)], ['63', '64'])).
% 0.37/0.61  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('67', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.37/0.61      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.37/0.61  thf('68', plain, (((v3_tops_1 @ sk_B @ sk_A) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.37/0.61      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.37/0.61  thf('69', plain,
% 0.37/0.61      (((v3_tops_1 @ sk_B @ sk_A)) <= ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 0.37/0.61      inference('sup-', [status(thm)], ['62', '68'])).
% 0.37/0.61  thf('70', plain,
% 0.37/0.61      ((~ (v3_tops_1 @ sk_B @ sk_A)) <= (~ ((v3_tops_1 @ sk_B @ sk_A)))),
% 0.37/0.61      inference('split', [status(esa)], ['0'])).
% 0.37/0.61  thf('71', plain,
% 0.37/0.61      (~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B))) | ((v3_tops_1 @ sk_B @ sk_A))),
% 0.37/0.61      inference('sup-', [status(thm)], ['69', '70'])).
% 0.37/0.61  thf('72', plain, ($false),
% 0.37/0.61      inference('sat_resolution*', [status(thm)], ['1', '51', '52', '71'])).
% 0.37/0.61  
% 0.37/0.61  % SZS output end Refutation
% 0.37/0.61  
% 0.37/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
