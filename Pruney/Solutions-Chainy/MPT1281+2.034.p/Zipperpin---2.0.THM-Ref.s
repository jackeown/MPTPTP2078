%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7gs0N3U3C4

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:49 EST 2020

% Result     : Theorem 31.65s
% Output     : Refutation 31.65s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 154 expanded)
%              Number of leaves         :   23 (  54 expanded)
%              Depth                    :   16
%              Number of atoms          :  774 (1931 expanded)
%              Number of equality atoms :   18 (  25 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(v5_tops_1_type,type,(
    v5_tops_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t103_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v5_tops_1 @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v5_tops_1 @ B @ A )
             => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t103_tops_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v5_tops_1 @ B @ A )
          <=> ( B
              = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v5_tops_1 @ X14 @ X15 )
      | ( X14
        = ( k2_pre_topc @ X15 @ ( k1_tops_1 @ X15 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[d7_tops_1])).

thf('3',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( sk_B
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v5_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v5_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( sk_B
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['0','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('11',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X8 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('13',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('17',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( ( k1_tops_1 @ X11 @ X10 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X11 ) @ ( k2_pre_topc @ X11 @ ( k3_subset_1 @ ( u1_struct_0 @ X11 ) @ X10 ) ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('20',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('25',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X8 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('27',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(t42_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) )).

thf('30',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X6 @ X7 ) @ ( k3_subset_1 @ X6 @ ( k9_subset_1 @ X6 @ X7 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t42_subset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['8','31'])).

thf('33',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','22'])).

thf(d2_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('34',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( ( k2_tops_1 @ X13 @ X12 )
        = ( k9_subset_1 @ ( u1_struct_0 @ X13 ) @ ( k2_pre_topc @ X13 @ X12 ) @ ( k2_pre_topc @ X13 @ ( k3_subset_1 @ ( u1_struct_0 @ X13 ) @ X12 ) ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_1])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t102_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v5_tops_1 @ B @ A )
           => ( ( k2_tops_1 @ A @ ( k1_tops_1 @ A @ B ) )
              = ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('39',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( ( k2_tops_1 @ X19 @ ( k1_tops_1 @ X19 @ X18 ) )
        = ( k2_tops_1 @ X19 @ X18 ) )
      | ~ ( v5_tops_1 @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t102_tops_1])).

thf('40',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v5_tops_1 @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v5_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,
    ( sk_B
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('45',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['37','43','44'])).

thf('46',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','45'])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('47',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X3 @ X2 ) @ ( k3_subset_1 @ X3 @ X4 ) )
      | ( r1_tarski @ X4 @ X2 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('48',plain,
    ( ~ ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('50',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('51',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['48','53','54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['7','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7gs0N3U3C4
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:35:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 31.65/31.85  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 31.65/31.85  % Solved by: fo/fo7.sh
% 31.65/31.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 31.65/31.85  % done 5010 iterations in 31.387s
% 31.65/31.85  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 31.65/31.85  % SZS output start Refutation
% 31.65/31.85  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 31.65/31.85  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 31.65/31.85  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 31.65/31.85  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 31.65/31.85  thf(sk_B_type, type, sk_B: $i).
% 31.65/31.85  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 31.65/31.85  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 31.65/31.85  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 31.65/31.85  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 31.65/31.85  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 31.65/31.85  thf(v5_tops_1_type, type, v5_tops_1: $i > $i > $o).
% 31.65/31.85  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 31.65/31.85  thf(sk_A_type, type, sk_A: $i).
% 31.65/31.85  thf(t103_tops_1, conjecture,
% 31.65/31.85    (![A:$i]:
% 31.65/31.85     ( ( l1_pre_topc @ A ) =>
% 31.65/31.85       ( ![B:$i]:
% 31.65/31.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 31.65/31.85           ( ( v5_tops_1 @ B @ A ) =>
% 31.65/31.85             ( r1_tarski @
% 31.65/31.85               ( k2_tops_1 @ A @ B ) @ 
% 31.65/31.85               ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 31.65/31.85  thf(zf_stmt_0, negated_conjecture,
% 31.65/31.85    (~( ![A:$i]:
% 31.65/31.85        ( ( l1_pre_topc @ A ) =>
% 31.65/31.85          ( ![B:$i]:
% 31.65/31.85            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 31.65/31.85              ( ( v5_tops_1 @ B @ A ) =>
% 31.65/31.85                ( r1_tarski @
% 31.65/31.85                  ( k2_tops_1 @ A @ B ) @ 
% 31.65/31.85                  ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 31.65/31.85    inference('cnf.neg', [status(esa)], [t103_tops_1])).
% 31.65/31.85  thf('0', plain,
% 31.65/31.85      (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 31.65/31.85          (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 31.65/31.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.65/31.85  thf('1', plain,
% 31.65/31.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 31.65/31.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.65/31.85  thf(d7_tops_1, axiom,
% 31.65/31.85    (![A:$i]:
% 31.65/31.85     ( ( l1_pre_topc @ A ) =>
% 31.65/31.85       ( ![B:$i]:
% 31.65/31.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 31.65/31.85           ( ( v5_tops_1 @ B @ A ) <=>
% 31.65/31.85             ( ( B ) = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 31.65/31.85  thf('2', plain,
% 31.65/31.85      (![X14 : $i, X15 : $i]:
% 31.65/31.85         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 31.65/31.85          | ~ (v5_tops_1 @ X14 @ X15)
% 31.65/31.85          | ((X14) = (k2_pre_topc @ X15 @ (k1_tops_1 @ X15 @ X14)))
% 31.65/31.85          | ~ (l1_pre_topc @ X15))),
% 31.65/31.85      inference('cnf', [status(esa)], [d7_tops_1])).
% 31.65/31.85  thf('3', plain,
% 31.65/31.85      ((~ (l1_pre_topc @ sk_A)
% 31.65/31.85        | ((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 31.65/31.85        | ~ (v5_tops_1 @ sk_B @ sk_A))),
% 31.65/31.85      inference('sup-', [status(thm)], ['1', '2'])).
% 31.65/31.85  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 31.65/31.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.65/31.85  thf('5', plain, ((v5_tops_1 @ sk_B @ sk_A)),
% 31.65/31.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.65/31.85  thf('6', plain,
% 31.65/31.85      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 31.65/31.85      inference('demod', [status(thm)], ['3', '4', '5'])).
% 31.65/31.85  thf('7', plain, (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 31.65/31.85      inference('demod', [status(thm)], ['0', '6'])).
% 31.65/31.85  thf('8', plain,
% 31.65/31.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 31.65/31.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.65/31.85  thf('9', plain,
% 31.65/31.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 31.65/31.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.65/31.85  thf(dt_k3_subset_1, axiom,
% 31.65/31.85    (![A:$i,B:$i]:
% 31.65/31.85     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 31.65/31.85       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 31.65/31.85  thf('10', plain,
% 31.65/31.85      (![X0 : $i, X1 : $i]:
% 31.65/31.85         ((m1_subset_1 @ (k3_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 31.65/31.85          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 31.65/31.85      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 31.65/31.85  thf('11', plain,
% 31.65/31.85      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 31.65/31.85        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 31.65/31.85      inference('sup-', [status(thm)], ['9', '10'])).
% 31.65/31.85  thf(dt_k2_pre_topc, axiom,
% 31.65/31.85    (![A:$i,B:$i]:
% 31.65/31.85     ( ( ( l1_pre_topc @ A ) & 
% 31.65/31.85         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 31.65/31.85       ( m1_subset_1 @
% 31.65/31.85         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 31.65/31.85  thf('12', plain,
% 31.65/31.85      (![X8 : $i, X9 : $i]:
% 31.65/31.85         (~ (l1_pre_topc @ X8)
% 31.65/31.85          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 31.65/31.85          | (m1_subset_1 @ (k2_pre_topc @ X8 @ X9) @ 
% 31.65/31.85             (k1_zfmisc_1 @ (u1_struct_0 @ X8))))),
% 31.65/31.85      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 31.65/31.85  thf('13', plain,
% 31.65/31.85      (((m1_subset_1 @ 
% 31.65/31.85         (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 31.65/31.85         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 31.65/31.85        | ~ (l1_pre_topc @ sk_A))),
% 31.65/31.85      inference('sup-', [status(thm)], ['11', '12'])).
% 31.65/31.85  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 31.65/31.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.65/31.85  thf('15', plain,
% 31.65/31.85      ((m1_subset_1 @ 
% 31.65/31.85        (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 31.65/31.85        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 31.65/31.85      inference('demod', [status(thm)], ['13', '14'])).
% 31.65/31.85  thf('16', plain,
% 31.65/31.85      (![X0 : $i, X1 : $i]:
% 31.65/31.85         ((m1_subset_1 @ (k3_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 31.65/31.85          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 31.65/31.85      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 31.65/31.85  thf('17', plain,
% 31.65/31.85      ((m1_subset_1 @ 
% 31.65/31.85        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 31.65/31.85         (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))) @ 
% 31.65/31.85        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 31.65/31.85      inference('sup-', [status(thm)], ['15', '16'])).
% 31.65/31.85  thf('18', plain,
% 31.65/31.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 31.65/31.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.65/31.85  thf(d1_tops_1, axiom,
% 31.65/31.85    (![A:$i]:
% 31.65/31.85     ( ( l1_pre_topc @ A ) =>
% 31.65/31.85       ( ![B:$i]:
% 31.65/31.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 31.65/31.85           ( ( k1_tops_1 @ A @ B ) =
% 31.65/31.85             ( k3_subset_1 @
% 31.65/31.85               ( u1_struct_0 @ A ) @ 
% 31.65/31.85               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 31.65/31.85  thf('19', plain,
% 31.65/31.85      (![X10 : $i, X11 : $i]:
% 31.65/31.85         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 31.65/31.85          | ((k1_tops_1 @ X11 @ X10)
% 31.65/31.85              = (k3_subset_1 @ (u1_struct_0 @ X11) @ 
% 31.65/31.85                 (k2_pre_topc @ X11 @ (k3_subset_1 @ (u1_struct_0 @ X11) @ X10))))
% 31.65/31.85          | ~ (l1_pre_topc @ X11))),
% 31.65/31.85      inference('cnf', [status(esa)], [d1_tops_1])).
% 31.65/31.85  thf('20', plain,
% 31.65/31.85      ((~ (l1_pre_topc @ sk_A)
% 31.65/31.85        | ((k1_tops_1 @ sk_A @ sk_B)
% 31.65/31.85            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 31.65/31.85               (k2_pre_topc @ sk_A @ 
% 31.65/31.85                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 31.65/31.85      inference('sup-', [status(thm)], ['18', '19'])).
% 31.65/31.85  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 31.65/31.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.65/31.85  thf('22', plain,
% 31.65/31.85      (((k1_tops_1 @ sk_A @ sk_B)
% 31.65/31.85         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 31.65/31.85            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 31.65/31.85      inference('demod', [status(thm)], ['20', '21'])).
% 31.65/31.85  thf('23', plain,
% 31.65/31.85      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 31.65/31.85        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 31.65/31.85      inference('demod', [status(thm)], ['17', '22'])).
% 31.65/31.85  thf('24', plain,
% 31.65/31.85      (![X0 : $i, X1 : $i]:
% 31.65/31.85         ((m1_subset_1 @ (k3_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 31.65/31.85          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 31.65/31.85      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 31.65/31.85  thf('25', plain,
% 31.65/31.85      ((m1_subset_1 @ 
% 31.65/31.85        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 31.65/31.85        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 31.65/31.85      inference('sup-', [status(thm)], ['23', '24'])).
% 31.65/31.85  thf('26', plain,
% 31.65/31.85      (![X8 : $i, X9 : $i]:
% 31.65/31.85         (~ (l1_pre_topc @ X8)
% 31.65/31.85          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 31.65/31.85          | (m1_subset_1 @ (k2_pre_topc @ X8 @ X9) @ 
% 31.65/31.85             (k1_zfmisc_1 @ (u1_struct_0 @ X8))))),
% 31.65/31.85      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 31.65/31.85  thf('27', plain,
% 31.65/31.85      (((m1_subset_1 @ 
% 31.65/31.85         (k2_pre_topc @ sk_A @ 
% 31.65/31.85          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))) @ 
% 31.65/31.85         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 31.65/31.85        | ~ (l1_pre_topc @ sk_A))),
% 31.65/31.85      inference('sup-', [status(thm)], ['25', '26'])).
% 31.65/31.85  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 31.65/31.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.65/31.85  thf('29', plain,
% 31.65/31.85      ((m1_subset_1 @ 
% 31.65/31.85        (k2_pre_topc @ sk_A @ 
% 31.65/31.85         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))) @ 
% 31.65/31.85        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 31.65/31.85      inference('demod', [status(thm)], ['27', '28'])).
% 31.65/31.85  thf(t42_subset_1, axiom,
% 31.65/31.85    (![A:$i,B:$i]:
% 31.65/31.85     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 31.65/31.85       ( ![C:$i]:
% 31.65/31.85         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 31.65/31.85           ( r1_tarski @
% 31.65/31.85             ( k3_subset_1 @ A @ B ) @ 
% 31.65/31.85             ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) ))).
% 31.65/31.85  thf('30', plain,
% 31.65/31.85      (![X5 : $i, X6 : $i, X7 : $i]:
% 31.65/31.85         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 31.65/31.85          | (r1_tarski @ (k3_subset_1 @ X6 @ X7) @ 
% 31.65/31.85             (k3_subset_1 @ X6 @ (k9_subset_1 @ X6 @ X7 @ X5)))
% 31.65/31.85          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 31.65/31.85      inference('cnf', [status(esa)], [t42_subset_1])).
% 31.65/31.85  thf('31', plain,
% 31.65/31.85      (![X0 : $i]:
% 31.65/31.85         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 31.65/31.85          | (r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 31.65/31.85             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 31.65/31.85              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 31.65/31.85               (k2_pre_topc @ sk_A @ 
% 31.65/31.85                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))))))),
% 31.65/31.85      inference('sup-', [status(thm)], ['29', '30'])).
% 31.65/31.85  thf('32', plain,
% 31.65/31.85      ((r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 31.65/31.85        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 31.65/31.85         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 31.65/31.85          (k2_pre_topc @ sk_A @ 
% 31.65/31.85           (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))))))),
% 31.65/31.85      inference('sup-', [status(thm)], ['8', '31'])).
% 31.65/31.85  thf('33', plain,
% 31.65/31.85      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 31.65/31.85        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 31.65/31.85      inference('demod', [status(thm)], ['17', '22'])).
% 31.65/31.85  thf(d2_tops_1, axiom,
% 31.65/31.85    (![A:$i]:
% 31.65/31.85     ( ( l1_pre_topc @ A ) =>
% 31.65/31.85       ( ![B:$i]:
% 31.65/31.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 31.65/31.85           ( ( k2_tops_1 @ A @ B ) =
% 31.65/31.85             ( k9_subset_1 @
% 31.65/31.85               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 31.65/31.85               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 31.65/31.85  thf('34', plain,
% 31.65/31.85      (![X12 : $i, X13 : $i]:
% 31.65/31.85         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 31.65/31.85          | ((k2_tops_1 @ X13 @ X12)
% 31.65/31.85              = (k9_subset_1 @ (u1_struct_0 @ X13) @ 
% 31.65/31.85                 (k2_pre_topc @ X13 @ X12) @ 
% 31.65/31.85                 (k2_pre_topc @ X13 @ (k3_subset_1 @ (u1_struct_0 @ X13) @ X12))))
% 31.65/31.85          | ~ (l1_pre_topc @ X13))),
% 31.65/31.85      inference('cnf', [status(esa)], [d2_tops_1])).
% 31.65/31.85  thf('35', plain,
% 31.65/31.85      ((~ (l1_pre_topc @ sk_A)
% 31.65/31.85        | ((k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 31.65/31.85            = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 31.65/31.85               (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 31.65/31.85               (k2_pre_topc @ sk_A @ 
% 31.65/31.85                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))))))),
% 31.65/31.85      inference('sup-', [status(thm)], ['33', '34'])).
% 31.65/31.85  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 31.65/31.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.65/31.85  thf('37', plain,
% 31.65/31.85      (((k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 31.65/31.85         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 31.65/31.85            (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 31.65/31.85            (k2_pre_topc @ sk_A @ 
% 31.65/31.85             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))))),
% 31.65/31.85      inference('demod', [status(thm)], ['35', '36'])).
% 31.65/31.85  thf('38', plain,
% 31.65/31.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 31.65/31.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.65/31.85  thf(t102_tops_1, axiom,
% 31.65/31.85    (![A:$i]:
% 31.65/31.85     ( ( l1_pre_topc @ A ) =>
% 31.65/31.85       ( ![B:$i]:
% 31.65/31.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 31.65/31.85           ( ( v5_tops_1 @ B @ A ) =>
% 31.65/31.85             ( ( k2_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) =
% 31.65/31.85               ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 31.65/31.85  thf('39', plain,
% 31.65/31.85      (![X18 : $i, X19 : $i]:
% 31.65/31.85         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 31.65/31.85          | ((k2_tops_1 @ X19 @ (k1_tops_1 @ X19 @ X18))
% 31.65/31.85              = (k2_tops_1 @ X19 @ X18))
% 31.65/31.85          | ~ (v5_tops_1 @ X18 @ X19)
% 31.65/31.85          | ~ (l1_pre_topc @ X19))),
% 31.65/31.85      inference('cnf', [status(esa)], [t102_tops_1])).
% 31.65/31.85  thf('40', plain,
% 31.65/31.85      ((~ (l1_pre_topc @ sk_A)
% 31.65/31.85        | ~ (v5_tops_1 @ sk_B @ sk_A)
% 31.65/31.85        | ((k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 31.65/31.85            = (k2_tops_1 @ sk_A @ sk_B)))),
% 31.65/31.85      inference('sup-', [status(thm)], ['38', '39'])).
% 31.65/31.85  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 31.65/31.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.65/31.85  thf('42', plain, ((v5_tops_1 @ sk_B @ sk_A)),
% 31.65/31.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.65/31.85  thf('43', plain,
% 31.65/31.85      (((k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 31.65/31.85         = (k2_tops_1 @ sk_A @ sk_B))),
% 31.65/31.85      inference('demod', [status(thm)], ['40', '41', '42'])).
% 31.65/31.85  thf('44', plain,
% 31.65/31.85      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 31.65/31.85      inference('demod', [status(thm)], ['3', '4', '5'])).
% 31.65/31.85  thf('45', plain,
% 31.65/31.85      (((k2_tops_1 @ sk_A @ sk_B)
% 31.65/31.85         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 31.65/31.85            (k2_pre_topc @ sk_A @ 
% 31.65/31.85             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))))),
% 31.65/31.85      inference('demod', [status(thm)], ['37', '43', '44'])).
% 31.65/31.85  thf('46', plain,
% 31.65/31.85      ((r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 31.65/31.85        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_tops_1 @ sk_A @ sk_B)))),
% 31.65/31.85      inference('demod', [status(thm)], ['32', '45'])).
% 31.65/31.85  thf(t31_subset_1, axiom,
% 31.65/31.85    (![A:$i,B:$i]:
% 31.65/31.85     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 31.65/31.85       ( ![C:$i]:
% 31.65/31.85         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 31.65/31.85           ( ( r1_tarski @ B @ C ) <=>
% 31.65/31.85             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 31.65/31.85  thf('47', plain,
% 31.65/31.85      (![X2 : $i, X3 : $i, X4 : $i]:
% 31.65/31.85         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 31.65/31.85          | ~ (r1_tarski @ (k3_subset_1 @ X3 @ X2) @ (k3_subset_1 @ X3 @ X4))
% 31.65/31.85          | (r1_tarski @ X4 @ X2)
% 31.65/31.85          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 31.65/31.85      inference('cnf', [status(esa)], [t31_subset_1])).
% 31.65/31.85  thf('48', plain,
% 31.65/31.85      ((~ (m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 31.65/31.85           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 31.65/31.85        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 31.65/31.85        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 31.65/31.85      inference('sup-', [status(thm)], ['46', '47'])).
% 31.65/31.85  thf('49', plain,
% 31.65/31.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 31.65/31.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.65/31.85  thf(dt_k2_tops_1, axiom,
% 31.65/31.85    (![A:$i,B:$i]:
% 31.65/31.85     ( ( ( l1_pre_topc @ A ) & 
% 31.65/31.85         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 31.65/31.85       ( m1_subset_1 @
% 31.65/31.85         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 31.65/31.85  thf('50', plain,
% 31.65/31.85      (![X16 : $i, X17 : $i]:
% 31.65/31.85         (~ (l1_pre_topc @ X16)
% 31.65/31.85          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 31.65/31.85          | (m1_subset_1 @ (k2_tops_1 @ X16 @ X17) @ 
% 31.65/31.85             (k1_zfmisc_1 @ (u1_struct_0 @ X16))))),
% 31.65/31.85      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 31.65/31.85  thf('51', plain,
% 31.65/31.85      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 31.65/31.85         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 31.65/31.85        | ~ (l1_pre_topc @ sk_A))),
% 31.65/31.85      inference('sup-', [status(thm)], ['49', '50'])).
% 31.65/31.85  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 31.65/31.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.65/31.85  thf('53', plain,
% 31.65/31.85      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 31.65/31.85        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 31.65/31.85      inference('demod', [status(thm)], ['51', '52'])).
% 31.65/31.85  thf('54', plain,
% 31.65/31.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 31.65/31.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 31.65/31.85  thf('55', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 31.65/31.85      inference('demod', [status(thm)], ['48', '53', '54'])).
% 31.65/31.85  thf('56', plain, ($false), inference('demod', [status(thm)], ['7', '55'])).
% 31.65/31.85  
% 31.65/31.85  % SZS output end Refutation
% 31.65/31.85  
% 31.65/31.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
