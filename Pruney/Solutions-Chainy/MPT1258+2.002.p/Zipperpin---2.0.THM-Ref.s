%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0ifrjhK2sl

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:19 EST 2020

% Result     : Theorem 1.02s
% Output     : Refutation 1.02s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 229 expanded)
%              Number of leaves         :   21 (  76 expanded)
%              Depth                    :   14
%              Number of atoms          :  790 (2934 expanded)
%              Number of equality atoms :   35 ( 134 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(t74_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( k1_tops_1 @ A @ B )
              = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t74_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('3',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t33_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k3_subset_1 @ A @ ( k7_subset_1 @ A @ B @ C ) )
            = ( k4_subset_1 @ A @ ( k3_subset_1 @ A @ B ) @ C ) ) ) ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( ( k3_subset_1 @ X8 @ ( k7_subset_1 @ X8 @ X9 @ X7 ) )
        = ( k4_subset_1 @ X8 @ ( k3_subset_1 @ X8 @ X9 ) @ X7 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t33_subset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
        = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','7'])).

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

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('12',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( ( k2_pre_topc @ X17 @ X16 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X17 ) @ X16 @ ( k2_tops_1 @ X17 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('13',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t62_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k2_tops_1 @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) )).

thf('16',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( ( k2_tops_1 @ X15 @ X14 )
        = ( k2_tops_1 @ X15 @ ( k3_subset_1 @ ( u1_struct_0 @ X15 ) @ X14 ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t62_tops_1])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('20',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X6 @ ( k3_subset_1 @ X6 @ X5 ) )
        = X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('21',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['17','18','21'])).

thf('23',plain,
    ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','14','22'])).

thf('24',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('26',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X3 @ X2 @ X4 ) @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['24','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('32',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('34',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( ( k1_tops_1 @ X11 @ X10 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X11 ) @ ( k2_pre_topc @ X11 @ ( k3_subset_1 @ ( u1_struct_0 @ X11 ) @ X10 ) ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','37'])).

thf('39',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X6 @ ( k3_subset_1 @ X6 @ X5 ) )
        = X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('40',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','23'])).

thf('42',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['24','29'])).

thf('43',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X6 @ ( k3_subset_1 @ X6 @ X5 ) )
        = X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('44',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) )
    = ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('46',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['41','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('49',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X6 @ ( k3_subset_1 @ X6 @ X5 ) )
        = X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['47','50'])).

thf('52',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['40','51'])).

thf('53',plain,(
    ( k1_tops_1 @ sk_A @ sk_B )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['52','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0ifrjhK2sl
% 0.14/0.37  % Computer   : n012.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 15:26:22 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 1.02/1.21  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.02/1.21  % Solved by: fo/fo7.sh
% 1.02/1.21  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.02/1.21  % done 520 iterations in 0.725s
% 1.02/1.21  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.02/1.21  % SZS output start Refutation
% 1.02/1.21  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.02/1.21  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.02/1.21  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.02/1.21  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.02/1.21  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.02/1.21  thf(sk_B_type, type, sk_B: $i).
% 1.02/1.21  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.02/1.21  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.02/1.21  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.02/1.21  thf(sk_A_type, type, sk_A: $i).
% 1.02/1.21  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.02/1.21  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.02/1.21  thf(t74_tops_1, conjecture,
% 1.02/1.21    (![A:$i]:
% 1.02/1.21     ( ( l1_pre_topc @ A ) =>
% 1.02/1.21       ( ![B:$i]:
% 1.02/1.21         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.02/1.21           ( ( k1_tops_1 @ A @ B ) =
% 1.02/1.21             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.02/1.21  thf(zf_stmt_0, negated_conjecture,
% 1.02/1.21    (~( ![A:$i]:
% 1.02/1.21        ( ( l1_pre_topc @ A ) =>
% 1.02/1.21          ( ![B:$i]:
% 1.02/1.21            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.02/1.21              ( ( k1_tops_1 @ A @ B ) =
% 1.02/1.21                ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ) )),
% 1.02/1.21    inference('cnf.neg', [status(esa)], [t74_tops_1])).
% 1.02/1.21  thf('0', plain,
% 1.02/1.21      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('1', plain,
% 1.02/1.21      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf(dt_k2_tops_1, axiom,
% 1.02/1.21    (![A:$i,B:$i]:
% 1.02/1.21     ( ( ( l1_pre_topc @ A ) & 
% 1.02/1.21         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.02/1.21       ( m1_subset_1 @
% 1.02/1.21         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.02/1.21  thf('2', plain,
% 1.02/1.21      (![X12 : $i, X13 : $i]:
% 1.02/1.21         (~ (l1_pre_topc @ X12)
% 1.02/1.21          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 1.02/1.21          | (m1_subset_1 @ (k2_tops_1 @ X12 @ X13) @ 
% 1.02/1.21             (k1_zfmisc_1 @ (u1_struct_0 @ X12))))),
% 1.02/1.21      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 1.02/1.21  thf('3', plain,
% 1.02/1.21      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.02/1.21         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.02/1.21        | ~ (l1_pre_topc @ sk_A))),
% 1.02/1.21      inference('sup-', [status(thm)], ['1', '2'])).
% 1.02/1.21  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('5', plain,
% 1.02/1.21      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.02/1.21        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.21      inference('demod', [status(thm)], ['3', '4'])).
% 1.02/1.21  thf(t33_subset_1, axiom,
% 1.02/1.21    (![A:$i,B:$i]:
% 1.02/1.21     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.02/1.21       ( ![C:$i]:
% 1.02/1.21         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.02/1.21           ( ( k3_subset_1 @ A @ ( k7_subset_1 @ A @ B @ C ) ) =
% 1.02/1.21             ( k4_subset_1 @ A @ ( k3_subset_1 @ A @ B ) @ C ) ) ) ) ))).
% 1.02/1.21  thf('6', plain,
% 1.02/1.21      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.02/1.21         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 1.02/1.21          | ((k3_subset_1 @ X8 @ (k7_subset_1 @ X8 @ X9 @ X7))
% 1.02/1.21              = (k4_subset_1 @ X8 @ (k3_subset_1 @ X8 @ X9) @ X7))
% 1.02/1.21          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 1.02/1.21      inference('cnf', [status(esa)], [t33_subset_1])).
% 1.02/1.21  thf('7', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.02/1.21          | ((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.02/1.21              (k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 1.02/1.21               (k2_tops_1 @ sk_A @ sk_B)))
% 1.02/1.21              = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.02/1.21                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 1.02/1.21                 (k2_tops_1 @ sk_A @ sk_B))))),
% 1.02/1.21      inference('sup-', [status(thm)], ['5', '6'])).
% 1.02/1.21  thf('8', plain,
% 1.02/1.21      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.02/1.21         (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.02/1.21         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.02/1.21            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.02/1.21            (k2_tops_1 @ sk_A @ sk_B)))),
% 1.02/1.21      inference('sup-', [status(thm)], ['0', '7'])).
% 1.02/1.21  thf('9', plain,
% 1.02/1.21      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf(dt_k3_subset_1, axiom,
% 1.02/1.21    (![A:$i,B:$i]:
% 1.02/1.21     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.02/1.21       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.02/1.21  thf('10', plain,
% 1.02/1.21      (![X0 : $i, X1 : $i]:
% 1.02/1.21         ((m1_subset_1 @ (k3_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 1.02/1.21          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 1.02/1.21      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 1.02/1.21  thf('11', plain,
% 1.02/1.21      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.02/1.21        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.21      inference('sup-', [status(thm)], ['9', '10'])).
% 1.02/1.21  thf(t65_tops_1, axiom,
% 1.02/1.21    (![A:$i]:
% 1.02/1.21     ( ( l1_pre_topc @ A ) =>
% 1.02/1.21       ( ![B:$i]:
% 1.02/1.21         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.02/1.21           ( ( k2_pre_topc @ A @ B ) =
% 1.02/1.21             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.02/1.21  thf('12', plain,
% 1.02/1.21      (![X16 : $i, X17 : $i]:
% 1.02/1.21         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 1.02/1.21          | ((k2_pre_topc @ X17 @ X16)
% 1.02/1.21              = (k4_subset_1 @ (u1_struct_0 @ X17) @ X16 @ 
% 1.02/1.21                 (k2_tops_1 @ X17 @ X16)))
% 1.02/1.21          | ~ (l1_pre_topc @ X17))),
% 1.02/1.21      inference('cnf', [status(esa)], [t65_tops_1])).
% 1.02/1.21  thf('13', plain,
% 1.02/1.21      ((~ (l1_pre_topc @ sk_A)
% 1.02/1.21        | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.02/1.21            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.02/1.21               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.02/1.21               (k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 1.02/1.21      inference('sup-', [status(thm)], ['11', '12'])).
% 1.02/1.21  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('15', plain,
% 1.02/1.21      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.02/1.21        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.21      inference('sup-', [status(thm)], ['9', '10'])).
% 1.02/1.21  thf(t62_tops_1, axiom,
% 1.02/1.21    (![A:$i]:
% 1.02/1.21     ( ( l1_pre_topc @ A ) =>
% 1.02/1.21       ( ![B:$i]:
% 1.02/1.21         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.02/1.21           ( ( k2_tops_1 @ A @ B ) =
% 1.02/1.21             ( k2_tops_1 @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 1.02/1.21  thf('16', plain,
% 1.02/1.21      (![X14 : $i, X15 : $i]:
% 1.02/1.21         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 1.02/1.21          | ((k2_tops_1 @ X15 @ X14)
% 1.02/1.21              = (k2_tops_1 @ X15 @ (k3_subset_1 @ (u1_struct_0 @ X15) @ X14)))
% 1.02/1.21          | ~ (l1_pre_topc @ X15))),
% 1.02/1.21      inference('cnf', [status(esa)], [t62_tops_1])).
% 1.02/1.21  thf('17', plain,
% 1.02/1.21      ((~ (l1_pre_topc @ sk_A)
% 1.02/1.21        | ((k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.02/1.21            = (k2_tops_1 @ sk_A @ 
% 1.02/1.21               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.02/1.21                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 1.02/1.21      inference('sup-', [status(thm)], ['15', '16'])).
% 1.02/1.21  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('19', plain,
% 1.02/1.21      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf(involutiveness_k3_subset_1, axiom,
% 1.02/1.21    (![A:$i,B:$i]:
% 1.02/1.21     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.02/1.21       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 1.02/1.21  thf('20', plain,
% 1.02/1.21      (![X5 : $i, X6 : $i]:
% 1.02/1.21         (((k3_subset_1 @ X6 @ (k3_subset_1 @ X6 @ X5)) = (X5))
% 1.02/1.21          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 1.02/1.21      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.02/1.21  thf('21', plain,
% 1.02/1.21      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.02/1.21         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 1.02/1.21      inference('sup-', [status(thm)], ['19', '20'])).
% 1.02/1.21  thf('22', plain,
% 1.02/1.21      (((k2_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.02/1.21         = (k2_tops_1 @ sk_A @ sk_B))),
% 1.02/1.21      inference('demod', [status(thm)], ['17', '18', '21'])).
% 1.02/1.21  thf('23', plain,
% 1.02/1.21      (((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.02/1.21         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.02/1.21            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.02/1.21            (k2_tops_1 @ sk_A @ sk_B)))),
% 1.02/1.21      inference('demod', [status(thm)], ['13', '14', '22'])).
% 1.02/1.21  thf('24', plain,
% 1.02/1.21      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.02/1.21         (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.02/1.21         = (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 1.02/1.21      inference('demod', [status(thm)], ['8', '23'])).
% 1.02/1.21  thf('25', plain,
% 1.02/1.21      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf(dt_k7_subset_1, axiom,
% 1.02/1.21    (![A:$i,B:$i,C:$i]:
% 1.02/1.21     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.02/1.21       ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.02/1.21  thf('26', plain,
% 1.02/1.21      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.02/1.21         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 1.02/1.21          | (m1_subset_1 @ (k7_subset_1 @ X3 @ X2 @ X4) @ (k1_zfmisc_1 @ X3)))),
% 1.02/1.21      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 1.02/1.21  thf('27', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         (m1_subset_1 @ (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 1.02/1.21          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.21      inference('sup-', [status(thm)], ['25', '26'])).
% 1.02/1.21  thf('28', plain,
% 1.02/1.21      (![X0 : $i, X1 : $i]:
% 1.02/1.21         ((m1_subset_1 @ (k3_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 1.02/1.21          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 1.02/1.21      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 1.02/1.21  thf('29', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         (m1_subset_1 @ 
% 1.02/1.21          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.02/1.21           (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)) @ 
% 1.02/1.21          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.21      inference('sup-', [status(thm)], ['27', '28'])).
% 1.02/1.21  thf('30', plain,
% 1.02/1.21      ((m1_subset_1 @ 
% 1.02/1.21        (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 1.02/1.21        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.21      inference('sup+', [status(thm)], ['24', '29'])).
% 1.02/1.21  thf('31', plain,
% 1.02/1.21      (![X0 : $i, X1 : $i]:
% 1.02/1.21         ((m1_subset_1 @ (k3_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 1.02/1.21          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 1.02/1.21      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 1.02/1.21  thf('32', plain,
% 1.02/1.21      ((m1_subset_1 @ 
% 1.02/1.21        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.02/1.21         (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))) @ 
% 1.02/1.21        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.21      inference('sup-', [status(thm)], ['30', '31'])).
% 1.02/1.21  thf('33', plain,
% 1.02/1.21      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf(d1_tops_1, axiom,
% 1.02/1.21    (![A:$i]:
% 1.02/1.21     ( ( l1_pre_topc @ A ) =>
% 1.02/1.21       ( ![B:$i]:
% 1.02/1.21         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.02/1.21           ( ( k1_tops_1 @ A @ B ) =
% 1.02/1.21             ( k3_subset_1 @
% 1.02/1.21               ( u1_struct_0 @ A ) @ 
% 1.02/1.21               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 1.02/1.21  thf('34', plain,
% 1.02/1.21      (![X10 : $i, X11 : $i]:
% 1.02/1.21         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 1.02/1.21          | ((k1_tops_1 @ X11 @ X10)
% 1.02/1.21              = (k3_subset_1 @ (u1_struct_0 @ X11) @ 
% 1.02/1.21                 (k2_pre_topc @ X11 @ (k3_subset_1 @ (u1_struct_0 @ X11) @ X10))))
% 1.02/1.21          | ~ (l1_pre_topc @ X11))),
% 1.02/1.21      inference('cnf', [status(esa)], [d1_tops_1])).
% 1.02/1.21  thf('35', plain,
% 1.02/1.21      ((~ (l1_pre_topc @ sk_A)
% 1.02/1.21        | ((k1_tops_1 @ sk_A @ sk_B)
% 1.02/1.21            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.02/1.21               (k2_pre_topc @ sk_A @ 
% 1.02/1.21                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 1.02/1.21      inference('sup-', [status(thm)], ['33', '34'])).
% 1.02/1.21  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('37', plain,
% 1.02/1.21      (((k1_tops_1 @ sk_A @ sk_B)
% 1.02/1.21         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.02/1.21            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 1.02/1.21      inference('demod', [status(thm)], ['35', '36'])).
% 1.02/1.21  thf('38', plain,
% 1.02/1.21      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 1.02/1.21        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.21      inference('demod', [status(thm)], ['32', '37'])).
% 1.02/1.21  thf('39', plain,
% 1.02/1.21      (![X5 : $i, X6 : $i]:
% 1.02/1.21         (((k3_subset_1 @ X6 @ (k3_subset_1 @ X6 @ X5)) = (X5))
% 1.02/1.21          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 1.02/1.21      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.02/1.21  thf('40', plain,
% 1.02/1.21      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.02/1.21         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))
% 1.02/1.21         = (k1_tops_1 @ sk_A @ sk_B))),
% 1.02/1.21      inference('sup-', [status(thm)], ['38', '39'])).
% 1.02/1.21  thf('41', plain,
% 1.02/1.21      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.02/1.21         (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.02/1.21         = (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 1.02/1.21      inference('demod', [status(thm)], ['8', '23'])).
% 1.02/1.21  thf('42', plain,
% 1.02/1.21      ((m1_subset_1 @ 
% 1.02/1.21        (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 1.02/1.21        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.21      inference('sup+', [status(thm)], ['24', '29'])).
% 1.02/1.21  thf('43', plain,
% 1.02/1.21      (![X5 : $i, X6 : $i]:
% 1.02/1.21         (((k3_subset_1 @ X6 @ (k3_subset_1 @ X6 @ X5)) = (X5))
% 1.02/1.21          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 1.02/1.21      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.02/1.21  thf('44', plain,
% 1.02/1.21      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.02/1.21         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.02/1.21          (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))
% 1.02/1.21         = (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 1.02/1.21      inference('sup-', [status(thm)], ['42', '43'])).
% 1.02/1.21  thf('45', plain,
% 1.02/1.21      (((k1_tops_1 @ sk_A @ sk_B)
% 1.02/1.21         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.02/1.21            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 1.02/1.21      inference('demod', [status(thm)], ['35', '36'])).
% 1.02/1.21  thf('46', plain,
% 1.02/1.21      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 1.02/1.21         = (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 1.02/1.21      inference('demod', [status(thm)], ['44', '45'])).
% 1.02/1.21  thf('47', plain,
% 1.02/1.21      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.02/1.21         (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.02/1.21         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.02/1.21      inference('demod', [status(thm)], ['41', '46'])).
% 1.02/1.21  thf('48', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         (m1_subset_1 @ (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 1.02/1.21          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.21      inference('sup-', [status(thm)], ['25', '26'])).
% 1.02/1.21  thf('49', plain,
% 1.02/1.21      (![X5 : $i, X6 : $i]:
% 1.02/1.21         (((k3_subset_1 @ X6 @ (k3_subset_1 @ X6 @ X5)) = (X5))
% 1.02/1.21          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 1.02/1.21      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.02/1.21  thf('50', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         ((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.02/1.21           (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.02/1.21            (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)))
% 1.02/1.21           = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 1.02/1.21      inference('sup-', [status(thm)], ['48', '49'])).
% 1.02/1.21  thf('51', plain,
% 1.02/1.21      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.02/1.21         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))
% 1.02/1.21         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.02/1.21            (k2_tops_1 @ sk_A @ sk_B)))),
% 1.02/1.21      inference('sup+', [status(thm)], ['47', '50'])).
% 1.02/1.21  thf('52', plain,
% 1.02/1.21      (((k1_tops_1 @ sk_A @ sk_B)
% 1.02/1.21         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.02/1.21            (k2_tops_1 @ sk_A @ sk_B)))),
% 1.02/1.21      inference('sup+', [status(thm)], ['40', '51'])).
% 1.02/1.21  thf('53', plain,
% 1.02/1.21      (((k1_tops_1 @ sk_A @ sk_B)
% 1.02/1.21         != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.02/1.21             (k2_tops_1 @ sk_A @ sk_B)))),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('54', plain, ($false),
% 1.02/1.21      inference('simplify_reflect-', [status(thm)], ['52', '53'])).
% 1.02/1.21  
% 1.02/1.21  % SZS output end Refutation
% 1.02/1.21  
% 1.02/1.22  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
