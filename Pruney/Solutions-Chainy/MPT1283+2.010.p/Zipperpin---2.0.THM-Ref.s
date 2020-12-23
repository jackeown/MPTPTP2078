%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.x7UyumAdBK

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:53 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 289 expanded)
%              Number of leaves         :   22 (  90 expanded)
%              Depth                    :   16
%              Number of atoms          :  852 (3570 expanded)
%              Number of equality atoms :   35 (  74 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v6_tops_1_type,type,(
    v6_tops_1: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_tops_1_type,type,(
    v5_tops_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(t105_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v3_pre_topc @ B @ A )
              & ( v4_pre_topc @ B @ A ) )
           => ( ( v5_tops_1 @ B @ A )
            <=> ( v6_tops_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( ( v3_pre_topc @ B @ A )
                & ( v4_pre_topc @ B @ A ) )
             => ( ( v5_tops_1 @ B @ A )
              <=> ( v6_tops_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t105_tops_1])).

thf('0',plain,
    ( ~ ( v6_tops_1 @ sk_B @ sk_A )
    | ~ ( v5_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v6_tops_1 @ sk_B @ sk_A )
   <= ~ ( v6_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( v6_tops_1 @ sk_B @ sk_A )
    | ~ ( v5_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( v6_tops_1 @ sk_B @ sk_A )
    | ( v5_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v6_tops_1 @ sk_B @ sk_A )
   <= ( v6_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v6_tops_1 @ B @ A )
          <=> ( B
              = ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v6_tops_1 @ X8 @ X9 )
      | ( X8
        = ( k1_tops_1 @ X9 @ ( k2_pre_topc @ X9 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d8_tops_1])).

thf('7',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( sk_B
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    | ~ ( v6_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
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

thf('10',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( v4_pre_topc @ X4 @ X5 )
      | ( ( k2_pre_topc @ X5 @ X4 )
        = X4 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('11',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,
    ( ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v6_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['7','8','14'])).

thf('16',plain,
    ( ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( v6_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','15'])).

thf('17',plain,(
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

thf('18',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( X6
       != ( k2_pre_topc @ X7 @ ( k1_tops_1 @ X7 @ X6 ) ) )
      | ( v5_tops_1 @ X6 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d7_tops_1])).

thf('19',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v5_tops_1 @ sk_B @ sk_A )
    | ( sk_B
     != ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v5_tops_1 @ sk_B @ sk_A )
    | ( sk_B
     != ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( sk_B
       != ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v5_tops_1 @ sk_B @ sk_A ) )
   <= ( v6_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('24',plain,
    ( ( ( sk_B != sk_B )
      | ( v5_tops_1 @ sk_B @ sk_A ) )
   <= ( v6_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( v5_tops_1 @ sk_B @ sk_A )
   <= ( v6_tops_1 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ~ ( v5_tops_1 @ sk_B @ sk_A )
   <= ~ ( v5_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('27',plain,
    ( ( v5_tops_1 @ sk_B @ sk_A )
    | ~ ( v6_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ~ ( v6_tops_1 @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','27'])).

thf('29',plain,(
    ~ ( v6_tops_1 @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t101_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v6_tops_1 @ B @ A )
          <=> ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('31',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X11 ) @ X10 ) @ X11 )
      | ( v6_tops_1 @ X10 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t101_tops_1])).

thf('32',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v6_tops_1 @ sk_B @ sk_A )
    | ~ ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v6_tops_1 @ sk_B @ sk_A )
    | ~ ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('37',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( X6
       != ( k2_pre_topc @ X7 @ ( k1_tops_1 @ X7 @ X6 ) ) )
      | ( v5_tops_1 @ X6 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d7_tops_1])).

thf('39',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
     != ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
     != ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( v5_tops_1 @ sk_B @ sk_A )
   <= ( v5_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('43',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('44',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X11 ) @ X10 ) @ X11 )
      | ( v6_tops_1 @ X10 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t101_tops_1])).

thf('45',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v6_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('48',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X3 @ ( k3_subset_1 @ X3 @ X2 ) )
        = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('49',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( v6_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v5_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['45','46','49'])).

thf('51',plain,
    ( ( v6_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v5_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['42','50'])).

thf('52',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('53',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v6_tops_1 @ X8 @ X9 )
      | ( X8
        = ( k1_tops_1 @ X9 @ ( k2_pre_topc @ X9 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d8_tops_1])).

thf('54',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) )
    | ~ ( v6_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('57',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( v4_pre_topc @ X4 @ X5 )
      | ( ( k2_pre_topc @ X5 @ X4 )
        = X4 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('58',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('62',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X13 ) @ X12 ) @ X13 )
      | ( v4_pre_topc @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('63',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['47','48'])).

thf('66',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['63','64','65','66'])).

thf('68',plain,
    ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['60','67'])).

thf('69',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( v6_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['54','55','68'])).

thf('70',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( v5_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['51','69'])).

thf('71',plain,
    ( ( v5_tops_1 @ sk_B @ sk_A )
    | ( v6_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('72',plain,(
    v5_tops_1 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','27','71'])).

thf('73',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['70','72'])).

thf('74',plain,
    ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['60','67'])).

thf('75',plain,
    ( ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
     != ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['41','73','74'])).

thf('76',plain,(
    v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    v6_tops_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['34','76'])).

thf('78',plain,(
    $false ),
    inference(demod,[status(thm)],['29','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.x7UyumAdBK
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:47:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 61 iterations in 0.028s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.48  thf(v6_tops_1_type, type, v6_tops_1: $i > $i > $o).
% 0.20/0.48  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(v5_tops_1_type, type, v5_tops_1: $i > $i > $o).
% 0.20/0.48  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.20/0.48  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.48  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.48  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.20/0.48  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.48  thf(t105_tops_1, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48           ( ( ( v3_pre_topc @ B @ A ) & ( v4_pre_topc @ B @ A ) ) =>
% 0.20/0.48             ( ( v5_tops_1 @ B @ A ) <=> ( v6_tops_1 @ B @ A ) ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( l1_pre_topc @ A ) =>
% 0.20/0.48          ( ![B:$i]:
% 0.20/0.48            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48              ( ( ( v3_pre_topc @ B @ A ) & ( v4_pre_topc @ B @ A ) ) =>
% 0.20/0.48                ( ( v5_tops_1 @ B @ A ) <=> ( v6_tops_1 @ B @ A ) ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t105_tops_1])).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      ((~ (v6_tops_1 @ sk_B @ sk_A) | ~ (v5_tops_1 @ sk_B @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      ((~ (v6_tops_1 @ sk_B @ sk_A)) <= (~ ((v6_tops_1 @ sk_B @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (~ ((v6_tops_1 @ sk_B @ sk_A)) | ~ ((v5_tops_1 @ sk_B @ sk_A))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('3', plain, (((v6_tops_1 @ sk_B @ sk_A) | (v5_tops_1 @ sk_B @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (((v6_tops_1 @ sk_B @ sk_A)) <= (((v6_tops_1 @ sk_B @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['3'])).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(d8_tops_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48           ( ( v6_tops_1 @ B @ A ) <=>
% 0.20/0.48             ( ( B ) = ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X8 : $i, X9 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.48          | ~ (v6_tops_1 @ X8 @ X9)
% 0.20/0.48          | ((X8) = (k1_tops_1 @ X9 @ (k2_pre_topc @ X9 @ X8)))
% 0.20/0.48          | ~ (l1_pre_topc @ X9))),
% 0.20/0.48      inference('cnf', [status(esa)], [d8_tops_1])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | ((sk_B) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 0.20/0.48        | ~ (v6_tops_1 @ sk_B @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.48  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t52_pre_topc, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.20/0.48             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.20/0.48               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (![X4 : $i, X5 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.20/0.48          | ~ (v4_pre_topc @ X4 @ X5)
% 0.20/0.48          | ((k2_pre_topc @ X5 @ X4) = (X4))
% 0.20/0.48          | ~ (l1_pre_topc @ X5))),
% 0.20/0.48      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.20/0.48        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.48  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('13', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('14', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      ((((sk_B) = (k1_tops_1 @ sk_A @ sk_B)) | ~ (v6_tops_1 @ sk_B @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['7', '8', '14'])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      ((((sk_B) = (k1_tops_1 @ sk_A @ sk_B))) <= (((v6_tops_1 @ sk_B @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['4', '15'])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(d7_tops_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48           ( ( v5_tops_1 @ B @ A ) <=>
% 0.20/0.48             ( ( B ) = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.48          | ((X6) != (k2_pre_topc @ X7 @ (k1_tops_1 @ X7 @ X6)))
% 0.20/0.48          | (v5_tops_1 @ X6 @ X7)
% 0.20/0.48          | ~ (l1_pre_topc @ X7))),
% 0.20/0.48      inference('cnf', [status(esa)], [d7_tops_1])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | (v5_tops_1 @ sk_B @ sk_A)
% 0.20/0.48        | ((sk_B) != (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.48  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (((v5_tops_1 @ sk_B @ sk_A)
% 0.20/0.48        | ((sk_B) != (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.20/0.48      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      (((((sk_B) != (k2_pre_topc @ sk_A @ sk_B)) | (v5_tops_1 @ sk_B @ sk_A)))
% 0.20/0.48         <= (((v6_tops_1 @ sk_B @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['16', '21'])).
% 0.20/0.48  thf('23', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      (((((sk_B) != (sk_B)) | (v5_tops_1 @ sk_B @ sk_A)))
% 0.20/0.48         <= (((v6_tops_1 @ sk_B @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      (((v5_tops_1 @ sk_B @ sk_A)) <= (((v6_tops_1 @ sk_B @ sk_A)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['24'])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      ((~ (v5_tops_1 @ sk_B @ sk_A)) <= (~ ((v5_tops_1 @ sk_B @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      (((v5_tops_1 @ sk_B @ sk_A)) | ~ ((v6_tops_1 @ sk_B @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.48  thf('28', plain, (~ ((v6_tops_1 @ sk_B @ sk_A))),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['2', '27'])).
% 0.20/0.48  thf('29', plain, (~ (v6_tops_1 @ sk_B @ sk_A)),
% 0.20/0.48      inference('simpl_trail', [status(thm)], ['1', '28'])).
% 0.20/0.48  thf('30', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t101_tops_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48           ( ( v6_tops_1 @ B @ A ) <=>
% 0.20/0.48             ( v5_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.20/0.48  thf('31', plain,
% 0.20/0.48      (![X10 : $i, X11 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.20/0.48          | ~ (v5_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X11) @ X10) @ X11)
% 0.20/0.48          | (v6_tops_1 @ X10 @ X11)
% 0.20/0.48          | ~ (l1_pre_topc @ X11))),
% 0.20/0.48      inference('cnf', [status(esa)], [t101_tops_1])).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | (v6_tops_1 @ sk_B @ sk_A)
% 0.20/0.48        | ~ (v5_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.48  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('34', plain,
% 0.20/0.48      (((v6_tops_1 @ sk_B @ sk_A)
% 0.20/0.48        | ~ (v5_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(dt_k3_subset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.48       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.48  thf('36', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((m1_subset_1 @ (k3_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 0.20/0.48          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.20/0.48  thf('37', plain,
% 0.20/0.48      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.48  thf('38', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.48          | ((X6) != (k2_pre_topc @ X7 @ (k1_tops_1 @ X7 @ X6)))
% 0.20/0.48          | (v5_tops_1 @ X6 @ X7)
% 0.20/0.48          | ~ (l1_pre_topc @ X7))),
% 0.20/0.48      inference('cnf', [status(esa)], [d7_tops_1])).
% 0.20/0.48  thf('39', plain,
% 0.20/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | (v5_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.20/0.48        | ((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.20/0.48            != (k2_pre_topc @ sk_A @ 
% 0.20/0.48                (k1_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.48  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('41', plain,
% 0.20/0.48      (((v5_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.20/0.48        | ((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.20/0.48            != (k2_pre_topc @ sk_A @ 
% 0.20/0.48                (k1_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.20/0.48      inference('demod', [status(thm)], ['39', '40'])).
% 0.20/0.48  thf('42', plain,
% 0.20/0.48      (((v5_tops_1 @ sk_B @ sk_A)) <= (((v5_tops_1 @ sk_B @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['3'])).
% 0.20/0.48  thf('43', plain,
% 0.20/0.48      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.48  thf('44', plain,
% 0.20/0.48      (![X10 : $i, X11 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.20/0.48          | ~ (v5_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X11) @ X10) @ X11)
% 0.20/0.48          | (v6_tops_1 @ X10 @ X11)
% 0.20/0.48          | ~ (l1_pre_topc @ X11))),
% 0.20/0.48      inference('cnf', [status(esa)], [t101_tops_1])).
% 0.20/0.48  thf('45', plain,
% 0.20/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | (v6_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.20/0.48        | ~ (v5_tops_1 @ 
% 0.20/0.48             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.48              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.20/0.48             sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.48  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('47', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(involutiveness_k3_subset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.48       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.20/0.48  thf('48', plain,
% 0.20/0.48      (![X2 : $i, X3 : $i]:
% 0.20/0.48         (((k3_subset_1 @ X3 @ (k3_subset_1 @ X3 @ X2)) = (X2))
% 0.20/0.48          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.20/0.48      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.20/0.48  thf('49', plain,
% 0.20/0.48      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.48         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.48  thf('50', plain,
% 0.20/0.48      (((v6_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.20/0.48        | ~ (v5_tops_1 @ sk_B @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['45', '46', '49'])).
% 0.20/0.48  thf('51', plain,
% 0.20/0.48      (((v6_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.20/0.48         <= (((v5_tops_1 @ sk_B @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['42', '50'])).
% 0.20/0.48  thf('52', plain,
% 0.20/0.48      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.48  thf('53', plain,
% 0.20/0.48      (![X8 : $i, X9 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.48          | ~ (v6_tops_1 @ X8 @ X9)
% 0.20/0.48          | ((X8) = (k1_tops_1 @ X9 @ (k2_pre_topc @ X9 @ X8)))
% 0.20/0.48          | ~ (l1_pre_topc @ X9))),
% 0.20/0.48      inference('cnf', [status(esa)], [d8_tops_1])).
% 0.20/0.48  thf('54', plain,
% 0.20/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | ((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.20/0.48            = (k1_tops_1 @ sk_A @ 
% 0.20/0.48               (k2_pre_topc @ sk_A @ 
% 0.20/0.48                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.20/0.48        | ~ (v6_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['52', '53'])).
% 0.20/0.48  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('56', plain,
% 0.20/0.48      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.48  thf('57', plain,
% 0.20/0.48      (![X4 : $i, X5 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.20/0.48          | ~ (v4_pre_topc @ X4 @ X5)
% 0.20/0.48          | ((k2_pre_topc @ X5 @ X4) = (X4))
% 0.20/0.48          | ~ (l1_pre_topc @ X5))),
% 0.20/0.48      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.20/0.48  thf('58', plain,
% 0.20/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.20/0.48            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.20/0.48        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['56', '57'])).
% 0.20/0.48  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('60', plain,
% 0.20/0.48      ((((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.20/0.48          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.20/0.48        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['58', '59'])).
% 0.20/0.48  thf('61', plain,
% 0.20/0.48      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.48  thf(t29_tops_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48           ( ( v4_pre_topc @ B @ A ) <=>
% 0.20/0.48             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.20/0.48  thf('62', plain,
% 0.20/0.48      (![X12 : $i, X13 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.20/0.48          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X13) @ X12) @ X13)
% 0.20/0.48          | (v4_pre_topc @ X12 @ X13)
% 0.20/0.48          | ~ (l1_pre_topc @ X13))),
% 0.20/0.48      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.20/0.48  thf('63', plain,
% 0.20/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.20/0.48        | ~ (v3_pre_topc @ 
% 0.20/0.48             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.48              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.20/0.48             sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['61', '62'])).
% 0.20/0.48  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('65', plain,
% 0.20/0.48      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.48         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.48  thf('66', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('67', plain,
% 0.20/0.48      ((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['63', '64', '65', '66'])).
% 0.20/0.48  thf('68', plain,
% 0.20/0.48      (((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.20/0.48         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['60', '67'])).
% 0.20/0.48  thf('69', plain,
% 0.20/0.48      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.20/0.48          = (k1_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.20/0.48        | ~ (v6_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['54', '55', '68'])).
% 0.20/0.48  thf('70', plain,
% 0.20/0.48      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.20/0.48          = (k1_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.20/0.48         <= (((v5_tops_1 @ sk_B @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['51', '69'])).
% 0.20/0.48  thf('71', plain, (((v5_tops_1 @ sk_B @ sk_A)) | ((v6_tops_1 @ sk_B @ sk_A))),
% 0.20/0.48      inference('split', [status(esa)], ['3'])).
% 0.20/0.48  thf('72', plain, (((v5_tops_1 @ sk_B @ sk_A))),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['2', '27', '71'])).
% 0.20/0.48  thf('73', plain,
% 0.20/0.48      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.20/0.48         = (k1_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.20/0.48      inference('simpl_trail', [status(thm)], ['70', '72'])).
% 0.20/0.48  thf('74', plain,
% 0.20/0.48      (((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.20/0.48         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['60', '67'])).
% 0.20/0.48  thf('75', plain,
% 0.20/0.48      (((v5_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.20/0.48        | ((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.20/0.48            != (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.20/0.48      inference('demod', [status(thm)], ['41', '73', '74'])).
% 0.20/0.48  thf('76', plain,
% 0.20/0.48      ((v5_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.20/0.48      inference('simplify', [status(thm)], ['75'])).
% 0.20/0.48  thf('77', plain, ((v6_tops_1 @ sk_B @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['34', '76'])).
% 0.20/0.48  thf('78', plain, ($false), inference('demod', [status(thm)], ['29', '77'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
