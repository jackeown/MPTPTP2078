%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ST5VOK5rmb

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:53 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 314 expanded)
%              Number of leaves         :   22 (  96 expanded)
%              Depth                    :   16
%              Number of atoms          :  903 (3921 expanded)
%              Number of equality atoms :   41 (  86 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v6_tops_1_type,type,(
    v6_tops_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v5_tops_1_type,type,(
    v5_tops_1: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

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
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( v4_pre_topc @ X2 @ X3 )
      | ( ( k2_pre_topc @ X3 @ X2 )
        = X2 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
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

thf('31',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( X8
       != ( k1_tops_1 @ X9 @ ( k2_pre_topc @ X9 @ X8 ) ) )
      | ( v6_tops_1 @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d8_tops_1])).

thf('32',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v6_tops_1 @ sk_B @ sk_A )
    | ( sk_B
     != ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('35',plain,
    ( ( v6_tops_1 @ sk_B @ sk_A )
    | ( sk_B
     != ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('38',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('40',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('42',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( ( k1_tops_1 @ X5 @ X4 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X5 ) @ ( k2_pre_topc @ X5 @ ( k3_subset_1 @ ( u1_struct_0 @ X5 ) @ X4 ) ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('43',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('47',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( v4_pre_topc @ X2 @ X3 )
      | ( ( k2_pre_topc @ X3 @ X2 )
        = X2 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('48',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t30_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('52',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v3_pre_topc @ X12 @ X13 )
      | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X13 ) @ X12 ) @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t30_tops_1])).

thf('53',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,
    ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['50','56'])).

thf('58',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','57'])).

thf('59',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','58'])).

thf('60',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( v4_pre_topc @ X2 @ X3 )
      | ( ( k2_pre_topc @ X3 @ X2 )
        = X2 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('61',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k1_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v4_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('64',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v3_pre_topc @ X12 @ X13 )
      | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X13 ) @ X12 ) @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t30_tops_1])).

thf('65',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('68',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v4_pre_topc @ X10 @ X11 )
      | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X11 ) @ X10 ) @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('69',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['65','66','72'])).

thf('74',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','57'])).

thf('75',plain,(
    v4_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['61','62','75'])).

thf('77',plain,
    ( ( v5_tops_1 @ sk_B @ sk_A )
   <= ( v5_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('78',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( v5_tops_1 @ X6 @ X7 )
      | ( X6
        = ( k2_pre_topc @ X7 @ ( k1_tops_1 @ X7 @ X6 ) ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d7_tops_1])).

thf('80',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( sk_B
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v5_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( sk_B
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v5_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( sk_B
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v5_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['77','82'])).

thf('84',plain,
    ( ( v5_tops_1 @ sk_B @ sk_A )
    | ( v6_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('85',plain,(
    v5_tops_1 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','27','84'])).

thf('86',plain,
    ( sk_B
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['83','85'])).

thf('87',plain,
    ( sk_B
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['76','86'])).

thf('88',plain,
    ( ( v6_tops_1 @ sk_B @ sk_A )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['35','87'])).

thf('89',plain,(
    v6_tops_1 @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    $false ),
    inference(demod,[status(thm)],['29','89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ST5VOK5rmb
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:31:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.51  % Solved by: fo/fo7.sh
% 0.22/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.51  % done 69 iterations in 0.045s
% 0.22/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.51  % SZS output start Refutation
% 0.22/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.51  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.22/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.51  thf(v6_tops_1_type, type, v6_tops_1: $i > $i > $o).
% 0.22/0.51  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.22/0.51  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.22/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.51  thf(v5_tops_1_type, type, v5_tops_1: $i > $i > $o).
% 0.22/0.51  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.22/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.51  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.22/0.51  thf(t105_tops_1, conjecture,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( l1_pre_topc @ A ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.51           ( ( ( v3_pre_topc @ B @ A ) & ( v4_pre_topc @ B @ A ) ) =>
% 0.22/0.51             ( ( v5_tops_1 @ B @ A ) <=> ( v6_tops_1 @ B @ A ) ) ) ) ) ))).
% 0.22/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.51    (~( ![A:$i]:
% 0.22/0.51        ( ( l1_pre_topc @ A ) =>
% 0.22/0.51          ( ![B:$i]:
% 0.22/0.51            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.51              ( ( ( v3_pre_topc @ B @ A ) & ( v4_pre_topc @ B @ A ) ) =>
% 0.22/0.51                ( ( v5_tops_1 @ B @ A ) <=> ( v6_tops_1 @ B @ A ) ) ) ) ) ) )),
% 0.22/0.51    inference('cnf.neg', [status(esa)], [t105_tops_1])).
% 0.22/0.51  thf('0', plain,
% 0.22/0.51      ((~ (v6_tops_1 @ sk_B @ sk_A) | ~ (v5_tops_1 @ sk_B @ sk_A))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('1', plain,
% 0.22/0.51      ((~ (v6_tops_1 @ sk_B @ sk_A)) <= (~ ((v6_tops_1 @ sk_B @ sk_A)))),
% 0.22/0.51      inference('split', [status(esa)], ['0'])).
% 0.22/0.51  thf('2', plain,
% 0.22/0.51      (~ ((v6_tops_1 @ sk_B @ sk_A)) | ~ ((v5_tops_1 @ sk_B @ sk_A))),
% 0.22/0.51      inference('split', [status(esa)], ['0'])).
% 0.22/0.51  thf('3', plain, (((v6_tops_1 @ sk_B @ sk_A) | (v5_tops_1 @ sk_B @ sk_A))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('4', plain,
% 0.22/0.51      (((v6_tops_1 @ sk_B @ sk_A)) <= (((v6_tops_1 @ sk_B @ sk_A)))),
% 0.22/0.51      inference('split', [status(esa)], ['3'])).
% 0.22/0.51  thf('5', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(d8_tops_1, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( l1_pre_topc @ A ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.51           ( ( v6_tops_1 @ B @ A ) <=>
% 0.22/0.51             ( ( B ) = ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) ) ) ) ) ))).
% 0.22/0.51  thf('6', plain,
% 0.22/0.51      (![X8 : $i, X9 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.22/0.51          | ~ (v6_tops_1 @ X8 @ X9)
% 0.22/0.51          | ((X8) = (k1_tops_1 @ X9 @ (k2_pre_topc @ X9 @ X8)))
% 0.22/0.51          | ~ (l1_pre_topc @ X9))),
% 0.22/0.51      inference('cnf', [status(esa)], [d8_tops_1])).
% 0.22/0.51  thf('7', plain,
% 0.22/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.51        | ((sk_B) = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 0.22/0.51        | ~ (v6_tops_1 @ sk_B @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.51  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('9', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(t52_pre_topc, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( l1_pre_topc @ A ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.51           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.22/0.51             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.22/0.51               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.22/0.51  thf('10', plain,
% 0.22/0.51      (![X2 : $i, X3 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.22/0.51          | ~ (v4_pre_topc @ X2 @ X3)
% 0.22/0.51          | ((k2_pre_topc @ X3 @ X2) = (X2))
% 0.22/0.51          | ~ (l1_pre_topc @ X3))),
% 0.22/0.51      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.22/0.51  thf('11', plain,
% 0.22/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.51        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.22/0.51        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.51  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('13', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('14', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.22/0.51      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.22/0.51  thf('15', plain,
% 0.22/0.51      ((((sk_B) = (k1_tops_1 @ sk_A @ sk_B)) | ~ (v6_tops_1 @ sk_B @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)], ['7', '8', '14'])).
% 0.22/0.51  thf('16', plain,
% 0.22/0.51      ((((sk_B) = (k1_tops_1 @ sk_A @ sk_B))) <= (((v6_tops_1 @ sk_B @ sk_A)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['4', '15'])).
% 0.22/0.51  thf('17', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(d7_tops_1, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( l1_pre_topc @ A ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.51           ( ( v5_tops_1 @ B @ A ) <=>
% 0.22/0.51             ( ( B ) = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.22/0.51  thf('18', plain,
% 0.22/0.51      (![X6 : $i, X7 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.22/0.51          | ((X6) != (k2_pre_topc @ X7 @ (k1_tops_1 @ X7 @ X6)))
% 0.22/0.51          | (v5_tops_1 @ X6 @ X7)
% 0.22/0.51          | ~ (l1_pre_topc @ X7))),
% 0.22/0.51      inference('cnf', [status(esa)], [d7_tops_1])).
% 0.22/0.51  thf('19', plain,
% 0.22/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.51        | (v5_tops_1 @ sk_B @ sk_A)
% 0.22/0.51        | ((sk_B) != (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.51  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('21', plain,
% 0.22/0.51      (((v5_tops_1 @ sk_B @ sk_A)
% 0.22/0.51        | ((sk_B) != (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.22/0.51      inference('demod', [status(thm)], ['19', '20'])).
% 0.22/0.51  thf('22', plain,
% 0.22/0.51      (((((sk_B) != (k2_pre_topc @ sk_A @ sk_B)) | (v5_tops_1 @ sk_B @ sk_A)))
% 0.22/0.51         <= (((v6_tops_1 @ sk_B @ sk_A)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['16', '21'])).
% 0.22/0.51  thf('23', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.22/0.51      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.22/0.51  thf('24', plain,
% 0.22/0.51      (((((sk_B) != (sk_B)) | (v5_tops_1 @ sk_B @ sk_A)))
% 0.22/0.51         <= (((v6_tops_1 @ sk_B @ sk_A)))),
% 0.22/0.51      inference('demod', [status(thm)], ['22', '23'])).
% 0.22/0.51  thf('25', plain,
% 0.22/0.51      (((v5_tops_1 @ sk_B @ sk_A)) <= (((v6_tops_1 @ sk_B @ sk_A)))),
% 0.22/0.51      inference('simplify', [status(thm)], ['24'])).
% 0.22/0.51  thf('26', plain,
% 0.22/0.51      ((~ (v5_tops_1 @ sk_B @ sk_A)) <= (~ ((v5_tops_1 @ sk_B @ sk_A)))),
% 0.22/0.51      inference('split', [status(esa)], ['0'])).
% 0.22/0.51  thf('27', plain,
% 0.22/0.51      (((v5_tops_1 @ sk_B @ sk_A)) | ~ ((v6_tops_1 @ sk_B @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['25', '26'])).
% 0.22/0.51  thf('28', plain, (~ ((v6_tops_1 @ sk_B @ sk_A))),
% 0.22/0.51      inference('sat_resolution*', [status(thm)], ['2', '27'])).
% 0.22/0.51  thf('29', plain, (~ (v6_tops_1 @ sk_B @ sk_A)),
% 0.22/0.51      inference('simpl_trail', [status(thm)], ['1', '28'])).
% 0.22/0.51  thf('30', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('31', plain,
% 0.22/0.51      (![X8 : $i, X9 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.22/0.51          | ((X8) != (k1_tops_1 @ X9 @ (k2_pre_topc @ X9 @ X8)))
% 0.22/0.51          | (v6_tops_1 @ X8 @ X9)
% 0.22/0.51          | ~ (l1_pre_topc @ X9))),
% 0.22/0.51      inference('cnf', [status(esa)], [d8_tops_1])).
% 0.22/0.51  thf('32', plain,
% 0.22/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.51        | (v6_tops_1 @ sk_B @ sk_A)
% 0.22/0.51        | ((sk_B) != (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['30', '31'])).
% 0.22/0.51  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('34', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.22/0.51      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.22/0.51  thf('35', plain,
% 0.22/0.51      (((v6_tops_1 @ sk_B @ sk_A) | ((sk_B) != (k1_tops_1 @ sk_A @ sk_B)))),
% 0.22/0.51      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.22/0.51  thf('36', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(dt_k3_subset_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.51       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.51  thf('37', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         ((m1_subset_1 @ (k3_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 0.22/0.51          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.22/0.51  thf('38', plain,
% 0.22/0.51      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['36', '37'])).
% 0.22/0.51  thf('39', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         ((m1_subset_1 @ (k3_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 0.22/0.51          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.22/0.51  thf('40', plain,
% 0.22/0.51      ((m1_subset_1 @ 
% 0.22/0.51        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.51         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.22/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['38', '39'])).
% 0.22/0.51  thf('41', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(d1_tops_1, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( l1_pre_topc @ A ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.51           ( ( k1_tops_1 @ A @ B ) =
% 0.22/0.51             ( k3_subset_1 @
% 0.22/0.51               ( u1_struct_0 @ A ) @ 
% 0.22/0.51               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.22/0.51  thf('42', plain,
% 0.22/0.51      (![X4 : $i, X5 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.22/0.51          | ((k1_tops_1 @ X5 @ X4)
% 0.22/0.51              = (k3_subset_1 @ (u1_struct_0 @ X5) @ 
% 0.22/0.51                 (k2_pre_topc @ X5 @ (k3_subset_1 @ (u1_struct_0 @ X5) @ X4))))
% 0.22/0.51          | ~ (l1_pre_topc @ X5))),
% 0.22/0.51      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.22/0.51  thf('43', plain,
% 0.22/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.51        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.22/0.51            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.51               (k2_pre_topc @ sk_A @ 
% 0.22/0.51                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['41', '42'])).
% 0.22/0.51  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('45', plain,
% 0.22/0.51      (((k1_tops_1 @ sk_A @ sk_B)
% 0.22/0.51         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.51            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.22/0.51      inference('demod', [status(thm)], ['43', '44'])).
% 0.22/0.51  thf('46', plain,
% 0.22/0.51      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['36', '37'])).
% 0.22/0.51  thf('47', plain,
% 0.22/0.51      (![X2 : $i, X3 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.22/0.51          | ~ (v4_pre_topc @ X2 @ X3)
% 0.22/0.51          | ((k2_pre_topc @ X3 @ X2) = (X2))
% 0.22/0.51          | ~ (l1_pre_topc @ X3))),
% 0.22/0.51      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.22/0.51  thf('48', plain,
% 0.22/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.51        | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.22/0.51            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.22/0.51        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['46', '47'])).
% 0.22/0.51  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('50', plain,
% 0.22/0.51      ((((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.22/0.51          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.22/0.51        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)], ['48', '49'])).
% 0.22/0.51  thf('51', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(t30_tops_1, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( l1_pre_topc @ A ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.51           ( ( v3_pre_topc @ B @ A ) <=>
% 0.22/0.51             ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.22/0.51  thf('52', plain,
% 0.22/0.51      (![X12 : $i, X13 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.22/0.51          | ~ (v3_pre_topc @ X12 @ X13)
% 0.22/0.51          | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X13) @ X12) @ X13)
% 0.22/0.51          | ~ (l1_pre_topc @ X13))),
% 0.22/0.51      inference('cnf', [status(esa)], [t30_tops_1])).
% 0.22/0.51  thf('53', plain,
% 0.22/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.51        | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.22/0.51        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['51', '52'])).
% 0.22/0.51  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('55', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('56', plain,
% 0.22/0.51      ((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.22/0.51      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.22/0.51  thf('57', plain,
% 0.22/0.51      (((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.22/0.51         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.22/0.51      inference('demod', [status(thm)], ['50', '56'])).
% 0.22/0.51  thf('58', plain,
% 0.22/0.51      (((k1_tops_1 @ sk_A @ sk_B)
% 0.22/0.51         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.51            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.22/0.51      inference('demod', [status(thm)], ['45', '57'])).
% 0.22/0.51  thf('59', plain,
% 0.22/0.51      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.22/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('demod', [status(thm)], ['40', '58'])).
% 0.22/0.51  thf('60', plain,
% 0.22/0.51      (![X2 : $i, X3 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.22/0.51          | ~ (v4_pre_topc @ X2 @ X3)
% 0.22/0.51          | ((k2_pre_topc @ X3 @ X2) = (X2))
% 0.22/0.51          | ~ (l1_pre_topc @ X3))),
% 0.22/0.51      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.22/0.51  thf('61', plain,
% 0.22/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.51        | ((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.22/0.51            = (k1_tops_1 @ sk_A @ sk_B))
% 0.22/0.51        | ~ (v4_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['59', '60'])).
% 0.22/0.51  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('63', plain,
% 0.22/0.51      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['36', '37'])).
% 0.22/0.51  thf('64', plain,
% 0.22/0.51      (![X12 : $i, X13 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.22/0.51          | ~ (v3_pre_topc @ X12 @ X13)
% 0.22/0.51          | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X13) @ X12) @ X13)
% 0.22/0.51          | ~ (l1_pre_topc @ X13))),
% 0.22/0.51      inference('cnf', [status(esa)], [t30_tops_1])).
% 0.22/0.51  thf('65', plain,
% 0.22/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.51        | (v4_pre_topc @ 
% 0.22/0.51           (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.51            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.22/0.51           sk_A)
% 0.22/0.51        | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['63', '64'])).
% 0.22/0.51  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('67', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(t29_tops_1, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( l1_pre_topc @ A ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.51           ( ( v4_pre_topc @ B @ A ) <=>
% 0.22/0.51             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.22/0.51  thf('68', plain,
% 0.22/0.51      (![X10 : $i, X11 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.22/0.51          | ~ (v4_pre_topc @ X10 @ X11)
% 0.22/0.51          | (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X11) @ X10) @ X11)
% 0.22/0.51          | ~ (l1_pre_topc @ X11))),
% 0.22/0.51      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.22/0.51  thf('69', plain,
% 0.22/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.51        | (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.22/0.51        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['67', '68'])).
% 0.22/0.51  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('71', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('72', plain,
% 0.22/0.51      ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.22/0.51      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.22/0.51  thf('73', plain,
% 0.22/0.51      ((v4_pre_topc @ 
% 0.22/0.51        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.51         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.22/0.51        sk_A)),
% 0.22/0.51      inference('demod', [status(thm)], ['65', '66', '72'])).
% 0.22/0.51  thf('74', plain,
% 0.22/0.51      (((k1_tops_1 @ sk_A @ sk_B)
% 0.22/0.51         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.51            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.22/0.51      inference('demod', [status(thm)], ['45', '57'])).
% 0.22/0.51  thf('75', plain, ((v4_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 0.22/0.51      inference('demod', [status(thm)], ['73', '74'])).
% 0.22/0.51  thf('76', plain,
% 0.22/0.51      (((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.22/0.51         = (k1_tops_1 @ sk_A @ sk_B))),
% 0.22/0.51      inference('demod', [status(thm)], ['61', '62', '75'])).
% 0.22/0.51  thf('77', plain,
% 0.22/0.51      (((v5_tops_1 @ sk_B @ sk_A)) <= (((v5_tops_1 @ sk_B @ sk_A)))),
% 0.22/0.51      inference('split', [status(esa)], ['3'])).
% 0.22/0.51  thf('78', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('79', plain,
% 0.22/0.51      (![X6 : $i, X7 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.22/0.51          | ~ (v5_tops_1 @ X6 @ X7)
% 0.22/0.51          | ((X6) = (k2_pre_topc @ X7 @ (k1_tops_1 @ X7 @ X6)))
% 0.22/0.51          | ~ (l1_pre_topc @ X7))),
% 0.22/0.51      inference('cnf', [status(esa)], [d7_tops_1])).
% 0.22/0.51  thf('80', plain,
% 0.22/0.51      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.51        | ((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.22/0.51        | ~ (v5_tops_1 @ sk_B @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['78', '79'])).
% 0.22/0.51  thf('81', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('82', plain,
% 0.22/0.51      ((((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.22/0.51        | ~ (v5_tops_1 @ sk_B @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)], ['80', '81'])).
% 0.22/0.51  thf('83', plain,
% 0.22/0.51      ((((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.22/0.51         <= (((v5_tops_1 @ sk_B @ sk_A)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['77', '82'])).
% 0.22/0.51  thf('84', plain, (((v5_tops_1 @ sk_B @ sk_A)) | ((v6_tops_1 @ sk_B @ sk_A))),
% 0.22/0.51      inference('split', [status(esa)], ['3'])).
% 0.22/0.51  thf('85', plain, (((v5_tops_1 @ sk_B @ sk_A))),
% 0.22/0.51      inference('sat_resolution*', [status(thm)], ['2', '27', '84'])).
% 0.22/0.51  thf('86', plain,
% 0.22/0.51      (((sk_B) = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.22/0.51      inference('simpl_trail', [status(thm)], ['83', '85'])).
% 0.22/0.51  thf('87', plain, (((sk_B) = (k1_tops_1 @ sk_A @ sk_B))),
% 0.22/0.51      inference('sup+', [status(thm)], ['76', '86'])).
% 0.22/0.51  thf('88', plain, (((v6_tops_1 @ sk_B @ sk_A) | ((sk_B) != (sk_B)))),
% 0.22/0.51      inference('demod', [status(thm)], ['35', '87'])).
% 0.22/0.51  thf('89', plain, ((v6_tops_1 @ sk_B @ sk_A)),
% 0.22/0.51      inference('simplify', [status(thm)], ['88'])).
% 0.22/0.51  thf('90', plain, ($false), inference('demod', [status(thm)], ['29', '89'])).
% 0.22/0.51  
% 0.22/0.51  % SZS output end Refutation
% 0.22/0.51  
% 0.22/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
