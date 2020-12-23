%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yiYZSxahZ9

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:57 EST 2020

% Result     : Theorem 7.51s
% Output     : Refutation 7.51s
% Verified   : 
% Statistics : Number of formulae       :  303 (1695 expanded)
%              Number of leaves         :   44 ( 501 expanded)
%              Depth                    :   18
%              Number of atoms          : 3346 (22327 expanded)
%              Number of equality atoms :  118 ( 864 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v5_tops_1_type,type,(
    v5_tops_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v4_tops_1_type,type,(
    v4_tops_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t110_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_tops_1 @ B @ A )
           => ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ B ) )
              = k1_xboole_0 ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_tops_1 @ B @ A )
             => ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ B ) )
                = k1_xboole_0 ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t110_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_pre_topc @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X29 @ X30 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('2',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( l1_pre_topc @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X31 @ X32 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('6',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('9',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X43 @ X42 ) @ X42 )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('14',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X8 @ X9 ) @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('15',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_subset_1 @ X6 @ X7 )
        = ( k4_xboole_0 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('18',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('20',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('21',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t69_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf('24',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X52 @ X51 ) @ X51 )
      | ~ ( v4_pre_topc @ X51 @ X52 )
      | ~ ( l1_pre_topc @ X52 ) ) ),
    inference(cnf,[status(esa)],[t69_tops_1])).

thf('25',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('28',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X33 @ X34 ) @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('29',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t62_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k2_tops_1 @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) )).

thf('34',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) )
      | ( ( k2_tops_1 @ X50 @ X49 )
        = ( k2_tops_1 @ X50 @ ( k3_subset_1 @ ( u1_struct_0 @ X50 ) @ X49 ) ) )
      | ~ ( l1_pre_topc @ X50 ) ) ),
    inference(cnf,[status(esa)],[t62_tops_1])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('38',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( ( k1_tops_1 @ X22 @ X21 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X22 ) @ ( k2_pre_topc @ X22 @ ( k3_subset_1 @ ( u1_struct_0 @ X22 ) @ X21 ) ) ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('39',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('42',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    = ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['35','36','42'])).

thf('44',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['25','26','32','43'])).

thf('45',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('46',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ~ ( r1_tarski @ X44 @ X46 )
      | ( r1_tarski @ ( k1_tops_1 @ X45 @ X44 ) @ ( k1_tops_1 @ X45 @ X46 ) )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) )
    | ~ ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['44','49'])).

thf('51',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('52',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X8 @ X9 ) @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('53',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('55',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_subset_1 @ X6 @ X7 )
        = ( k4_xboole_0 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('56',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( ( k1_tops_1 @ X22 @ X21 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X22 ) @ ( k2_pre_topc @ X22 @ ( k3_subset_1 @ ( u1_struct_0 @ X22 ) @ X21 ) ) ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('59',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('62',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X11 @ ( k3_subset_1 @ X11 @ X10 ) )
        = X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('63',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('65',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('67',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('68',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_subset_1 @ X6 @ X7 )
        = ( k4_xboole_0 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('72',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['59','60','65','72'])).

thf('74',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('75',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X11 @ ( k3_subset_1 @ X11 @ X10 ) )
        = X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('76',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) )
    = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('78',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('80',plain,
    ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['73','80'])).

thf('82',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('83',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t49_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) )).

thf('84',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( r1_tarski @ X18 @ X20 )
      | ( r1_tarski @ ( k2_pre_topc @ X19 @ X18 ) @ ( k2_pre_topc @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t49_pre_topc])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['82','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_tops_1 @ B @ A )
          <=> ( ( r1_tarski @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ B )
              & ( r1_tarski @ B @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )).

thf('90',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v4_tops_1 @ X25 @ X26 )
      | ( r1_tarski @ X25 @ ( k2_pre_topc @ X26 @ ( k1_tops_1 @ X26 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('91',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v4_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(projectivity_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) )
        = ( k2_pre_topc @ A @ B ) ) ) )).

thf('96',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( ( k2_pre_topc @ X14 @ ( k2_pre_topc @ X14 @ X15 ) )
        = ( k2_pre_topc @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k2_pre_topc])).

thf('97',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['88','94','99'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('101',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('102',plain,
    ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('105',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( r1_tarski @ X18 @ X20 )
      | ( r1_tarski @ ( k2_pre_topc @ X19 @ X18 ) @ ( k2_pre_topc @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t49_pre_topc])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
    | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['103','108'])).

thf('110',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X43 @ X42 ) @ X42 )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('112',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['109','114'])).

thf('116',plain,
    ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['102','115'])).

thf('117',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['81','116'])).

thf('118',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('119',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['50','117','118'])).

thf(t67_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ B @ C ) )
     => ( A = k1_xboole_0 ) ) )).

thf('120',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X3 @ X5 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t67_xboole_1])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ X0 )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) @ X0 )
      | ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      = k1_xboole_0 )
    | ~ ( r1_xboole_0 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['12','121'])).

thf('123',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','56'])).

thf(t73_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_xboole_0 @ ( k1_tops_1 @ A @ B ) @ ( k2_tops_1 @ A @ B ) ) ) ) )).

thf('124',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X54 ) ) )
      | ( r1_xboole_0 @ ( k1_tops_1 @ X54 @ X53 ) @ ( k2_tops_1 @ X54 @ X53 ) )
      | ~ ( l1_pre_topc @ X54 ) ) ),
    inference(cnf,[status(esa)],[t73_tops_1])).

thf('125',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) @ ( k2_tops_1 @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['59','60','65','72'])).

thf('128',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','56'])).

thf('129',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) )
      | ( ( k2_tops_1 @ X50 @ X49 )
        = ( k2_tops_1 @ X50 @ ( k3_subset_1 @ ( u1_struct_0 @ X50 ) @ X49 ) ) )
      | ~ ( l1_pre_topc @ X50 ) ) ),
    inference(cnf,[status(esa)],[t62_tops_1])).

thf('130',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('133',plain,
    ( ( k2_tops_1 @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['130','131','132'])).

thf('134',plain,(
    r1_xboole_0 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['125','126','127','133'])).

thf('135',plain,
    ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['102','115'])).

thf('136',plain,(
    r1_xboole_0 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['122','136'])).

thf('138',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('140',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['140','141'])).

thf(t102_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v5_tops_1 @ B @ A )
           => ( ( k2_tops_1 @ A @ ( k1_tops_1 @ A @ B ) )
              = ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('143',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ( ( k2_tops_1 @ X38 @ ( k1_tops_1 @ X38 @ X37 ) )
        = ( k2_tops_1 @ X38 @ X37 ) )
      | ~ ( v5_tops_1 @ X37 @ X38 )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t102_tops_1])).

thf('144',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v5_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ~ ( v5_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf(d7_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v5_tops_1 @ B @ A )
          <=> ( B
              = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) )).

thf('148',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( X27
       != ( k2_pre_topc @ X28 @ ( k1_tops_1 @ X28 @ X27 ) ) )
      | ( v5_tops_1 @ X27 @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[d7_tops_1])).

thf('149',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v5_tops_1 @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
     != ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ( v5_tops_1 @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
     != ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t58_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) )
            = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )).

thf('153',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) )
      | ( ( k2_pre_topc @ X48 @ ( k1_tops_1 @ X48 @ X47 ) )
        = ( k2_pre_topc @ X48 @ ( k1_tops_1 @ X48 @ ( k2_pre_topc @ X48 @ ( k1_tops_1 @ X48 @ X47 ) ) ) ) )
      | ~ ( l1_pre_topc @ X48 ) ) ),
    inference(cnf,[status(esa)],[t58_tops_1])).

thf('154',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(projectivity_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) )
        = ( k1_tops_1 @ A @ B ) ) ) )).

thf('157',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( l1_pre_topc @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( ( k1_tops_1 @ X35 @ ( k1_tops_1 @ X35 @ X36 ) )
        = ( k1_tops_1 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k1_tops_1])).

thf('158',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k1_tops_1 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['158','159'])).

thf('161',plain,
    ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['158','159'])).

thf('162',plain,
    ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['154','155','160','161'])).

thf('163',plain,
    ( ( v5_tops_1 @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
     != ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['151','162'])).

thf('164',plain,(
    v5_tops_1 @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A ),
    inference(simplify,[status(thm)],['163'])).

thf('165',plain,
    ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['102','115'])).

thf('166',plain,(
    v5_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,
    ( ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    = ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['146','166'])).

thf('168',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('169',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ~ ( r1_tarski @ X44 @ X46 )
      | ( r1_tarski @ ( k1_tops_1 @ X45 @ X44 ) @ ( k1_tops_1 @ X45 @ X46 ) )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('171',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['171','172'])).

thf('174',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['168','173'])).

thf('175',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('176',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( r1_tarski @ X16 @ ( k2_pre_topc @ X17 @ X16 ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('177',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['177','178'])).

thf('180',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['174','179'])).

thf('181',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('182',plain,
    ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
      = ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v4_tops_1 @ X25 @ X26 )
      | ( r1_tarski @ ( k1_tops_1 @ X26 @ ( k2_pre_topc @ X26 @ X25 ) ) @ X25 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('185',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B )
    | ~ ( v4_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    v4_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B ),
    inference(demod,[status(thm)],['185','186','187'])).

thf('189',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('190',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_pre_topc @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X29 @ X30 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('191',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['191','192'])).

thf('194',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ~ ( r1_tarski @ X44 @ X46 )
      | ( r1_tarski @ ( k1_tops_1 @ X45 @ X44 ) @ ( k1_tops_1 @ X45 @ X46 ) )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('195',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('198',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( l1_pre_topc @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( ( k1_tops_1 @ X35 @ ( k1_tops_1 @ X35 @ X36 ) )
        = ( k1_tops_1 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k1_tops_1])).

thf('199',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
      = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['197','198'])).

thf('200',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,
    ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    = ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['199','200'])).

thf('202',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['195','196','201'])).

thf('203',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['188','202'])).

thf('204',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['203','204'])).

thf('206',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['182','205'])).

thf('207',plain,
    ( ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['167','206'])).

thf('208',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['137','207'])).

thf('209',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','56'])).

thf(d2_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('210',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( ( k2_tops_1 @ X24 @ X23 )
        = ( k9_subset_1 @ ( u1_struct_0 @ X24 ) @ ( k2_pre_topc @ X24 @ X23 ) @ ( k2_pre_topc @ X24 @ ( k3_subset_1 @ ( u1_struct_0 @ X24 ) @ X23 ) ) ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_1])).

thf('211',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['209','210'])).

thf('212',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('214',plain,
    ( ( k2_tops_1 @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['211','212','213'])).

thf('215',plain,
    ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('216',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['191','192'])).

thf('217',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) )
      | ( ( k2_tops_1 @ X50 @ X49 )
        = ( k2_tops_1 @ X50 @ ( k3_subset_1 @ ( u1_struct_0 @ X50 ) @ X49 ) ) )
      | ~ ( l1_pre_topc @ X50 ) ) ),
    inference(cnf,[status(esa)],[t62_tops_1])).

thf('218',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['216','217'])).

thf('219',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['191','192'])).

thf('221',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_subset_1 @ X6 @ X7 )
        = ( k4_xboole_0 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('222',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['220','221'])).

thf('223',plain,
    ( ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    = ( k2_tops_1 @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['218','219','222'])).

thf('224',plain,
    ( ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    = ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['146','166'])).

thf('225',plain,
    ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['223','224'])).

thf('226',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['182','205'])).

thf('227',plain,
    ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('228',plain,
    ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['225','226','227'])).

thf('229',plain,
    ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('230',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('231',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( ( k2_pre_topc @ X14 @ ( k2_pre_topc @ X14 @ X15 ) )
        = ( k2_pre_topc @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k2_pre_topc])).

thf('232',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['230','231'])).

thf('233',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['232','233'])).

thf('235',plain,
    ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['102','115'])).

thf('236',plain,
    ( ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['214','215','228','229','234','235'])).

thf('237',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('238',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( ( k2_tops_1 @ X24 @ X23 )
        = ( k9_subset_1 @ ( u1_struct_0 @ X24 ) @ ( k2_pre_topc @ X24 @ X23 ) @ ( k2_pre_topc @ X24 @ ( k3_subset_1 @ ( u1_struct_0 @ X24 ) @ X23 ) ) ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_1])).

thf('239',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['237','238'])).

thf('240',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X11 @ ( k3_subset_1 @ X11 @ X10 ) )
        = X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('243',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['241','242'])).

thf('244',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('245',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['243','244'])).

thf('246',plain,
    ( ( k2_tops_1 @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['239','240','245'])).

thf('247',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('248',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) )
      | ( ( k2_tops_1 @ X50 @ X49 )
        = ( k2_tops_1 @ X50 @ ( k3_subset_1 @ ( u1_struct_0 @ X50 ) @ X49 ) ) )
      | ~ ( l1_pre_topc @ X50 ) ) ),
    inference(cnf,[status(esa)],[t62_tops_1])).

thf('249',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['247','248'])).

thf('250',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('251',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['243','244'])).

thf('252',plain,
    ( ( k2_tops_1 @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['249','250','251'])).

thf('253',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['246','252'])).

thf('254',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k2_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['236','253'])).

thf('255',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['208','254'])).

thf('256',plain,(
    ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('257',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['255','256'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yiYZSxahZ9
% 0.16/0.37  % Computer   : n010.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 13:35:45 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 7.51/7.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 7.51/7.72  % Solved by: fo/fo7.sh
% 7.51/7.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.51/7.72  % done 5237 iterations in 7.228s
% 7.51/7.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 7.51/7.72  % SZS output start Refutation
% 7.51/7.72  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 7.51/7.72  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 7.51/7.72  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 7.51/7.72  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 7.51/7.72  thf(v5_tops_1_type, type, v5_tops_1: $i > $i > $o).
% 7.51/7.72  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 7.51/7.72  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 7.51/7.72  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 7.51/7.72  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 7.51/7.72  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 7.51/7.72  thf(v4_tops_1_type, type, v4_tops_1: $i > $i > $o).
% 7.51/7.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 7.51/7.72  thf(sk_B_type, type, sk_B: $i).
% 7.51/7.72  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 7.51/7.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 7.51/7.72  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 7.51/7.72  thf(sk_A_type, type, sk_A: $i).
% 7.51/7.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 7.51/7.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 7.51/7.72  thf(t110_tops_1, conjecture,
% 7.51/7.72    (![A:$i]:
% 7.51/7.72     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 7.51/7.72       ( ![B:$i]:
% 7.51/7.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.51/7.72           ( ( v4_tops_1 @ B @ A ) =>
% 7.51/7.72             ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 7.51/7.72  thf(zf_stmt_0, negated_conjecture,
% 7.51/7.72    (~( ![A:$i]:
% 7.51/7.72        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 7.51/7.72          ( ![B:$i]:
% 7.51/7.72            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.51/7.72              ( ( v4_tops_1 @ B @ A ) =>
% 7.51/7.72                ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 7.51/7.72    inference('cnf.neg', [status(esa)], [t110_tops_1])).
% 7.51/7.72  thf('0', plain,
% 7.51/7.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.51/7.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.72  thf(dt_k1_tops_1, axiom,
% 7.51/7.72    (![A:$i,B:$i]:
% 7.51/7.72     ( ( ( l1_pre_topc @ A ) & 
% 7.51/7.72         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 7.51/7.72       ( m1_subset_1 @
% 7.51/7.72         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 7.51/7.72  thf('1', plain,
% 7.51/7.72      (![X29 : $i, X30 : $i]:
% 7.51/7.72         (~ (l1_pre_topc @ X29)
% 7.51/7.72          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 7.51/7.72          | (m1_subset_1 @ (k1_tops_1 @ X29 @ X30) @ 
% 7.51/7.72             (k1_zfmisc_1 @ (u1_struct_0 @ X29))))),
% 7.51/7.72      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 7.51/7.72  thf('2', plain,
% 7.51/7.72      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 7.51/7.72         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.51/7.72        | ~ (l1_pre_topc @ sk_A))),
% 7.51/7.72      inference('sup-', [status(thm)], ['0', '1'])).
% 7.51/7.72  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 7.51/7.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.72  thf('4', plain,
% 7.51/7.72      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 7.51/7.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.51/7.72      inference('demod', [status(thm)], ['2', '3'])).
% 7.51/7.72  thf(dt_k2_tops_1, axiom,
% 7.51/7.72    (![A:$i,B:$i]:
% 7.51/7.72     ( ( ( l1_pre_topc @ A ) & 
% 7.51/7.72         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 7.51/7.72       ( m1_subset_1 @
% 7.51/7.72         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 7.51/7.72  thf('5', plain,
% 7.51/7.72      (![X31 : $i, X32 : $i]:
% 7.51/7.72         (~ (l1_pre_topc @ X31)
% 7.51/7.72          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 7.51/7.72          | (m1_subset_1 @ (k2_tops_1 @ X31 @ X32) @ 
% 7.51/7.72             (k1_zfmisc_1 @ (u1_struct_0 @ X31))))),
% 7.51/7.72      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 7.51/7.72  thf('6', plain,
% 7.51/7.72      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 7.51/7.72         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.51/7.72        | ~ (l1_pre_topc @ sk_A))),
% 7.51/7.72      inference('sup-', [status(thm)], ['4', '5'])).
% 7.51/7.72  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 7.51/7.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.72  thf('8', plain,
% 7.51/7.72      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 7.51/7.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.51/7.72      inference('demod', [status(thm)], ['6', '7'])).
% 7.51/7.72  thf(t44_tops_1, axiom,
% 7.51/7.72    (![A:$i]:
% 7.51/7.72     ( ( l1_pre_topc @ A ) =>
% 7.51/7.72       ( ![B:$i]:
% 7.51/7.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.51/7.72           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 7.51/7.72  thf('9', plain,
% 7.51/7.72      (![X42 : $i, X43 : $i]:
% 7.51/7.72         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 7.51/7.72          | (r1_tarski @ (k1_tops_1 @ X43 @ X42) @ X42)
% 7.51/7.72          | ~ (l1_pre_topc @ X43))),
% 7.51/7.72      inference('cnf', [status(esa)], [t44_tops_1])).
% 7.51/7.72  thf('10', plain,
% 7.51/7.72      ((~ (l1_pre_topc @ sk_A)
% 7.51/7.72        | (r1_tarski @ 
% 7.51/7.72           (k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))) @ 
% 7.51/7.72           (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 7.51/7.72      inference('sup-', [status(thm)], ['8', '9'])).
% 7.51/7.72  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 7.51/7.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.72  thf('12', plain,
% 7.51/7.72      ((r1_tarski @ 
% 7.51/7.72        (k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))) @ 
% 7.51/7.72        (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 7.51/7.72      inference('demod', [status(thm)], ['10', '11'])).
% 7.51/7.72  thf('13', plain,
% 7.51/7.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.51/7.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.72  thf(dt_k3_subset_1, axiom,
% 7.51/7.72    (![A:$i,B:$i]:
% 7.51/7.72     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 7.51/7.72       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 7.51/7.72  thf('14', plain,
% 7.51/7.72      (![X8 : $i, X9 : $i]:
% 7.51/7.72         ((m1_subset_1 @ (k3_subset_1 @ X8 @ X9) @ (k1_zfmisc_1 @ X8))
% 7.51/7.72          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 7.51/7.72      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 7.51/7.72  thf('15', plain,
% 7.51/7.72      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 7.51/7.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.51/7.72      inference('sup-', [status(thm)], ['13', '14'])).
% 7.51/7.72  thf('16', plain,
% 7.51/7.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.51/7.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.72  thf(d5_subset_1, axiom,
% 7.51/7.72    (![A:$i,B:$i]:
% 7.51/7.72     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 7.51/7.72       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 7.51/7.72  thf('17', plain,
% 7.51/7.72      (![X6 : $i, X7 : $i]:
% 7.51/7.72         (((k3_subset_1 @ X6 @ X7) = (k4_xboole_0 @ X6 @ X7))
% 7.51/7.72          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 7.51/7.72      inference('cnf', [status(esa)], [d5_subset_1])).
% 7.51/7.72  thf('18', plain,
% 7.51/7.72      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 7.51/7.72         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 7.51/7.72      inference('sup-', [status(thm)], ['16', '17'])).
% 7.51/7.72  thf('19', plain,
% 7.51/7.72      ((m1_subset_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 7.51/7.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.51/7.72      inference('demod', [status(thm)], ['15', '18'])).
% 7.51/7.72  thf(dt_k2_pre_topc, axiom,
% 7.51/7.72    (![A:$i,B:$i]:
% 7.51/7.72     ( ( ( l1_pre_topc @ A ) & 
% 7.51/7.72         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 7.51/7.72       ( m1_subset_1 @
% 7.51/7.72         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 7.51/7.72  thf('20', plain,
% 7.51/7.72      (![X12 : $i, X13 : $i]:
% 7.51/7.72         (~ (l1_pre_topc @ X12)
% 7.51/7.72          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 7.51/7.72          | (m1_subset_1 @ (k2_pre_topc @ X12 @ X13) @ 
% 7.51/7.72             (k1_zfmisc_1 @ (u1_struct_0 @ X12))))),
% 7.51/7.72      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 7.51/7.72  thf('21', plain,
% 7.51/7.72      (((m1_subset_1 @ 
% 7.51/7.72         (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 7.51/7.72         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.51/7.72        | ~ (l1_pre_topc @ sk_A))),
% 7.51/7.72      inference('sup-', [status(thm)], ['19', '20'])).
% 7.51/7.72  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 7.51/7.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.72  thf('23', plain,
% 7.51/7.72      ((m1_subset_1 @ 
% 7.51/7.72        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 7.51/7.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.51/7.72      inference('demod', [status(thm)], ['21', '22'])).
% 7.51/7.72  thf(t69_tops_1, axiom,
% 7.51/7.72    (![A:$i]:
% 7.51/7.72     ( ( l1_pre_topc @ A ) =>
% 7.51/7.72       ( ![B:$i]:
% 7.51/7.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.51/7.72           ( ( v4_pre_topc @ B @ A ) =>
% 7.51/7.72             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 7.51/7.72  thf('24', plain,
% 7.51/7.72      (![X51 : $i, X52 : $i]:
% 7.51/7.72         (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 7.51/7.72          | (r1_tarski @ (k2_tops_1 @ X52 @ X51) @ X51)
% 7.51/7.72          | ~ (v4_pre_topc @ X51 @ X52)
% 7.51/7.72          | ~ (l1_pre_topc @ X52))),
% 7.51/7.72      inference('cnf', [status(esa)], [t69_tops_1])).
% 7.51/7.72  thf('25', plain,
% 7.51/7.72      ((~ (l1_pre_topc @ sk_A)
% 7.51/7.72        | ~ (v4_pre_topc @ 
% 7.51/7.72             (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 7.51/7.72             sk_A)
% 7.51/7.72        | (r1_tarski @ 
% 7.51/7.72           (k2_tops_1 @ sk_A @ 
% 7.51/7.72            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))) @ 
% 7.51/7.72           (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 7.51/7.72      inference('sup-', [status(thm)], ['23', '24'])).
% 7.51/7.72  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 7.51/7.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.72  thf('27', plain,
% 7.51/7.72      ((m1_subset_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 7.51/7.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.51/7.72      inference('demod', [status(thm)], ['15', '18'])).
% 7.51/7.72  thf(fc1_tops_1, axiom,
% 7.51/7.72    (![A:$i,B:$i]:
% 7.51/7.72     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 7.51/7.72         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 7.51/7.72       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 7.51/7.72  thf('28', plain,
% 7.51/7.72      (![X33 : $i, X34 : $i]:
% 7.51/7.72         (~ (l1_pre_topc @ X33)
% 7.51/7.72          | ~ (v2_pre_topc @ X33)
% 7.51/7.72          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 7.51/7.72          | (v4_pre_topc @ (k2_pre_topc @ X33 @ X34) @ X33))),
% 7.51/7.72      inference('cnf', [status(esa)], [fc1_tops_1])).
% 7.51/7.72  thf('29', plain,
% 7.51/7.72      (((v4_pre_topc @ 
% 7.51/7.72         (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 7.51/7.72         sk_A)
% 7.51/7.72        | ~ (v2_pre_topc @ sk_A)
% 7.51/7.72        | ~ (l1_pre_topc @ sk_A))),
% 7.51/7.72      inference('sup-', [status(thm)], ['27', '28'])).
% 7.51/7.72  thf('30', plain, ((v2_pre_topc @ sk_A)),
% 7.51/7.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.72  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 7.51/7.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.72  thf('32', plain,
% 7.51/7.72      ((v4_pre_topc @ 
% 7.51/7.72        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 7.51/7.72        sk_A)),
% 7.51/7.72      inference('demod', [status(thm)], ['29', '30', '31'])).
% 7.51/7.72  thf('33', plain,
% 7.51/7.72      ((m1_subset_1 @ 
% 7.51/7.72        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 7.51/7.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.51/7.72      inference('demod', [status(thm)], ['21', '22'])).
% 7.51/7.72  thf(t62_tops_1, axiom,
% 7.51/7.72    (![A:$i]:
% 7.51/7.72     ( ( l1_pre_topc @ A ) =>
% 7.51/7.72       ( ![B:$i]:
% 7.51/7.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.51/7.72           ( ( k2_tops_1 @ A @ B ) =
% 7.51/7.72             ( k2_tops_1 @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 7.51/7.72  thf('34', plain,
% 7.51/7.72      (![X49 : $i, X50 : $i]:
% 7.51/7.72         (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 7.51/7.72          | ((k2_tops_1 @ X50 @ X49)
% 7.51/7.72              = (k2_tops_1 @ X50 @ (k3_subset_1 @ (u1_struct_0 @ X50) @ X49)))
% 7.51/7.72          | ~ (l1_pre_topc @ X50))),
% 7.51/7.72      inference('cnf', [status(esa)], [t62_tops_1])).
% 7.51/7.72  thf('35', plain,
% 7.51/7.72      ((~ (l1_pre_topc @ sk_A)
% 7.51/7.72        | ((k2_tops_1 @ sk_A @ 
% 7.51/7.72            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 7.51/7.72            = (k2_tops_1 @ sk_A @ 
% 7.51/7.72               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.51/7.72                (k2_pre_topc @ sk_A @ 
% 7.51/7.72                 (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))))),
% 7.51/7.72      inference('sup-', [status(thm)], ['33', '34'])).
% 7.51/7.72  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 7.51/7.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.72  thf('37', plain,
% 7.51/7.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.51/7.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.72  thf(d1_tops_1, axiom,
% 7.51/7.72    (![A:$i]:
% 7.51/7.72     ( ( l1_pre_topc @ A ) =>
% 7.51/7.72       ( ![B:$i]:
% 7.51/7.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.51/7.72           ( ( k1_tops_1 @ A @ B ) =
% 7.51/7.72             ( k3_subset_1 @
% 7.51/7.72               ( u1_struct_0 @ A ) @ 
% 7.51/7.72               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 7.51/7.72  thf('38', plain,
% 7.51/7.72      (![X21 : $i, X22 : $i]:
% 7.51/7.72         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 7.51/7.72          | ((k1_tops_1 @ X22 @ X21)
% 7.51/7.72              = (k3_subset_1 @ (u1_struct_0 @ X22) @ 
% 7.51/7.72                 (k2_pre_topc @ X22 @ (k3_subset_1 @ (u1_struct_0 @ X22) @ X21))))
% 7.51/7.72          | ~ (l1_pre_topc @ X22))),
% 7.51/7.72      inference('cnf', [status(esa)], [d1_tops_1])).
% 7.51/7.72  thf('39', plain,
% 7.51/7.72      ((~ (l1_pre_topc @ sk_A)
% 7.51/7.72        | ((k1_tops_1 @ sk_A @ sk_B)
% 7.51/7.72            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.51/7.72               (k2_pre_topc @ sk_A @ 
% 7.51/7.72                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 7.51/7.72      inference('sup-', [status(thm)], ['37', '38'])).
% 7.51/7.72  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 7.51/7.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.72  thf('41', plain,
% 7.51/7.72      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 7.51/7.72         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 7.51/7.72      inference('sup-', [status(thm)], ['16', '17'])).
% 7.51/7.72  thf('42', plain,
% 7.51/7.72      (((k1_tops_1 @ sk_A @ sk_B)
% 7.51/7.72         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.51/7.72            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 7.51/7.72      inference('demod', [status(thm)], ['39', '40', '41'])).
% 7.51/7.72  thf('43', plain,
% 7.51/7.72      (((k2_tops_1 @ sk_A @ 
% 7.51/7.72         (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 7.51/7.72         = (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 7.51/7.72      inference('demod', [status(thm)], ['35', '36', '42'])).
% 7.51/7.72  thf('44', plain,
% 7.51/7.72      ((r1_tarski @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 7.51/7.72        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 7.51/7.72      inference('demod', [status(thm)], ['25', '26', '32', '43'])).
% 7.51/7.72  thf('45', plain,
% 7.51/7.72      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 7.51/7.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.51/7.72      inference('demod', [status(thm)], ['6', '7'])).
% 7.51/7.72  thf(t48_tops_1, axiom,
% 7.51/7.72    (![A:$i]:
% 7.51/7.72     ( ( l1_pre_topc @ A ) =>
% 7.51/7.72       ( ![B:$i]:
% 7.51/7.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.51/7.72           ( ![C:$i]:
% 7.51/7.72             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.51/7.72               ( ( r1_tarski @ B @ C ) =>
% 7.51/7.72                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 7.51/7.72  thf('46', plain,
% 7.51/7.72      (![X44 : $i, X45 : $i, X46 : $i]:
% 7.51/7.72         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 7.51/7.72          | ~ (r1_tarski @ X44 @ X46)
% 7.51/7.72          | (r1_tarski @ (k1_tops_1 @ X45 @ X44) @ (k1_tops_1 @ X45 @ X46))
% 7.51/7.72          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 7.51/7.72          | ~ (l1_pre_topc @ X45))),
% 7.51/7.72      inference('cnf', [status(esa)], [t48_tops_1])).
% 7.51/7.72  thf('47', plain,
% 7.51/7.72      (![X0 : $i]:
% 7.51/7.72         (~ (l1_pre_topc @ sk_A)
% 7.51/7.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.51/7.72          | (r1_tarski @ 
% 7.51/7.72             (k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))) @ 
% 7.51/7.72             (k1_tops_1 @ sk_A @ X0))
% 7.51/7.72          | ~ (r1_tarski @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ X0))),
% 7.51/7.72      inference('sup-', [status(thm)], ['45', '46'])).
% 7.51/7.72  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 7.51/7.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.72  thf('49', plain,
% 7.51/7.72      (![X0 : $i]:
% 7.51/7.72         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.51/7.72          | (r1_tarski @ 
% 7.51/7.72             (k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))) @ 
% 7.51/7.72             (k1_tops_1 @ sk_A @ X0))
% 7.51/7.72          | ~ (r1_tarski @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ X0))),
% 7.51/7.72      inference('demod', [status(thm)], ['47', '48'])).
% 7.51/7.72  thf('50', plain,
% 7.51/7.72      (((r1_tarski @ 
% 7.51/7.72         (k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))) @ 
% 7.51/7.72         (k1_tops_1 @ sk_A @ 
% 7.51/7.72          (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))
% 7.51/7.72        | ~ (m1_subset_1 @ 
% 7.51/7.72             (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 7.51/7.72             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 7.51/7.72      inference('sup-', [status(thm)], ['44', '49'])).
% 7.51/7.72  thf('51', plain,
% 7.51/7.72      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 7.51/7.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.51/7.72      inference('demod', [status(thm)], ['2', '3'])).
% 7.51/7.72  thf('52', plain,
% 7.51/7.72      (![X8 : $i, X9 : $i]:
% 7.51/7.72         ((m1_subset_1 @ (k3_subset_1 @ X8 @ X9) @ (k1_zfmisc_1 @ X8))
% 7.51/7.72          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 7.51/7.72      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 7.51/7.72  thf('53', plain,
% 7.51/7.72      ((m1_subset_1 @ 
% 7.51/7.72        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 7.51/7.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.51/7.72      inference('sup-', [status(thm)], ['51', '52'])).
% 7.51/7.72  thf('54', plain,
% 7.51/7.72      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 7.51/7.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.51/7.72      inference('demod', [status(thm)], ['2', '3'])).
% 7.51/7.72  thf('55', plain,
% 7.51/7.72      (![X6 : $i, X7 : $i]:
% 7.51/7.72         (((k3_subset_1 @ X6 @ X7) = (k4_xboole_0 @ X6 @ X7))
% 7.51/7.72          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 7.51/7.72      inference('cnf', [status(esa)], [d5_subset_1])).
% 7.51/7.72  thf('56', plain,
% 7.51/7.72      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 7.51/7.72         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 7.51/7.72      inference('sup-', [status(thm)], ['54', '55'])).
% 7.51/7.72  thf('57', plain,
% 7.51/7.72      ((m1_subset_1 @ 
% 7.51/7.72        (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 7.51/7.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.51/7.72      inference('demod', [status(thm)], ['53', '56'])).
% 7.51/7.72  thf('58', plain,
% 7.51/7.72      (![X21 : $i, X22 : $i]:
% 7.51/7.72         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 7.51/7.72          | ((k1_tops_1 @ X22 @ X21)
% 7.51/7.72              = (k3_subset_1 @ (u1_struct_0 @ X22) @ 
% 7.51/7.72                 (k2_pre_topc @ X22 @ (k3_subset_1 @ (u1_struct_0 @ X22) @ X21))))
% 7.51/7.72          | ~ (l1_pre_topc @ X22))),
% 7.51/7.72      inference('cnf', [status(esa)], [d1_tops_1])).
% 7.51/7.72  thf('59', plain,
% 7.51/7.72      ((~ (l1_pre_topc @ sk_A)
% 7.51/7.72        | ((k1_tops_1 @ sk_A @ 
% 7.51/7.72            (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))
% 7.51/7.72            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.51/7.72               (k2_pre_topc @ sk_A @ 
% 7.51/7.72                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.51/7.72                 (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 7.51/7.72                  (k1_tops_1 @ sk_A @ sk_B)))))))),
% 7.51/7.72      inference('sup-', [status(thm)], ['57', '58'])).
% 7.51/7.72  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 7.51/7.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.72  thf('61', plain,
% 7.51/7.72      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 7.51/7.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.51/7.72      inference('demod', [status(thm)], ['2', '3'])).
% 7.51/7.72  thf(involutiveness_k3_subset_1, axiom,
% 7.51/7.72    (![A:$i,B:$i]:
% 7.51/7.72     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 7.51/7.72       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 7.51/7.72  thf('62', plain,
% 7.51/7.72      (![X10 : $i, X11 : $i]:
% 7.51/7.72         (((k3_subset_1 @ X11 @ (k3_subset_1 @ X11 @ X10)) = (X10))
% 7.51/7.72          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 7.51/7.72      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 7.51/7.72  thf('63', plain,
% 7.51/7.72      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.51/7.72         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))
% 7.51/7.72         = (k1_tops_1 @ sk_A @ sk_B))),
% 7.51/7.72      inference('sup-', [status(thm)], ['61', '62'])).
% 7.51/7.72  thf('64', plain,
% 7.51/7.72      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 7.51/7.72         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 7.51/7.72      inference('sup-', [status(thm)], ['54', '55'])).
% 7.51/7.72  thf('65', plain,
% 7.51/7.72      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.51/7.72         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))
% 7.51/7.72         = (k1_tops_1 @ sk_A @ sk_B))),
% 7.51/7.72      inference('demod', [status(thm)], ['63', '64'])).
% 7.51/7.72  thf('66', plain,
% 7.51/7.72      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 7.51/7.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.51/7.72      inference('demod', [status(thm)], ['2', '3'])).
% 7.51/7.72  thf('67', plain,
% 7.51/7.72      (![X12 : $i, X13 : $i]:
% 7.51/7.72         (~ (l1_pre_topc @ X12)
% 7.51/7.72          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 7.51/7.72          | (m1_subset_1 @ (k2_pre_topc @ X12 @ X13) @ 
% 7.51/7.72             (k1_zfmisc_1 @ (u1_struct_0 @ X12))))),
% 7.51/7.72      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 7.51/7.72  thf('68', plain,
% 7.51/7.72      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 7.51/7.72         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.51/7.72        | ~ (l1_pre_topc @ sk_A))),
% 7.51/7.72      inference('sup-', [status(thm)], ['66', '67'])).
% 7.51/7.72  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 7.51/7.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.72  thf('70', plain,
% 7.51/7.72      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 7.51/7.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.51/7.72      inference('demod', [status(thm)], ['68', '69'])).
% 7.51/7.72  thf('71', plain,
% 7.51/7.72      (![X6 : $i, X7 : $i]:
% 7.51/7.72         (((k3_subset_1 @ X6 @ X7) = (k4_xboole_0 @ X6 @ X7))
% 7.51/7.72          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 7.51/7.72      inference('cnf', [status(esa)], [d5_subset_1])).
% 7.51/7.72  thf('72', plain,
% 7.51/7.72      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.51/7.72         (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 7.51/7.72         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 7.51/7.72            (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 7.51/7.72      inference('sup-', [status(thm)], ['70', '71'])).
% 7.51/7.72  thf('73', plain,
% 7.51/7.72      (((k1_tops_1 @ sk_A @ 
% 7.51/7.72         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))
% 7.51/7.72         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 7.51/7.72            (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 7.51/7.72      inference('demod', [status(thm)], ['59', '60', '65', '72'])).
% 7.51/7.72  thf('74', plain,
% 7.51/7.72      ((m1_subset_1 @ 
% 7.51/7.72        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 7.51/7.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.51/7.72      inference('demod', [status(thm)], ['21', '22'])).
% 7.51/7.72  thf('75', plain,
% 7.51/7.72      (![X10 : $i, X11 : $i]:
% 7.51/7.72         (((k3_subset_1 @ X11 @ (k3_subset_1 @ X11 @ X10)) = (X10))
% 7.51/7.72          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 7.51/7.72      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 7.51/7.72  thf('76', plain,
% 7.51/7.72      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.51/7.72         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.51/7.72          (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))
% 7.51/7.72         = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 7.51/7.72      inference('sup-', [status(thm)], ['74', '75'])).
% 7.51/7.72  thf('77', plain,
% 7.51/7.72      (((k1_tops_1 @ sk_A @ sk_B)
% 7.51/7.72         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.51/7.72            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 7.51/7.72      inference('demod', [status(thm)], ['39', '40', '41'])).
% 7.51/7.72  thf('78', plain,
% 7.51/7.72      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 7.51/7.72         = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 7.51/7.72      inference('demod', [status(thm)], ['76', '77'])).
% 7.51/7.72  thf('79', plain,
% 7.51/7.72      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 7.51/7.72         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 7.51/7.72      inference('sup-', [status(thm)], ['54', '55'])).
% 7.51/7.72  thf('80', plain,
% 7.51/7.72      (((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 7.51/7.72         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 7.51/7.72      inference('sup+', [status(thm)], ['78', '79'])).
% 7.51/7.72  thf('81', plain,
% 7.51/7.72      (((k1_tops_1 @ sk_A @ 
% 7.51/7.72         (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 7.51/7.72         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 7.51/7.72            (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 7.51/7.72      inference('demod', [status(thm)], ['73', '80'])).
% 7.51/7.72  thf('82', plain,
% 7.51/7.72      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 7.51/7.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.51/7.72      inference('demod', [status(thm)], ['68', '69'])).
% 7.51/7.72  thf('83', plain,
% 7.51/7.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.51/7.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.72  thf(t49_pre_topc, axiom,
% 7.51/7.72    (![A:$i]:
% 7.51/7.72     ( ( l1_pre_topc @ A ) =>
% 7.51/7.72       ( ![B:$i]:
% 7.51/7.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.51/7.72           ( ![C:$i]:
% 7.51/7.72             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.51/7.72               ( ( r1_tarski @ B @ C ) =>
% 7.51/7.72                 ( r1_tarski @
% 7.51/7.72                   ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 7.51/7.72  thf('84', plain,
% 7.51/7.72      (![X18 : $i, X19 : $i, X20 : $i]:
% 7.51/7.72         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 7.51/7.72          | ~ (r1_tarski @ X18 @ X20)
% 7.51/7.72          | (r1_tarski @ (k2_pre_topc @ X19 @ X18) @ (k2_pre_topc @ X19 @ X20))
% 7.51/7.72          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 7.51/7.72          | ~ (l1_pre_topc @ X19))),
% 7.51/7.72      inference('cnf', [status(esa)], [t49_pre_topc])).
% 7.51/7.72  thf('85', plain,
% 7.51/7.72      (![X0 : $i]:
% 7.51/7.72         (~ (l1_pre_topc @ sk_A)
% 7.51/7.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.51/7.72          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 7.51/7.72             (k2_pre_topc @ sk_A @ X0))
% 7.51/7.72          | ~ (r1_tarski @ sk_B @ X0))),
% 7.51/7.72      inference('sup-', [status(thm)], ['83', '84'])).
% 7.51/7.72  thf('86', plain, ((l1_pre_topc @ sk_A)),
% 7.51/7.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.72  thf('87', plain,
% 7.51/7.72      (![X0 : $i]:
% 7.51/7.72         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.51/7.72          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 7.51/7.72             (k2_pre_topc @ sk_A @ X0))
% 7.51/7.72          | ~ (r1_tarski @ sk_B @ X0))),
% 7.51/7.72      inference('demod', [status(thm)], ['85', '86'])).
% 7.51/7.72  thf('88', plain,
% 7.51/7.72      ((~ (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 7.51/7.72        | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 7.51/7.72           (k2_pre_topc @ sk_A @ 
% 7.51/7.72            (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))))),
% 7.51/7.72      inference('sup-', [status(thm)], ['82', '87'])).
% 7.51/7.72  thf('89', plain,
% 7.51/7.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.51/7.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.72  thf(d6_tops_1, axiom,
% 7.51/7.72    (![A:$i]:
% 7.51/7.72     ( ( l1_pre_topc @ A ) =>
% 7.51/7.72       ( ![B:$i]:
% 7.51/7.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.51/7.72           ( ( v4_tops_1 @ B @ A ) <=>
% 7.51/7.72             ( ( r1_tarski @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ B ) & 
% 7.51/7.72               ( r1_tarski @ B @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) ))).
% 7.51/7.72  thf('90', plain,
% 7.51/7.72      (![X25 : $i, X26 : $i]:
% 7.51/7.72         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 7.51/7.72          | ~ (v4_tops_1 @ X25 @ X26)
% 7.51/7.72          | (r1_tarski @ X25 @ (k2_pre_topc @ X26 @ (k1_tops_1 @ X26 @ X25)))
% 7.51/7.72          | ~ (l1_pre_topc @ X26))),
% 7.51/7.72      inference('cnf', [status(esa)], [d6_tops_1])).
% 7.51/7.72  thf('91', plain,
% 7.51/7.72      ((~ (l1_pre_topc @ sk_A)
% 7.51/7.72        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 7.51/7.72        | ~ (v4_tops_1 @ sk_B @ sk_A))),
% 7.51/7.72      inference('sup-', [status(thm)], ['89', '90'])).
% 7.51/7.72  thf('92', plain, ((l1_pre_topc @ sk_A)),
% 7.51/7.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.72  thf('93', plain, ((v4_tops_1 @ sk_B @ sk_A)),
% 7.51/7.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.72  thf('94', plain,
% 7.51/7.72      ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 7.51/7.72      inference('demod', [status(thm)], ['91', '92', '93'])).
% 7.51/7.72  thf('95', plain,
% 7.51/7.72      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 7.51/7.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.51/7.72      inference('demod', [status(thm)], ['2', '3'])).
% 7.51/7.72  thf(projectivity_k2_pre_topc, axiom,
% 7.51/7.72    (![A:$i,B:$i]:
% 7.51/7.72     ( ( ( l1_pre_topc @ A ) & 
% 7.51/7.72         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 7.51/7.72       ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) ) =
% 7.51/7.72         ( k2_pre_topc @ A @ B ) ) ))).
% 7.51/7.72  thf('96', plain,
% 7.51/7.72      (![X14 : $i, X15 : $i]:
% 7.51/7.72         (~ (l1_pre_topc @ X14)
% 7.51/7.72          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 7.51/7.72          | ((k2_pre_topc @ X14 @ (k2_pre_topc @ X14 @ X15))
% 7.51/7.72              = (k2_pre_topc @ X14 @ X15)))),
% 7.51/7.72      inference('cnf', [status(esa)], [projectivity_k2_pre_topc])).
% 7.51/7.72  thf('97', plain,
% 7.51/7.72      ((((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 7.51/7.72          = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 7.51/7.72        | ~ (l1_pre_topc @ sk_A))),
% 7.51/7.72      inference('sup-', [status(thm)], ['95', '96'])).
% 7.51/7.72  thf('98', plain, ((l1_pre_topc @ sk_A)),
% 7.51/7.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.72  thf('99', plain,
% 7.51/7.72      (((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 7.51/7.72         = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 7.51/7.72      inference('demod', [status(thm)], ['97', '98'])).
% 7.51/7.72  thf('100', plain,
% 7.51/7.72      ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 7.51/7.72        (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 7.51/7.72      inference('demod', [status(thm)], ['88', '94', '99'])).
% 7.51/7.72  thf(d10_xboole_0, axiom,
% 7.51/7.72    (![A:$i,B:$i]:
% 7.51/7.72     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 7.51/7.72  thf('101', plain,
% 7.51/7.72      (![X0 : $i, X2 : $i]:
% 7.51/7.72         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 7.51/7.72      inference('cnf', [status(esa)], [d10_xboole_0])).
% 7.51/7.72  thf('102', plain,
% 7.51/7.72      ((~ (r1_tarski @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 7.51/7.72           (k2_pre_topc @ sk_A @ sk_B))
% 7.51/7.72        | ((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 7.51/7.72            = (k2_pre_topc @ sk_A @ sk_B)))),
% 7.51/7.72      inference('sup-', [status(thm)], ['100', '101'])).
% 7.51/7.72  thf('103', plain,
% 7.51/7.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.51/7.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.72  thf('104', plain,
% 7.51/7.72      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 7.51/7.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.51/7.72      inference('demod', [status(thm)], ['2', '3'])).
% 7.51/7.72  thf('105', plain,
% 7.51/7.72      (![X18 : $i, X19 : $i, X20 : $i]:
% 7.51/7.72         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 7.51/7.72          | ~ (r1_tarski @ X18 @ X20)
% 7.51/7.72          | (r1_tarski @ (k2_pre_topc @ X19 @ X18) @ (k2_pre_topc @ X19 @ X20))
% 7.51/7.72          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 7.51/7.72          | ~ (l1_pre_topc @ X19))),
% 7.51/7.72      inference('cnf', [status(esa)], [t49_pre_topc])).
% 7.51/7.72  thf('106', plain,
% 7.51/7.72      (![X0 : $i]:
% 7.51/7.72         (~ (l1_pre_topc @ sk_A)
% 7.51/7.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.51/7.72          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 7.51/7.72             (k2_pre_topc @ sk_A @ X0))
% 7.51/7.72          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0))),
% 7.51/7.72      inference('sup-', [status(thm)], ['104', '105'])).
% 7.51/7.72  thf('107', plain, ((l1_pre_topc @ sk_A)),
% 7.51/7.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.72  thf('108', plain,
% 7.51/7.72      (![X0 : $i]:
% 7.51/7.72         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.51/7.72          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 7.51/7.72             (k2_pre_topc @ sk_A @ X0))
% 7.51/7.72          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0))),
% 7.51/7.72      inference('demod', [status(thm)], ['106', '107'])).
% 7.51/7.72  thf('109', plain,
% 7.51/7.72      ((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 7.51/7.72        | (r1_tarski @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 7.51/7.72           (k2_pre_topc @ sk_A @ sk_B)))),
% 7.51/7.72      inference('sup-', [status(thm)], ['103', '108'])).
% 7.51/7.72  thf('110', plain,
% 7.51/7.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.51/7.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.72  thf('111', plain,
% 7.51/7.72      (![X42 : $i, X43 : $i]:
% 7.51/7.72         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 7.51/7.72          | (r1_tarski @ (k1_tops_1 @ X43 @ X42) @ X42)
% 7.51/7.72          | ~ (l1_pre_topc @ X43))),
% 7.51/7.72      inference('cnf', [status(esa)], [t44_tops_1])).
% 7.51/7.72  thf('112', plain,
% 7.51/7.72      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 7.51/7.72      inference('sup-', [status(thm)], ['110', '111'])).
% 7.51/7.72  thf('113', plain, ((l1_pre_topc @ sk_A)),
% 7.51/7.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.72  thf('114', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 7.51/7.72      inference('demod', [status(thm)], ['112', '113'])).
% 7.51/7.72  thf('115', plain,
% 7.51/7.72      ((r1_tarski @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 7.51/7.72        (k2_pre_topc @ sk_A @ sk_B))),
% 7.51/7.72      inference('demod', [status(thm)], ['109', '114'])).
% 7.51/7.72  thf('116', plain,
% 7.51/7.72      (((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 7.51/7.72         = (k2_pre_topc @ sk_A @ sk_B))),
% 7.51/7.72      inference('demod', [status(thm)], ['102', '115'])).
% 7.51/7.72  thf('117', plain,
% 7.51/7.72      (((k1_tops_1 @ sk_A @ 
% 7.51/7.72         (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 7.51/7.72         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)))),
% 7.51/7.72      inference('demod', [status(thm)], ['81', '116'])).
% 7.51/7.72  thf('118', plain,
% 7.51/7.72      ((m1_subset_1 @ 
% 7.51/7.72        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 7.51/7.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.51/7.72      inference('demod', [status(thm)], ['21', '22'])).
% 7.51/7.72  thf('119', plain,
% 7.51/7.72      ((r1_tarski @ 
% 7.51/7.72        (k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))) @ 
% 7.51/7.72        (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)))),
% 7.51/7.72      inference('demod', [status(thm)], ['50', '117', '118'])).
% 7.51/7.72  thf(t67_xboole_1, axiom,
% 7.51/7.72    (![A:$i,B:$i,C:$i]:
% 7.51/7.72     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 7.51/7.72         ( r1_xboole_0 @ B @ C ) ) =>
% 7.51/7.72       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 7.51/7.72  thf('120', plain,
% 7.51/7.72      (![X3 : $i, X4 : $i, X5 : $i]:
% 7.51/7.72         (((X3) = (k1_xboole_0))
% 7.51/7.72          | ~ (r1_tarski @ X3 @ X4)
% 7.51/7.72          | ~ (r1_tarski @ X3 @ X5)
% 7.51/7.72          | ~ (r1_xboole_0 @ X4 @ X5))),
% 7.51/7.72      inference('cnf', [status(esa)], [t67_xboole_1])).
% 7.51/7.72  thf('121', plain,
% 7.51/7.72      (![X0 : $i]:
% 7.51/7.72         (~ (r1_xboole_0 @ 
% 7.51/7.72             (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 7.51/7.72             X0)
% 7.51/7.72          | ~ (r1_tarski @ 
% 7.51/7.72               (k1_tops_1 @ sk_A @ 
% 7.51/7.72                (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))) @ 
% 7.51/7.72               X0)
% 7.51/7.72          | ((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 7.51/7.72              = (k1_xboole_0)))),
% 7.51/7.72      inference('sup-', [status(thm)], ['119', '120'])).
% 7.51/7.72  thf('122', plain,
% 7.51/7.72      ((((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 7.51/7.72          = (k1_xboole_0))
% 7.51/7.72        | ~ (r1_xboole_0 @ 
% 7.51/7.72             (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 7.51/7.72             (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 7.51/7.72      inference('sup-', [status(thm)], ['12', '121'])).
% 7.51/7.72  thf('123', plain,
% 7.51/7.72      ((m1_subset_1 @ 
% 7.51/7.72        (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 7.51/7.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.51/7.72      inference('demod', [status(thm)], ['53', '56'])).
% 7.51/7.72  thf(t73_tops_1, axiom,
% 7.51/7.72    (![A:$i]:
% 7.51/7.72     ( ( l1_pre_topc @ A ) =>
% 7.51/7.72       ( ![B:$i]:
% 7.51/7.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.51/7.72           ( r1_xboole_0 @ ( k1_tops_1 @ A @ B ) @ ( k2_tops_1 @ A @ B ) ) ) ) ))).
% 7.51/7.72  thf('124', plain,
% 7.51/7.72      (![X53 : $i, X54 : $i]:
% 7.51/7.72         (~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (u1_struct_0 @ X54)))
% 7.51/7.72          | (r1_xboole_0 @ (k1_tops_1 @ X54 @ X53) @ (k2_tops_1 @ X54 @ X53))
% 7.51/7.72          | ~ (l1_pre_topc @ X54))),
% 7.51/7.72      inference('cnf', [status(esa)], [t73_tops_1])).
% 7.51/7.72  thf('125', plain,
% 7.51/7.72      ((~ (l1_pre_topc @ sk_A)
% 7.51/7.72        | (r1_xboole_0 @ 
% 7.51/7.72           (k1_tops_1 @ sk_A @ 
% 7.51/7.72            (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))) @ 
% 7.51/7.72           (k2_tops_1 @ sk_A @ 
% 7.51/7.72            (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))))),
% 7.51/7.72      inference('sup-', [status(thm)], ['123', '124'])).
% 7.51/7.72  thf('126', plain, ((l1_pre_topc @ sk_A)),
% 7.51/7.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.72  thf('127', plain,
% 7.51/7.72      (((k1_tops_1 @ sk_A @ 
% 7.51/7.72         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))
% 7.51/7.72         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 7.51/7.72            (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 7.51/7.72      inference('demod', [status(thm)], ['59', '60', '65', '72'])).
% 7.51/7.72  thf('128', plain,
% 7.51/7.72      ((m1_subset_1 @ 
% 7.51/7.72        (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 7.51/7.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.51/7.72      inference('demod', [status(thm)], ['53', '56'])).
% 7.51/7.72  thf('129', plain,
% 7.51/7.72      (![X49 : $i, X50 : $i]:
% 7.51/7.72         (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 7.51/7.72          | ((k2_tops_1 @ X50 @ X49)
% 7.51/7.72              = (k2_tops_1 @ X50 @ (k3_subset_1 @ (u1_struct_0 @ X50) @ X49)))
% 7.51/7.72          | ~ (l1_pre_topc @ X50))),
% 7.51/7.72      inference('cnf', [status(esa)], [t62_tops_1])).
% 7.51/7.72  thf('130', plain,
% 7.51/7.72      ((~ (l1_pre_topc @ sk_A)
% 7.51/7.72        | ((k2_tops_1 @ sk_A @ 
% 7.51/7.72            (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))
% 7.51/7.72            = (k2_tops_1 @ sk_A @ 
% 7.51/7.72               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.51/7.72                (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))))))),
% 7.51/7.72      inference('sup-', [status(thm)], ['128', '129'])).
% 7.51/7.72  thf('131', plain, ((l1_pre_topc @ sk_A)),
% 7.51/7.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.72  thf('132', plain,
% 7.51/7.72      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.51/7.72         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))
% 7.51/7.72         = (k1_tops_1 @ sk_A @ sk_B))),
% 7.51/7.72      inference('demod', [status(thm)], ['63', '64'])).
% 7.51/7.72  thf('133', plain,
% 7.51/7.72      (((k2_tops_1 @ sk_A @ 
% 7.51/7.72         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))
% 7.51/7.72         = (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 7.51/7.72      inference('demod', [status(thm)], ['130', '131', '132'])).
% 7.51/7.72  thf('134', plain,
% 7.51/7.72      ((r1_xboole_0 @ 
% 7.51/7.72        (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 7.51/7.72         (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))) @ 
% 7.51/7.72        (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 7.51/7.72      inference('demod', [status(thm)], ['125', '126', '127', '133'])).
% 7.51/7.72  thf('135', plain,
% 7.51/7.72      (((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 7.51/7.72         = (k2_pre_topc @ sk_A @ sk_B))),
% 7.51/7.72      inference('demod', [status(thm)], ['102', '115'])).
% 7.51/7.72  thf('136', plain,
% 7.51/7.72      ((r1_xboole_0 @ 
% 7.51/7.72        (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 7.51/7.72        (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 7.51/7.72      inference('demod', [status(thm)], ['134', '135'])).
% 7.51/7.72  thf('137', plain,
% 7.51/7.72      (((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 7.51/7.72         = (k1_xboole_0))),
% 7.51/7.72      inference('demod', [status(thm)], ['122', '136'])).
% 7.51/7.72  thf('138', plain,
% 7.51/7.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.51/7.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.72  thf('139', plain,
% 7.51/7.72      (![X12 : $i, X13 : $i]:
% 7.51/7.72         (~ (l1_pre_topc @ X12)
% 7.51/7.72          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 7.51/7.72          | (m1_subset_1 @ (k2_pre_topc @ X12 @ X13) @ 
% 7.51/7.72             (k1_zfmisc_1 @ (u1_struct_0 @ X12))))),
% 7.51/7.72      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 7.51/7.72  thf('140', plain,
% 7.51/7.72      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 7.51/7.72         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.51/7.72        | ~ (l1_pre_topc @ sk_A))),
% 7.51/7.72      inference('sup-', [status(thm)], ['138', '139'])).
% 7.51/7.72  thf('141', plain, ((l1_pre_topc @ sk_A)),
% 7.51/7.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.72  thf('142', plain,
% 7.51/7.72      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 7.51/7.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.51/7.72      inference('demod', [status(thm)], ['140', '141'])).
% 7.51/7.72  thf(t102_tops_1, axiom,
% 7.51/7.72    (![A:$i]:
% 7.51/7.72     ( ( l1_pre_topc @ A ) =>
% 7.51/7.72       ( ![B:$i]:
% 7.51/7.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.51/7.72           ( ( v5_tops_1 @ B @ A ) =>
% 7.51/7.72             ( ( k2_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) =
% 7.51/7.72               ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 7.51/7.72  thf('143', plain,
% 7.51/7.72      (![X37 : $i, X38 : $i]:
% 7.51/7.72         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 7.51/7.72          | ((k2_tops_1 @ X38 @ (k1_tops_1 @ X38 @ X37))
% 7.51/7.72              = (k2_tops_1 @ X38 @ X37))
% 7.51/7.72          | ~ (v5_tops_1 @ X37 @ X38)
% 7.51/7.72          | ~ (l1_pre_topc @ X38))),
% 7.51/7.72      inference('cnf', [status(esa)], [t102_tops_1])).
% 7.51/7.72  thf('144', plain,
% 7.51/7.72      ((~ (l1_pre_topc @ sk_A)
% 7.51/7.72        | ~ (v5_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 7.51/7.72        | ((k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 7.51/7.72            = (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))),
% 7.51/7.72      inference('sup-', [status(thm)], ['142', '143'])).
% 7.51/7.72  thf('145', plain, ((l1_pre_topc @ sk_A)),
% 7.51/7.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.72  thf('146', plain,
% 7.51/7.72      ((~ (v5_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 7.51/7.72        | ((k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 7.51/7.72            = (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))),
% 7.51/7.72      inference('demod', [status(thm)], ['144', '145'])).
% 7.51/7.72  thf('147', plain,
% 7.51/7.72      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 7.51/7.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.51/7.72      inference('demod', [status(thm)], ['68', '69'])).
% 7.51/7.72  thf(d7_tops_1, axiom,
% 7.51/7.72    (![A:$i]:
% 7.51/7.72     ( ( l1_pre_topc @ A ) =>
% 7.51/7.72       ( ![B:$i]:
% 7.51/7.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.51/7.72           ( ( v5_tops_1 @ B @ A ) <=>
% 7.51/7.72             ( ( B ) = ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 7.51/7.72  thf('148', plain,
% 7.51/7.72      (![X27 : $i, X28 : $i]:
% 7.51/7.72         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 7.51/7.72          | ((X27) != (k2_pre_topc @ X28 @ (k1_tops_1 @ X28 @ X27)))
% 7.51/7.72          | (v5_tops_1 @ X27 @ X28)
% 7.51/7.72          | ~ (l1_pre_topc @ X28))),
% 7.51/7.72      inference('cnf', [status(esa)], [d7_tops_1])).
% 7.51/7.72  thf('149', plain,
% 7.51/7.72      ((~ (l1_pre_topc @ sk_A)
% 7.51/7.72        | (v5_tops_1 @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A)
% 7.51/7.72        | ((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 7.51/7.72            != (k2_pre_topc @ sk_A @ 
% 7.51/7.72                (k1_tops_1 @ sk_A @ 
% 7.51/7.72                 (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))))),
% 7.51/7.72      inference('sup-', [status(thm)], ['147', '148'])).
% 7.51/7.72  thf('150', plain, ((l1_pre_topc @ sk_A)),
% 7.51/7.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.72  thf('151', plain,
% 7.51/7.72      (((v5_tops_1 @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A)
% 7.51/7.72        | ((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 7.51/7.72            != (k2_pre_topc @ sk_A @ 
% 7.51/7.72                (k1_tops_1 @ sk_A @ 
% 7.51/7.72                 (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))))),
% 7.51/7.72      inference('demod', [status(thm)], ['149', '150'])).
% 7.51/7.72  thf('152', plain,
% 7.51/7.72      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 7.51/7.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.51/7.72      inference('demod', [status(thm)], ['2', '3'])).
% 7.51/7.72  thf(t58_tops_1, axiom,
% 7.51/7.72    (![A:$i]:
% 7.51/7.72     ( ( l1_pre_topc @ A ) =>
% 7.51/7.72       ( ![B:$i]:
% 7.51/7.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.51/7.72           ( ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) =
% 7.51/7.72             ( k2_pre_topc @
% 7.51/7.72               A @ 
% 7.51/7.72               ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) ))).
% 7.51/7.72  thf('153', plain,
% 7.51/7.72      (![X47 : $i, X48 : $i]:
% 7.51/7.72         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48)))
% 7.51/7.72          | ((k2_pre_topc @ X48 @ (k1_tops_1 @ X48 @ X47))
% 7.51/7.72              = (k2_pre_topc @ X48 @ 
% 7.51/7.72                 (k1_tops_1 @ X48 @ 
% 7.51/7.72                  (k2_pre_topc @ X48 @ (k1_tops_1 @ X48 @ X47)))))
% 7.51/7.72          | ~ (l1_pre_topc @ X48))),
% 7.51/7.72      inference('cnf', [status(esa)], [t58_tops_1])).
% 7.51/7.72  thf('154', plain,
% 7.51/7.72      ((~ (l1_pre_topc @ sk_A)
% 7.51/7.72        | ((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 7.51/7.72            = (k2_pre_topc @ sk_A @ 
% 7.51/7.72               (k1_tops_1 @ sk_A @ 
% 7.51/7.72                (k2_pre_topc @ sk_A @ 
% 7.51/7.72                 (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))))))),
% 7.51/7.72      inference('sup-', [status(thm)], ['152', '153'])).
% 7.51/7.72  thf('155', plain, ((l1_pre_topc @ sk_A)),
% 7.51/7.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.72  thf('156', plain,
% 7.51/7.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.51/7.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.72  thf(projectivity_k1_tops_1, axiom,
% 7.51/7.72    (![A:$i,B:$i]:
% 7.51/7.72     ( ( ( l1_pre_topc @ A ) & 
% 7.51/7.72         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 7.51/7.72       ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) = ( k1_tops_1 @ A @ B ) ) ))).
% 7.51/7.72  thf('157', plain,
% 7.51/7.72      (![X35 : $i, X36 : $i]:
% 7.51/7.72         (~ (l1_pre_topc @ X35)
% 7.51/7.72          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 7.51/7.72          | ((k1_tops_1 @ X35 @ (k1_tops_1 @ X35 @ X36))
% 7.51/7.72              = (k1_tops_1 @ X35 @ X36)))),
% 7.51/7.72      inference('cnf', [status(esa)], [projectivity_k1_tops_1])).
% 7.51/7.72  thf('158', plain,
% 7.51/7.72      ((((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 7.51/7.72          = (k1_tops_1 @ sk_A @ sk_B))
% 7.51/7.72        | ~ (l1_pre_topc @ sk_A))),
% 7.51/7.72      inference('sup-', [status(thm)], ['156', '157'])).
% 7.51/7.72  thf('159', plain, ((l1_pre_topc @ sk_A)),
% 7.51/7.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.72  thf('160', plain,
% 7.51/7.72      (((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 7.51/7.72         = (k1_tops_1 @ sk_A @ sk_B))),
% 7.51/7.72      inference('demod', [status(thm)], ['158', '159'])).
% 7.51/7.72  thf('161', plain,
% 7.51/7.72      (((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 7.51/7.72         = (k1_tops_1 @ sk_A @ sk_B))),
% 7.51/7.72      inference('demod', [status(thm)], ['158', '159'])).
% 7.51/7.72  thf('162', plain,
% 7.51/7.72      (((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 7.51/7.72         = (k2_pre_topc @ sk_A @ 
% 7.51/7.72            (k1_tops_1 @ sk_A @ 
% 7.51/7.72             (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))))),
% 7.51/7.72      inference('demod', [status(thm)], ['154', '155', '160', '161'])).
% 7.51/7.72  thf('163', plain,
% 7.51/7.72      (((v5_tops_1 @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A)
% 7.51/7.72        | ((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 7.51/7.72            != (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 7.51/7.72      inference('demod', [status(thm)], ['151', '162'])).
% 7.51/7.72  thf('164', plain,
% 7.51/7.72      ((v5_tops_1 @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A)),
% 7.51/7.72      inference('simplify', [status(thm)], ['163'])).
% 7.51/7.72  thf('165', plain,
% 7.51/7.72      (((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 7.51/7.72         = (k2_pre_topc @ sk_A @ sk_B))),
% 7.51/7.72      inference('demod', [status(thm)], ['102', '115'])).
% 7.51/7.72  thf('166', plain, ((v5_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 7.51/7.72      inference('demod', [status(thm)], ['164', '165'])).
% 7.51/7.72  thf('167', plain,
% 7.51/7.72      (((k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 7.51/7.72         = (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 7.51/7.72      inference('demod', [status(thm)], ['146', '166'])).
% 7.51/7.72  thf('168', plain,
% 7.51/7.72      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 7.51/7.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.51/7.72      inference('demod', [status(thm)], ['140', '141'])).
% 7.51/7.72  thf('169', plain,
% 7.51/7.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.51/7.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.72  thf('170', plain,
% 7.51/7.72      (![X44 : $i, X45 : $i, X46 : $i]:
% 7.51/7.72         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 7.51/7.72          | ~ (r1_tarski @ X44 @ X46)
% 7.51/7.72          | (r1_tarski @ (k1_tops_1 @ X45 @ X44) @ (k1_tops_1 @ X45 @ X46))
% 7.51/7.72          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 7.51/7.72          | ~ (l1_pre_topc @ X45))),
% 7.51/7.72      inference('cnf', [status(esa)], [t48_tops_1])).
% 7.51/7.72  thf('171', plain,
% 7.51/7.72      (![X0 : $i]:
% 7.51/7.72         (~ (l1_pre_topc @ sk_A)
% 7.51/7.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.51/7.72          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 7.51/7.72          | ~ (r1_tarski @ sk_B @ X0))),
% 7.51/7.72      inference('sup-', [status(thm)], ['169', '170'])).
% 7.51/7.72  thf('172', plain, ((l1_pre_topc @ sk_A)),
% 7.51/7.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.72  thf('173', plain,
% 7.51/7.72      (![X0 : $i]:
% 7.51/7.72         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.51/7.72          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 7.51/7.72          | ~ (r1_tarski @ sk_B @ X0))),
% 7.51/7.72      inference('demod', [status(thm)], ['171', '172'])).
% 7.51/7.72  thf('174', plain,
% 7.51/7.72      ((~ (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))
% 7.51/7.72        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 7.51/7.72           (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))),
% 7.51/7.72      inference('sup-', [status(thm)], ['168', '173'])).
% 7.51/7.72  thf('175', plain,
% 7.51/7.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.51/7.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.72  thf(t48_pre_topc, axiom,
% 7.51/7.72    (![A:$i]:
% 7.51/7.72     ( ( l1_pre_topc @ A ) =>
% 7.51/7.72       ( ![B:$i]:
% 7.51/7.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.51/7.72           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 7.51/7.72  thf('176', plain,
% 7.51/7.72      (![X16 : $i, X17 : $i]:
% 7.51/7.72         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 7.51/7.72          | (r1_tarski @ X16 @ (k2_pre_topc @ X17 @ X16))
% 7.51/7.72          | ~ (l1_pre_topc @ X17))),
% 7.51/7.72      inference('cnf', [status(esa)], [t48_pre_topc])).
% 7.51/7.72  thf('177', plain,
% 7.51/7.72      ((~ (l1_pre_topc @ sk_A)
% 7.51/7.72        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 7.51/7.72      inference('sup-', [status(thm)], ['175', '176'])).
% 7.51/7.72  thf('178', plain, ((l1_pre_topc @ sk_A)),
% 7.51/7.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.72  thf('179', plain, ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 7.51/7.72      inference('demod', [status(thm)], ['177', '178'])).
% 7.51/7.72  thf('180', plain,
% 7.51/7.72      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 7.51/7.72        (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 7.51/7.72      inference('demod', [status(thm)], ['174', '179'])).
% 7.51/7.72  thf('181', plain,
% 7.51/7.72      (![X0 : $i, X2 : $i]:
% 7.51/7.72         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 7.51/7.72      inference('cnf', [status(esa)], [d10_xboole_0])).
% 7.51/7.72  thf('182', plain,
% 7.51/7.72      ((~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 7.51/7.72           (k1_tops_1 @ sk_A @ sk_B))
% 7.51/7.72        | ((k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 7.51/7.72            = (k1_tops_1 @ sk_A @ sk_B)))),
% 7.51/7.72      inference('sup-', [status(thm)], ['180', '181'])).
% 7.51/7.72  thf('183', plain,
% 7.51/7.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.51/7.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.72  thf('184', plain,
% 7.51/7.72      (![X25 : $i, X26 : $i]:
% 7.51/7.72         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 7.51/7.72          | ~ (v4_tops_1 @ X25 @ X26)
% 7.51/7.72          | (r1_tarski @ (k1_tops_1 @ X26 @ (k2_pre_topc @ X26 @ X25)) @ X25)
% 7.51/7.72          | ~ (l1_pre_topc @ X26))),
% 7.51/7.72      inference('cnf', [status(esa)], [d6_tops_1])).
% 7.51/7.72  thf('185', plain,
% 7.51/7.72      ((~ (l1_pre_topc @ sk_A)
% 7.51/7.72        | (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_B)
% 7.51/7.72        | ~ (v4_tops_1 @ sk_B @ sk_A))),
% 7.51/7.72      inference('sup-', [status(thm)], ['183', '184'])).
% 7.51/7.72  thf('186', plain, ((l1_pre_topc @ sk_A)),
% 7.51/7.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.72  thf('187', plain, ((v4_tops_1 @ sk_B @ sk_A)),
% 7.51/7.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.72  thf('188', plain,
% 7.51/7.72      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_B)),
% 7.51/7.72      inference('demod', [status(thm)], ['185', '186', '187'])).
% 7.51/7.72  thf('189', plain,
% 7.51/7.72      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 7.51/7.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.51/7.72      inference('demod', [status(thm)], ['140', '141'])).
% 7.51/7.72  thf('190', plain,
% 7.51/7.72      (![X29 : $i, X30 : $i]:
% 7.51/7.72         (~ (l1_pre_topc @ X29)
% 7.51/7.72          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 7.51/7.72          | (m1_subset_1 @ (k1_tops_1 @ X29 @ X30) @ 
% 7.51/7.72             (k1_zfmisc_1 @ (u1_struct_0 @ X29))))),
% 7.51/7.72      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 7.51/7.72  thf('191', plain,
% 7.51/7.72      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 7.51/7.72         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.51/7.72        | ~ (l1_pre_topc @ sk_A))),
% 7.51/7.72      inference('sup-', [status(thm)], ['189', '190'])).
% 7.51/7.72  thf('192', plain, ((l1_pre_topc @ sk_A)),
% 7.51/7.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.72  thf('193', plain,
% 7.51/7.72      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 7.51/7.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.51/7.72      inference('demod', [status(thm)], ['191', '192'])).
% 7.51/7.72  thf('194', plain,
% 7.51/7.72      (![X44 : $i, X45 : $i, X46 : $i]:
% 7.51/7.72         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 7.51/7.72          | ~ (r1_tarski @ X44 @ X46)
% 7.51/7.72          | (r1_tarski @ (k1_tops_1 @ X45 @ X44) @ (k1_tops_1 @ X45 @ X46))
% 7.51/7.72          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 7.51/7.72          | ~ (l1_pre_topc @ X45))),
% 7.51/7.72      inference('cnf', [status(esa)], [t48_tops_1])).
% 7.51/7.72  thf('195', plain,
% 7.51/7.72      (![X0 : $i]:
% 7.51/7.72         (~ (l1_pre_topc @ sk_A)
% 7.51/7.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.51/7.72          | (r1_tarski @ 
% 7.51/7.72             (k1_tops_1 @ sk_A @ 
% 7.51/7.72              (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))) @ 
% 7.51/7.72             (k1_tops_1 @ sk_A @ X0))
% 7.51/7.72          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 7.51/7.72               X0))),
% 7.51/7.72      inference('sup-', [status(thm)], ['193', '194'])).
% 7.51/7.72  thf('196', plain, ((l1_pre_topc @ sk_A)),
% 7.51/7.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.72  thf('197', plain,
% 7.51/7.72      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 7.51/7.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.51/7.72      inference('demod', [status(thm)], ['140', '141'])).
% 7.51/7.72  thf('198', plain,
% 7.51/7.72      (![X35 : $i, X36 : $i]:
% 7.51/7.72         (~ (l1_pre_topc @ X35)
% 7.51/7.72          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 7.51/7.72          | ((k1_tops_1 @ X35 @ (k1_tops_1 @ X35 @ X36))
% 7.51/7.72              = (k1_tops_1 @ X35 @ X36)))),
% 7.51/7.72      inference('cnf', [status(esa)], [projectivity_k1_tops_1])).
% 7.51/7.72  thf('199', plain,
% 7.51/7.72      ((((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 7.51/7.72          = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 7.51/7.72        | ~ (l1_pre_topc @ sk_A))),
% 7.51/7.72      inference('sup-', [status(thm)], ['197', '198'])).
% 7.51/7.72  thf('200', plain, ((l1_pre_topc @ sk_A)),
% 7.51/7.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.72  thf('201', plain,
% 7.51/7.72      (((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 7.51/7.72         = (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 7.51/7.72      inference('demod', [status(thm)], ['199', '200'])).
% 7.51/7.72  thf('202', plain,
% 7.51/7.72      (![X0 : $i]:
% 7.51/7.72         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.51/7.72          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 7.51/7.72             (k1_tops_1 @ sk_A @ X0))
% 7.51/7.72          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 7.51/7.72               X0))),
% 7.51/7.72      inference('demod', [status(thm)], ['195', '196', '201'])).
% 7.51/7.72  thf('203', plain,
% 7.51/7.72      (((r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 7.51/7.72         (k1_tops_1 @ sk_A @ sk_B))
% 7.51/7.72        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 7.51/7.72      inference('sup-', [status(thm)], ['188', '202'])).
% 7.51/7.72  thf('204', plain,
% 7.51/7.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.51/7.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.72  thf('205', plain,
% 7.51/7.72      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 7.51/7.72        (k1_tops_1 @ sk_A @ sk_B))),
% 7.51/7.72      inference('demod', [status(thm)], ['203', '204'])).
% 7.51/7.72  thf('206', plain,
% 7.51/7.72      (((k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 7.51/7.72         = (k1_tops_1 @ sk_A @ sk_B))),
% 7.51/7.72      inference('demod', [status(thm)], ['182', '205'])).
% 7.51/7.72  thf('207', plain,
% 7.51/7.72      (((k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 7.51/7.72         = (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 7.51/7.72      inference('demod', [status(thm)], ['167', '206'])).
% 7.51/7.72  thf('208', plain,
% 7.51/7.72      (((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 7.51/7.72         = (k1_xboole_0))),
% 7.51/7.72      inference('demod', [status(thm)], ['137', '207'])).
% 7.51/7.72  thf('209', plain,
% 7.51/7.72      ((m1_subset_1 @ 
% 7.51/7.72        (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 7.51/7.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.51/7.72      inference('demod', [status(thm)], ['53', '56'])).
% 7.51/7.72  thf(d2_tops_1, axiom,
% 7.51/7.72    (![A:$i]:
% 7.51/7.72     ( ( l1_pre_topc @ A ) =>
% 7.51/7.72       ( ![B:$i]:
% 7.51/7.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 7.51/7.72           ( ( k2_tops_1 @ A @ B ) =
% 7.51/7.72             ( k9_subset_1 @
% 7.51/7.72               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 7.51/7.72               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 7.51/7.72  thf('210', plain,
% 7.51/7.72      (![X23 : $i, X24 : $i]:
% 7.51/7.72         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 7.51/7.72          | ((k2_tops_1 @ X24 @ X23)
% 7.51/7.72              = (k9_subset_1 @ (u1_struct_0 @ X24) @ 
% 7.51/7.72                 (k2_pre_topc @ X24 @ X23) @ 
% 7.51/7.72                 (k2_pre_topc @ X24 @ (k3_subset_1 @ (u1_struct_0 @ X24) @ X23))))
% 7.51/7.72          | ~ (l1_pre_topc @ X24))),
% 7.51/7.72      inference('cnf', [status(esa)], [d2_tops_1])).
% 7.51/7.72  thf('211', plain,
% 7.51/7.72      ((~ (l1_pre_topc @ sk_A)
% 7.51/7.72        | ((k2_tops_1 @ sk_A @ 
% 7.51/7.72            (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))
% 7.51/7.72            = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.51/7.72               (k2_pre_topc @ sk_A @ 
% 7.51/7.72                (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))) @ 
% 7.51/7.72               (k2_pre_topc @ sk_A @ 
% 7.51/7.72                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.51/7.72                 (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 7.51/7.72                  (k1_tops_1 @ sk_A @ sk_B)))))))),
% 7.51/7.72      inference('sup-', [status(thm)], ['209', '210'])).
% 7.51/7.72  thf('212', plain, ((l1_pre_topc @ sk_A)),
% 7.51/7.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.72  thf('213', plain,
% 7.51/7.72      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.51/7.72         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))
% 7.51/7.72         = (k1_tops_1 @ sk_A @ sk_B))),
% 7.51/7.72      inference('demod', [status(thm)], ['63', '64'])).
% 7.51/7.72  thf('214', plain,
% 7.51/7.72      (((k2_tops_1 @ sk_A @ 
% 7.51/7.72         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))
% 7.51/7.72         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.51/7.72            (k2_pre_topc @ sk_A @ 
% 7.51/7.72             (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))) @ 
% 7.51/7.72            (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 7.51/7.72      inference('demod', [status(thm)], ['211', '212', '213'])).
% 7.51/7.72  thf('215', plain,
% 7.51/7.72      (((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 7.51/7.72         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 7.51/7.72      inference('sup+', [status(thm)], ['78', '79'])).
% 7.51/7.72  thf('216', plain,
% 7.51/7.72      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 7.51/7.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.51/7.72      inference('demod', [status(thm)], ['191', '192'])).
% 7.51/7.72  thf('217', plain,
% 7.51/7.72      (![X49 : $i, X50 : $i]:
% 7.51/7.72         (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 7.51/7.72          | ((k2_tops_1 @ X50 @ X49)
% 7.51/7.72              = (k2_tops_1 @ X50 @ (k3_subset_1 @ (u1_struct_0 @ X50) @ X49)))
% 7.51/7.72          | ~ (l1_pre_topc @ X50))),
% 7.51/7.72      inference('cnf', [status(esa)], [t62_tops_1])).
% 7.51/7.72  thf('218', plain,
% 7.51/7.72      ((~ (l1_pre_topc @ sk_A)
% 7.51/7.72        | ((k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 7.51/7.72            = (k2_tops_1 @ sk_A @ 
% 7.51/7.72               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.51/7.72                (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))))),
% 7.51/7.72      inference('sup-', [status(thm)], ['216', '217'])).
% 7.51/7.72  thf('219', plain, ((l1_pre_topc @ sk_A)),
% 7.51/7.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.72  thf('220', plain,
% 7.51/7.72      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 7.51/7.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.51/7.72      inference('demod', [status(thm)], ['191', '192'])).
% 7.51/7.72  thf('221', plain,
% 7.51/7.72      (![X6 : $i, X7 : $i]:
% 7.51/7.72         (((k3_subset_1 @ X6 @ X7) = (k4_xboole_0 @ X6 @ X7))
% 7.51/7.72          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 7.51/7.72      inference('cnf', [status(esa)], [d5_subset_1])).
% 7.51/7.72  thf('222', plain,
% 7.51/7.72      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.51/7.72         (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 7.51/7.72         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 7.51/7.72            (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))),
% 7.51/7.72      inference('sup-', [status(thm)], ['220', '221'])).
% 7.51/7.72  thf('223', plain,
% 7.51/7.72      (((k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 7.51/7.72         = (k2_tops_1 @ sk_A @ 
% 7.51/7.72            (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 7.51/7.72             (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))))),
% 7.51/7.72      inference('demod', [status(thm)], ['218', '219', '222'])).
% 7.51/7.72  thf('224', plain,
% 7.51/7.72      (((k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))
% 7.51/7.72         = (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 7.51/7.72      inference('demod', [status(thm)], ['146', '166'])).
% 7.51/7.72  thf('225', plain,
% 7.51/7.72      (((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 7.51/7.72         = (k2_tops_1 @ sk_A @ 
% 7.51/7.72            (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 7.51/7.72             (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))))),
% 7.51/7.72      inference('demod', [status(thm)], ['223', '224'])).
% 7.51/7.72  thf('226', plain,
% 7.51/7.72      (((k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 7.51/7.72         = (k1_tops_1 @ sk_A @ sk_B))),
% 7.51/7.72      inference('demod', [status(thm)], ['182', '205'])).
% 7.51/7.72  thf('227', plain,
% 7.51/7.72      (((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 7.51/7.72         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 7.51/7.72      inference('sup+', [status(thm)], ['78', '79'])).
% 7.51/7.72  thf('228', plain,
% 7.51/7.72      (((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 7.51/7.72         = (k2_tops_1 @ sk_A @ 
% 7.51/7.72            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 7.51/7.72      inference('demod', [status(thm)], ['225', '226', '227'])).
% 7.51/7.72  thf('229', plain,
% 7.51/7.72      (((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 7.51/7.72         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B)))),
% 7.51/7.72      inference('sup+', [status(thm)], ['78', '79'])).
% 7.51/7.72  thf('230', plain,
% 7.51/7.72      ((m1_subset_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 7.51/7.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.51/7.72      inference('demod', [status(thm)], ['15', '18'])).
% 7.51/7.72  thf('231', plain,
% 7.51/7.72      (![X14 : $i, X15 : $i]:
% 7.51/7.72         (~ (l1_pre_topc @ X14)
% 7.51/7.72          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 7.51/7.72          | ((k2_pre_topc @ X14 @ (k2_pre_topc @ X14 @ X15))
% 7.51/7.72              = (k2_pre_topc @ X14 @ X15)))),
% 7.51/7.72      inference('cnf', [status(esa)], [projectivity_k2_pre_topc])).
% 7.51/7.72  thf('232', plain,
% 7.51/7.72      ((((k2_pre_topc @ sk_A @ 
% 7.51/7.72          (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 7.51/7.72          = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 7.51/7.72        | ~ (l1_pre_topc @ sk_A))),
% 7.51/7.72      inference('sup-', [status(thm)], ['230', '231'])).
% 7.51/7.72  thf('233', plain, ((l1_pre_topc @ sk_A)),
% 7.51/7.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.72  thf('234', plain,
% 7.51/7.72      (((k2_pre_topc @ sk_A @ 
% 7.51/7.72         (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 7.51/7.72         = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 7.51/7.72      inference('demod', [status(thm)], ['232', '233'])).
% 7.51/7.72  thf('235', plain,
% 7.51/7.72      (((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 7.51/7.72         = (k2_pre_topc @ sk_A @ sk_B))),
% 7.51/7.72      inference('demod', [status(thm)], ['102', '115'])).
% 7.51/7.72  thf('236', plain,
% 7.51/7.72      (((k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 7.51/7.72         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.51/7.72            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 7.51/7.72            (k2_pre_topc @ sk_A @ sk_B)))),
% 7.51/7.72      inference('demod', [status(thm)],
% 7.51/7.72                ['214', '215', '228', '229', '234', '235'])).
% 7.51/7.72  thf('237', plain,
% 7.51/7.72      ((m1_subset_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 7.51/7.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.51/7.72      inference('demod', [status(thm)], ['15', '18'])).
% 7.51/7.72  thf('238', plain,
% 7.51/7.72      (![X23 : $i, X24 : $i]:
% 7.51/7.72         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 7.51/7.72          | ((k2_tops_1 @ X24 @ X23)
% 7.51/7.72              = (k9_subset_1 @ (u1_struct_0 @ X24) @ 
% 7.51/7.72                 (k2_pre_topc @ X24 @ X23) @ 
% 7.51/7.72                 (k2_pre_topc @ X24 @ (k3_subset_1 @ (u1_struct_0 @ X24) @ X23))))
% 7.51/7.72          | ~ (l1_pre_topc @ X24))),
% 7.51/7.72      inference('cnf', [status(esa)], [d2_tops_1])).
% 7.51/7.72  thf('239', plain,
% 7.51/7.72      ((~ (l1_pre_topc @ sk_A)
% 7.51/7.72        | ((k2_tops_1 @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 7.51/7.72            = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.51/7.72               (k2_pre_topc @ sk_A @ 
% 7.51/7.72                (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 7.51/7.72               (k2_pre_topc @ sk_A @ 
% 7.51/7.72                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.51/7.72                 (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))))),
% 7.51/7.72      inference('sup-', [status(thm)], ['237', '238'])).
% 7.51/7.72  thf('240', plain, ((l1_pre_topc @ sk_A)),
% 7.51/7.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.72  thf('241', plain,
% 7.51/7.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.51/7.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.72  thf('242', plain,
% 7.51/7.72      (![X10 : $i, X11 : $i]:
% 7.51/7.72         (((k3_subset_1 @ X11 @ (k3_subset_1 @ X11 @ X10)) = (X10))
% 7.51/7.72          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 7.51/7.72      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 7.51/7.72  thf('243', plain,
% 7.51/7.72      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.51/7.72         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 7.51/7.72      inference('sup-', [status(thm)], ['241', '242'])).
% 7.51/7.72  thf('244', plain,
% 7.51/7.72      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 7.51/7.72         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 7.51/7.72      inference('sup-', [status(thm)], ['16', '17'])).
% 7.51/7.72  thf('245', plain,
% 7.51/7.72      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.51/7.72         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 7.51/7.72      inference('demod', [status(thm)], ['243', '244'])).
% 7.51/7.72  thf('246', plain,
% 7.51/7.72      (((k2_tops_1 @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 7.51/7.72         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.51/7.72            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 7.51/7.72            (k2_pre_topc @ sk_A @ sk_B)))),
% 7.51/7.72      inference('demod', [status(thm)], ['239', '240', '245'])).
% 7.51/7.72  thf('247', plain,
% 7.51/7.72      ((m1_subset_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 7.51/7.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.51/7.72      inference('demod', [status(thm)], ['15', '18'])).
% 7.51/7.72  thf('248', plain,
% 7.51/7.72      (![X49 : $i, X50 : $i]:
% 7.51/7.72         (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 7.51/7.72          | ((k2_tops_1 @ X50 @ X49)
% 7.51/7.72              = (k2_tops_1 @ X50 @ (k3_subset_1 @ (u1_struct_0 @ X50) @ X49)))
% 7.51/7.72          | ~ (l1_pre_topc @ X50))),
% 7.51/7.72      inference('cnf', [status(esa)], [t62_tops_1])).
% 7.51/7.72  thf('249', plain,
% 7.51/7.72      ((~ (l1_pre_topc @ sk_A)
% 7.51/7.72        | ((k2_tops_1 @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 7.51/7.72            = (k2_tops_1 @ sk_A @ 
% 7.51/7.72               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.51/7.72                (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 7.51/7.72      inference('sup-', [status(thm)], ['247', '248'])).
% 7.51/7.72  thf('250', plain, ((l1_pre_topc @ sk_A)),
% 7.51/7.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.72  thf('251', plain,
% 7.51/7.72      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.51/7.72         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 7.51/7.72      inference('demod', [status(thm)], ['243', '244'])).
% 7.51/7.72  thf('252', plain,
% 7.51/7.72      (((k2_tops_1 @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 7.51/7.72         = (k2_tops_1 @ sk_A @ sk_B))),
% 7.51/7.72      inference('demod', [status(thm)], ['249', '250', '251'])).
% 7.51/7.72  thf('253', plain,
% 7.51/7.72      (((k2_tops_1 @ sk_A @ sk_B)
% 7.51/7.72         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 7.51/7.72            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 7.51/7.72            (k2_pre_topc @ sk_A @ sk_B)))),
% 7.51/7.72      inference('demod', [status(thm)], ['246', '252'])).
% 7.51/7.72  thf('254', plain,
% 7.51/7.72      (((k2_tops_1 @ sk_A @ sk_B)
% 7.51/7.72         = (k2_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)))),
% 7.51/7.72      inference('sup+', [status(thm)], ['236', '253'])).
% 7.51/7.72  thf('255', plain,
% 7.51/7.72      (((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 7.51/7.72      inference('demod', [status(thm)], ['208', '254'])).
% 7.51/7.72  thf('256', plain,
% 7.51/7.72      (((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) != (k1_xboole_0))),
% 7.51/7.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.51/7.72  thf('257', plain, ($false),
% 7.51/7.72      inference('simplify_reflect-', [status(thm)], ['255', '256'])).
% 7.51/7.72  
% 7.51/7.72  % SZS output end Refutation
% 7.51/7.72  
% 7.51/7.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
