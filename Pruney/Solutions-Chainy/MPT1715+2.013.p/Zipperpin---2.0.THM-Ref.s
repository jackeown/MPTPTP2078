%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DxnHFH8xB4

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 541 expanded)
%              Number of leaves         :   25 ( 166 expanded)
%              Depth                    :   26
%              Number of atoms          :  872 (7405 expanded)
%              Number of equality atoms :    3 (  12 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('0',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('1',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('2',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('3',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(t24_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ( ( m1_pre_topc @ B @ C )
                   => ( ( ~ ( r1_tsep_1 @ C @ D )
                        & ~ ( r1_tsep_1 @ D @ C ) )
                      | ( ( r1_tsep_1 @ B @ D )
                        & ( r1_tsep_1 @ D @ B ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( m1_pre_topc @ B @ A ) )
           => ! [C: $i] :
                ( ( ~ ( v2_struct_0 @ C )
                  & ( m1_pre_topc @ C @ A ) )
               => ! [D: $i] :
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( m1_pre_topc @ D @ A ) )
                   => ( ( m1_pre_topc @ B @ C )
                     => ( ( ~ ( r1_tsep_1 @ C @ D )
                          & ~ ( r1_tsep_1 @ D @ C ) )
                        | ( ( r1_tsep_1 @ B @ D )
                          & ( r1_tsep_1 @ D @ B ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t24_tmap_1])).

thf('4',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_C )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['4'])).

thf(d3_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ( ( r1_tsep_1 @ A @ B )
          <=> ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_struct_0 @ X12 )
      | ~ ( r1_tsep_1 @ X13 @ X12 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('7',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( l1_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf('9',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('10',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( l1_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('11',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ~ ( l1_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['8','13'])).

thf('15',plain,
    ( ( ~ ( l1_pre_topc @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['2','14'])).

thf('16',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( l1_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('18',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['15','20'])).

thf('22',plain,(
    m1_pre_topc @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('23',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('24',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('26',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('27',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('28',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('30',plain,
    ( ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    = ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('31',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X2 @ ( k2_xboole_0 @ X3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['21','32'])).

thf('34',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_struct_0 @ X12 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X12 ) )
      | ( r1_tsep_1 @ X13 @ X12 )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('35',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_D @ sk_B )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['1','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['11','12'])).

thf('38',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['0','38'])).

thf('40',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( l1_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('42',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['39','44'])).

thf('46',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['46'])).

thf('48',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_C )
    | ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('50',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('51',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('52',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('53',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('54',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('55',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('56',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('57',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_D )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['4'])).

thf(symmetry_r1_tsep_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B ) )
     => ( ( r1_tsep_1 @ A @ B )
       => ( r1_tsep_1 @ B @ A ) ) ) )).

thf('58',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_struct_0 @ X14 )
      | ~ ( l1_struct_0 @ X15 )
      | ( r1_tsep_1 @ X15 @ X14 )
      | ~ ( r1_tsep_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('59',plain,
    ( ( ( r1_tsep_1 @ sk_D @ sk_C )
      | ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( l1_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_D @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['11','12'])).

thf('62',plain,
    ( ( ~ ( l1_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_D @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ~ ( l1_pre_topc @ sk_C )
      | ( r1_tsep_1 @ sk_D @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['55','62'])).

thf('64',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('65',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_C )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_struct_0 @ X12 )
      | ~ ( r1_tsep_1 @ X13 @ X12 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('67',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( l1_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['54','67'])).

thf('69',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['11','12'])).

thf('70',plain,
    ( ( ~ ( l1_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ~ ( l1_pre_topc @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['53','70'])).

thf('72',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['18','19'])).

thf('73',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_xboole_0 @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('75',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_struct_0 @ X12 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X12 ) )
      | ( r1_tsep_1 @ X13 @ X12 )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('77',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_D @ sk_B )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['52','77'])).

thf('79',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['11','12'])).

thf('80',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['51','80'])).

thf('82',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['42','43'])).

thf('83',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_struct_0 @ X14 )
      | ~ ( l1_struct_0 @ X15 )
      | ( r1_tsep_1 @ X15 @ X14 )
      | ~ ( r1_tsep_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('85',plain,
    ( ( ( r1_tsep_1 @ sk_B @ sk_D )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['50','85'])).

thf('87',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['42','43'])).

thf('88',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['49','88'])).

thf('90',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['11','12'])).

thf('91',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['46'])).

thf('93',plain,
    ( ~ ( r1_tsep_1 @ sk_C @ sk_D )
    | ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('95',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('96',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['39','44'])).

thf('97',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_struct_0 @ X14 )
      | ~ ( l1_struct_0 @ X15 )
      | ( r1_tsep_1 @ X15 @ X14 )
      | ~ ( r1_tsep_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('98',plain,
    ( ( ( r1_tsep_1 @ sk_B @ sk_D )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['95','98'])).

thf('100',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['42','43'])).

thf('101',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['94','101'])).

thf('103',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['11','12'])).

thf('104',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
   <= ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['46'])).

thf('106',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_C )
    | ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['46'])).

thf('108',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B )
   <= ( r1_tsep_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('109',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['46'])).

thf('110',plain,
    ( ~ ( r1_tsep_1 @ sk_C @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['4'])).

thf('112',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['48','93','106','107','110','111'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DxnHFH8xB4
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:02:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 89 iterations in 0.035s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.51  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.51  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.51  thf(dt_l1_pre_topc, axiom,
% 0.21/0.51    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.51  thf('0', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.51  thf('1', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.51  thf('2', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.51  thf('3', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.51  thf(t24_tmap_1, conjecture,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.51               ( ![D:$i]:
% 0.21/0.51                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.21/0.51                   ( ( m1_pre_topc @ B @ C ) =>
% 0.21/0.51                     ( ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.21/0.51                         ( ~( r1_tsep_1 @ D @ C ) ) ) | 
% 0.21/0.51                       ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i]:
% 0.21/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.51            ( l1_pre_topc @ A ) ) =>
% 0.21/0.51          ( ![B:$i]:
% 0.21/0.51            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.51              ( ![C:$i]:
% 0.21/0.51                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.51                  ( ![D:$i]:
% 0.21/0.51                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.21/0.51                      ( ( m1_pre_topc @ B @ C ) =>
% 0.21/0.51                        ( ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.21/0.51                            ( ~( r1_tsep_1 @ D @ C ) ) ) | 
% 0.21/0.51                          ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t24_tmap_1])).
% 0.21/0.51  thf('4', plain, (((r1_tsep_1 @ sk_C @ sk_D) | (r1_tsep_1 @ sk_D @ sk_C))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      (((r1_tsep_1 @ sk_D @ sk_C)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.51      inference('split', [status(esa)], ['4'])).
% 0.21/0.51  thf(d3_tsep_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_struct_0 @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( l1_struct_0 @ B ) =>
% 0.21/0.51           ( ( r1_tsep_1 @ A @ B ) <=>
% 0.21/0.51             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (![X12 : $i, X13 : $i]:
% 0.21/0.51         (~ (l1_struct_0 @ X12)
% 0.21/0.51          | ~ (r1_tsep_1 @ X13 @ X12)
% 0.21/0.51          | (r1_xboole_0 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X12))
% 0.21/0.51          | ~ (l1_struct_0 @ X13))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (((~ (l1_struct_0 @ sk_D)
% 0.21/0.51         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))
% 0.21/0.51         | ~ (l1_struct_0 @ sk_C))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (((~ (l1_pre_topc @ sk_D)
% 0.21/0.51         | ~ (l1_struct_0 @ sk_C)
% 0.21/0.51         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['3', '7'])).
% 0.21/0.51  thf('9', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(dt_m1_pre_topc, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (![X10 : $i, X11 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X10 @ X11)
% 0.21/0.51          | (l1_pre_topc @ X10)
% 0.21/0.51          | ~ (l1_pre_topc @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.51  thf('11', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.21/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.51  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('13', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.51      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      (((~ (l1_struct_0 @ sk_C)
% 0.21/0.51         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.51      inference('demod', [status(thm)], ['8', '13'])).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (((~ (l1_pre_topc @ sk_C)
% 0.21/0.51         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['2', '14'])).
% 0.21/0.51  thf('16', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      (![X10 : $i, X11 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X10 @ X11)
% 0.21/0.51          | (l1_pre_topc @ X10)
% 0.21/0.51          | ~ (l1_pre_topc @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.51  thf('18', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.51  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('20', plain, ((l1_pre_topc @ sk_C)),
% 0.21/0.51      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      (((r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C)))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.51      inference('demod', [status(thm)], ['15', '20'])).
% 0.21/0.51  thf('22', plain, ((m1_pre_topc @ sk_B @ sk_C)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t1_tsep_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.51           ( m1_subset_1 @
% 0.21/0.51             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.51  thf('23', plain,
% 0.21/0.51      (![X16 : $i, X17 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X16 @ X17)
% 0.21/0.51          | (m1_subset_1 @ (u1_struct_0 @ X16) @ 
% 0.21/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.21/0.51          | ~ (l1_pre_topc @ X17))),
% 0.21/0.51      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      ((~ (l1_pre_topc @ sk_C)
% 0.21/0.51        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.51  thf('25', plain, ((l1_pre_topc @ sk_C)),
% 0.21/0.51      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.21/0.51      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.51  thf(t3_subset, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      (![X6 : $i, X7 : $i]:
% 0.21/0.51         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.51  thf('28', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.51  thf(t12_xboole_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (((k2_xboole_0 @ X1 @ X0) = (X0)) | ~ (r1_tarski @ X1 @ X0))),
% 0.21/0.51      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      (((k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.21/0.51         = (u1_struct_0 @ sk_C))),
% 0.21/0.51      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.51  thf(t70_xboole_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.21/0.51            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.21/0.51       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.21/0.51            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.21/0.51         ((r1_xboole_0 @ X2 @ X3)
% 0.21/0.51          | ~ (r1_xboole_0 @ X2 @ (k2_xboole_0 @ X3 @ X5)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.21/0.51  thf('32', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_C))
% 0.21/0.51          | (r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.51  thf('33', plain,
% 0.21/0.51      (((r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['21', '32'])).
% 0.21/0.51  thf('34', plain,
% 0.21/0.51      (![X12 : $i, X13 : $i]:
% 0.21/0.51         (~ (l1_struct_0 @ X12)
% 0.21/0.51          | ~ (r1_xboole_0 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X12))
% 0.21/0.51          | (r1_tsep_1 @ X13 @ X12)
% 0.21/0.51          | ~ (l1_struct_0 @ X13))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.21/0.51  thf('35', plain,
% 0.21/0.51      (((~ (l1_struct_0 @ sk_D)
% 0.21/0.51         | (r1_tsep_1 @ sk_D @ sk_B)
% 0.21/0.51         | ~ (l1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.51  thf('36', plain,
% 0.21/0.51      (((~ (l1_pre_topc @ sk_D)
% 0.21/0.51         | ~ (l1_struct_0 @ sk_B)
% 0.21/0.51         | (r1_tsep_1 @ sk_D @ sk_B))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['1', '35'])).
% 0.21/0.51  thf('37', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.51      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.51  thf('38', plain,
% 0.21/0.51      (((~ (l1_struct_0 @ sk_B) | (r1_tsep_1 @ sk_D @ sk_B)))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.51      inference('demod', [status(thm)], ['36', '37'])).
% 0.21/0.51  thf('39', plain,
% 0.21/0.51      (((~ (l1_pre_topc @ sk_B) | (r1_tsep_1 @ sk_D @ sk_B)))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['0', '38'])).
% 0.21/0.51  thf('40', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('41', plain,
% 0.21/0.51      (![X10 : $i, X11 : $i]:
% 0.21/0.51         (~ (m1_pre_topc @ X10 @ X11)
% 0.21/0.51          | (l1_pre_topc @ X10)
% 0.21/0.51          | ~ (l1_pre_topc @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.51  thf('42', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.51  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('44', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('demod', [status(thm)], ['42', '43'])).
% 0.21/0.51  thf('45', plain,
% 0.21/0.51      (((r1_tsep_1 @ sk_D @ sk_B)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.51      inference('demod', [status(thm)], ['39', '44'])).
% 0.21/0.51  thf('46', plain,
% 0.21/0.51      ((~ (r1_tsep_1 @ sk_B @ sk_D) | ~ (r1_tsep_1 @ sk_D @ sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('47', plain,
% 0.21/0.51      ((~ (r1_tsep_1 @ sk_D @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D @ sk_B)))),
% 0.21/0.51      inference('split', [status(esa)], ['46'])).
% 0.21/0.51  thf('48', plain,
% 0.21/0.51      (~ ((r1_tsep_1 @ sk_D @ sk_C)) | ((r1_tsep_1 @ sk_D @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['45', '47'])).
% 0.21/0.51  thf('49', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.51  thf('50', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.51  thf('51', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.51  thf('52', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.51  thf('53', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.51  thf('54', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.51  thf('55', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.51  thf('56', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.51  thf('57', plain,
% 0.21/0.51      (((r1_tsep_1 @ sk_C @ sk_D)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.51      inference('split', [status(esa)], ['4'])).
% 0.21/0.51  thf(symmetry_r1_tsep_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) ) =>
% 0.21/0.51       ( ( r1_tsep_1 @ A @ B ) => ( r1_tsep_1 @ B @ A ) ) ))).
% 0.21/0.51  thf('58', plain,
% 0.21/0.51      (![X14 : $i, X15 : $i]:
% 0.21/0.51         (~ (l1_struct_0 @ X14)
% 0.21/0.51          | ~ (l1_struct_0 @ X15)
% 0.21/0.51          | (r1_tsep_1 @ X15 @ X14)
% 0.21/0.51          | ~ (r1_tsep_1 @ X14 @ X15))),
% 0.21/0.51      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.21/0.51  thf('59', plain,
% 0.21/0.51      ((((r1_tsep_1 @ sk_D @ sk_C)
% 0.21/0.51         | ~ (l1_struct_0 @ sk_D)
% 0.21/0.51         | ~ (l1_struct_0 @ sk_C))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['57', '58'])).
% 0.21/0.51  thf('60', plain,
% 0.21/0.51      (((~ (l1_pre_topc @ sk_D)
% 0.21/0.51         | ~ (l1_struct_0 @ sk_C)
% 0.21/0.51         | (r1_tsep_1 @ sk_D @ sk_C))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['56', '59'])).
% 0.21/0.51  thf('61', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.51      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.51  thf('62', plain,
% 0.21/0.51      (((~ (l1_struct_0 @ sk_C) | (r1_tsep_1 @ sk_D @ sk_C)))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.51      inference('demod', [status(thm)], ['60', '61'])).
% 0.21/0.51  thf('63', plain,
% 0.21/0.51      (((~ (l1_pre_topc @ sk_C) | (r1_tsep_1 @ sk_D @ sk_C)))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['55', '62'])).
% 0.21/0.51  thf('64', plain, ((l1_pre_topc @ sk_C)),
% 0.21/0.51      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.51  thf('65', plain,
% 0.21/0.51      (((r1_tsep_1 @ sk_D @ sk_C)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.51      inference('demod', [status(thm)], ['63', '64'])).
% 0.21/0.51  thf('66', plain,
% 0.21/0.51      (![X12 : $i, X13 : $i]:
% 0.21/0.51         (~ (l1_struct_0 @ X12)
% 0.21/0.51          | ~ (r1_tsep_1 @ X13 @ X12)
% 0.21/0.51          | (r1_xboole_0 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X12))
% 0.21/0.51          | ~ (l1_struct_0 @ X13))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.21/0.51  thf('67', plain,
% 0.21/0.51      (((~ (l1_struct_0 @ sk_D)
% 0.21/0.51         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))
% 0.21/0.51         | ~ (l1_struct_0 @ sk_C))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['65', '66'])).
% 0.21/0.51  thf('68', plain,
% 0.21/0.51      (((~ (l1_pre_topc @ sk_D)
% 0.21/0.51         | ~ (l1_struct_0 @ sk_C)
% 0.21/0.51         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['54', '67'])).
% 0.21/0.51  thf('69', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.51      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.51  thf('70', plain,
% 0.21/0.51      (((~ (l1_struct_0 @ sk_C)
% 0.21/0.51         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.51      inference('demod', [status(thm)], ['68', '69'])).
% 0.21/0.51  thf('71', plain,
% 0.21/0.51      (((~ (l1_pre_topc @ sk_C)
% 0.21/0.51         | (r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['53', '70'])).
% 0.21/0.51  thf('72', plain, ((l1_pre_topc @ sk_C)),
% 0.21/0.51      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.51  thf('73', plain,
% 0.21/0.51      (((r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C)))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.51      inference('demod', [status(thm)], ['71', '72'])).
% 0.21/0.51  thf('74', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_C))
% 0.21/0.51          | (r1_xboole_0 @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.51  thf('75', plain,
% 0.21/0.51      (((r1_xboole_0 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['73', '74'])).
% 0.21/0.51  thf('76', plain,
% 0.21/0.51      (![X12 : $i, X13 : $i]:
% 0.21/0.51         (~ (l1_struct_0 @ X12)
% 0.21/0.51          | ~ (r1_xboole_0 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X12))
% 0.21/0.51          | (r1_tsep_1 @ X13 @ X12)
% 0.21/0.51          | ~ (l1_struct_0 @ X13))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.21/0.51  thf('77', plain,
% 0.21/0.51      (((~ (l1_struct_0 @ sk_D)
% 0.21/0.51         | (r1_tsep_1 @ sk_D @ sk_B)
% 0.21/0.51         | ~ (l1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['75', '76'])).
% 0.21/0.51  thf('78', plain,
% 0.21/0.51      (((~ (l1_pre_topc @ sk_D)
% 0.21/0.51         | ~ (l1_struct_0 @ sk_B)
% 0.21/0.51         | (r1_tsep_1 @ sk_D @ sk_B))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['52', '77'])).
% 0.21/0.51  thf('79', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.51      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.51  thf('80', plain,
% 0.21/0.51      (((~ (l1_struct_0 @ sk_B) | (r1_tsep_1 @ sk_D @ sk_B)))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.51      inference('demod', [status(thm)], ['78', '79'])).
% 0.21/0.51  thf('81', plain,
% 0.21/0.51      (((~ (l1_pre_topc @ sk_B) | (r1_tsep_1 @ sk_D @ sk_B)))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['51', '80'])).
% 0.21/0.51  thf('82', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('demod', [status(thm)], ['42', '43'])).
% 0.21/0.51  thf('83', plain,
% 0.21/0.51      (((r1_tsep_1 @ sk_D @ sk_B)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.51      inference('demod', [status(thm)], ['81', '82'])).
% 0.21/0.51  thf('84', plain,
% 0.21/0.51      (![X14 : $i, X15 : $i]:
% 0.21/0.51         (~ (l1_struct_0 @ X14)
% 0.21/0.51          | ~ (l1_struct_0 @ X15)
% 0.21/0.51          | (r1_tsep_1 @ X15 @ X14)
% 0.21/0.51          | ~ (r1_tsep_1 @ X14 @ X15))),
% 0.21/0.51      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.21/0.51  thf('85', plain,
% 0.21/0.51      ((((r1_tsep_1 @ sk_B @ sk_D)
% 0.21/0.51         | ~ (l1_struct_0 @ sk_B)
% 0.21/0.51         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['83', '84'])).
% 0.21/0.51  thf('86', plain,
% 0.21/0.51      (((~ (l1_pre_topc @ sk_B)
% 0.21/0.51         | ~ (l1_struct_0 @ sk_D)
% 0.21/0.51         | (r1_tsep_1 @ sk_B @ sk_D))) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['50', '85'])).
% 0.21/0.51  thf('87', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('demod', [status(thm)], ['42', '43'])).
% 0.21/0.51  thf('88', plain,
% 0.21/0.51      (((~ (l1_struct_0 @ sk_D) | (r1_tsep_1 @ sk_B @ sk_D)))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.51      inference('demod', [status(thm)], ['86', '87'])).
% 0.21/0.51  thf('89', plain,
% 0.21/0.51      (((~ (l1_pre_topc @ sk_D) | (r1_tsep_1 @ sk_B @ sk_D)))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['49', '88'])).
% 0.21/0.51  thf('90', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.51      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.51  thf('91', plain,
% 0.21/0.51      (((r1_tsep_1 @ sk_B @ sk_D)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.51      inference('demod', [status(thm)], ['89', '90'])).
% 0.21/0.51  thf('92', plain,
% 0.21/0.51      ((~ (r1_tsep_1 @ sk_B @ sk_D)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D)))),
% 0.21/0.51      inference('split', [status(esa)], ['46'])).
% 0.21/0.51  thf('93', plain,
% 0.21/0.51      (~ ((r1_tsep_1 @ sk_C @ sk_D)) | ((r1_tsep_1 @ sk_B @ sk_D))),
% 0.21/0.51      inference('sup-', [status(thm)], ['91', '92'])).
% 0.21/0.51  thf('94', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.51  thf('95', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.51  thf('96', plain,
% 0.21/0.51      (((r1_tsep_1 @ sk_D @ sk_B)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.51      inference('demod', [status(thm)], ['39', '44'])).
% 0.21/0.51  thf('97', plain,
% 0.21/0.51      (![X14 : $i, X15 : $i]:
% 0.21/0.51         (~ (l1_struct_0 @ X14)
% 0.21/0.51          | ~ (l1_struct_0 @ X15)
% 0.21/0.51          | (r1_tsep_1 @ X15 @ X14)
% 0.21/0.51          | ~ (r1_tsep_1 @ X14 @ X15))),
% 0.21/0.51      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.21/0.51  thf('98', plain,
% 0.21/0.51      ((((r1_tsep_1 @ sk_B @ sk_D)
% 0.21/0.51         | ~ (l1_struct_0 @ sk_B)
% 0.21/0.51         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['96', '97'])).
% 0.21/0.51  thf('99', plain,
% 0.21/0.51      (((~ (l1_pre_topc @ sk_B)
% 0.21/0.51         | ~ (l1_struct_0 @ sk_D)
% 0.21/0.51         | (r1_tsep_1 @ sk_B @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['95', '98'])).
% 0.21/0.51  thf('100', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.51      inference('demod', [status(thm)], ['42', '43'])).
% 0.21/0.51  thf('101', plain,
% 0.21/0.51      (((~ (l1_struct_0 @ sk_D) | (r1_tsep_1 @ sk_B @ sk_D)))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.51      inference('demod', [status(thm)], ['99', '100'])).
% 0.21/0.51  thf('102', plain,
% 0.21/0.51      (((~ (l1_pre_topc @ sk_D) | (r1_tsep_1 @ sk_B @ sk_D)))
% 0.21/0.51         <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['94', '101'])).
% 0.21/0.51  thf('103', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.51      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.51  thf('104', plain,
% 0.21/0.51      (((r1_tsep_1 @ sk_B @ sk_D)) <= (((r1_tsep_1 @ sk_D @ sk_C)))),
% 0.21/0.51      inference('demod', [status(thm)], ['102', '103'])).
% 0.21/0.51  thf('105', plain,
% 0.21/0.51      ((~ (r1_tsep_1 @ sk_B @ sk_D)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D)))),
% 0.21/0.51      inference('split', [status(esa)], ['46'])).
% 0.21/0.51  thf('106', plain,
% 0.21/0.51      (~ ((r1_tsep_1 @ sk_D @ sk_C)) | ((r1_tsep_1 @ sk_B @ sk_D))),
% 0.21/0.51      inference('sup-', [status(thm)], ['104', '105'])).
% 0.21/0.51  thf('107', plain,
% 0.21/0.51      (~ ((r1_tsep_1 @ sk_D @ sk_B)) | ~ ((r1_tsep_1 @ sk_B @ sk_D))),
% 0.21/0.51      inference('split', [status(esa)], ['46'])).
% 0.21/0.51  thf('108', plain,
% 0.21/0.51      (((r1_tsep_1 @ sk_D @ sk_B)) <= (((r1_tsep_1 @ sk_C @ sk_D)))),
% 0.21/0.51      inference('demod', [status(thm)], ['81', '82'])).
% 0.21/0.51  thf('109', plain,
% 0.21/0.51      ((~ (r1_tsep_1 @ sk_D @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D @ sk_B)))),
% 0.21/0.51      inference('split', [status(esa)], ['46'])).
% 0.21/0.51  thf('110', plain,
% 0.21/0.51      (~ ((r1_tsep_1 @ sk_C @ sk_D)) | ((r1_tsep_1 @ sk_D @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['108', '109'])).
% 0.21/0.51  thf('111', plain,
% 0.21/0.51      (((r1_tsep_1 @ sk_C @ sk_D)) | ((r1_tsep_1 @ sk_D @ sk_C))),
% 0.21/0.51      inference('split', [status(esa)], ['4'])).
% 0.21/0.51  thf('112', plain, ($false),
% 0.21/0.51      inference('sat_resolution*', [status(thm)],
% 0.21/0.51                ['48', '93', '106', '107', '110', '111'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
