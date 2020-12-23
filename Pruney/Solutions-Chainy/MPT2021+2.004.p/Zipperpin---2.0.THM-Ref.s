%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.S1BKa9xyBm

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:24 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 162 expanded)
%              Number of leaves         :   21 (  56 expanded)
%              Depth                    :   11
%              Number of atoms          :  690 (2721 expanded)
%              Number of equality atoms :   35 ( 157 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_tops_2_type,type,(
    v2_tops_2: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(t20_waybel_9,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) )
                 => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                        = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                      & ( C = D )
                      & ( v2_tops_2 @ C @ A ) )
                   => ( v2_tops_2 @ D @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( l1_pre_topc @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) )
                   => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                          = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                        & ( C = D )
                        & ( v2_tops_2 @ C @ A ) )
                     => ( v2_tops_2 @ D @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t20_waybel_9])).

thf('0',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    sk_C = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(dt_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('4',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t78_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_tops_2 @ B @ A )
          <=> ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( r1_tarski @ X11 @ ( u1_pre_topc @ X12 ) )
      | ( v1_tops_2 @ X11 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B )
    | ~ ( r1_tarski @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B )
    | ~ ( r1_tarski @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('10',plain,(
    ! [X4: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X4 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) ) )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(free_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_pre_topc @ A @ B )
            = ( g1_pre_topc @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('11',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( ( g1_pre_topc @ X7 @ X8 )
       != ( g1_pre_topc @ X5 @ X6 ) )
      | ( X8 = X6 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( g1_pre_topc @ X1 @ X0 ) )
      | ( ( u1_pre_topc @ sk_B )
        = X0 )
      | ~ ( l1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( g1_pre_topc @ X1 @ X0 ) )
      | ( ( u1_pre_topc @ sk_B )
        = X0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( u1_pre_topc @ sk_B )
    = ( u1_pre_topc @ sk_A ) ),
    inference(eq_res,[status(thm)],['15'])).

thf('17',plain,
    ( ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B )
    | ~ ( r1_tarski @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','16'])).

thf('18',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t17_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_tops_2 @ B @ A )
          <=> ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('19',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( v1_tops_2 @ X9 @ X10 )
      | ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ X10 ) @ X9 ) @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t17_tops_2])).

thf('20',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_B ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_B )
    | ~ ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(involutiveness_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
        = B ) ) )).

thf('23',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k7_setfam_1 @ X3 @ ( k7_setfam_1 @ X3 @ X2 ) )
        = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k7_setfam_1])).

thf('24',plain,
    ( ( k7_setfam_1 @ ( u1_struct_0 @ sk_B ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( v2_tops_2 @ sk_C @ sk_B )
    | ~ ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['20','21','24'])).

thf('26',plain,(
    ~ ( v2_tops_2 @ sk_D @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    sk_C = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ~ ( v2_tops_2 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ~ ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ sk_B ) ),
    inference(clc,[status(thm)],['25','28'])).

thf('30',plain,(
    ~ ( r1_tarski @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(clc,[status(thm)],['17','29'])).

thf('31',plain,
    ( ( u1_pre_topc @ sk_B )
    = ( u1_pre_topc @ sk_A ) ),
    inference(eq_res,[status(thm)],['15'])).

thf('32',plain,(
    ! [X4: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X4 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) ) )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('33',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( ( g1_pre_topc @ X7 @ X8 )
       != ( g1_pre_topc @ X5 @ X6 ) )
      | ( X7 = X5 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_B )
        = X0 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
       != ( g1_pre_topc @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( u1_pre_topc @ sk_B )
    = ( u1_pre_topc @ sk_A ) ),
    inference(eq_res,[status(thm)],['15'])).

thf('40',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_B )
        = X0 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( g1_pre_topc @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['37','40'])).

thf('42',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['41'])).

thf('43',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('45',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( v1_tops_2 @ X11 @ X12 )
      | ( r1_tarski @ X11 @ ( u1_pre_topc @ X12 ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('47',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('50',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ X10 ) @ X9 ) @ X10 )
      | ( v1_tops_2 @ X9 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t17_tops_2])).

thf('51',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A )
    | ~ ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k7_setfam_1 @ X3 @ ( k7_setfam_1 @ X3 @ X2 ) )
        = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k7_setfam_1])).

thf('55',plain,
    ( ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v2_tops_2 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['51','52','55','56'])).

thf('58',plain,(
    r1_tarski @ ( k7_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['47','48','57'])).

thf('59',plain,(
    $false ),
    inference(demod,[status(thm)],['30','42','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.S1BKa9xyBm
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:10:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.37/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.56  % Solved by: fo/fo7.sh
% 0.37/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.56  % done 139 iterations in 0.087s
% 0.37/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.56  % SZS output start Refutation
% 0.37/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.56  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.37/0.56  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.37/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.37/0.56  thf(v2_tops_2_type, type, v2_tops_2: $i > $i > $o).
% 0.37/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.56  thf(sk_D_type, type, sk_D: $i).
% 0.37/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.56  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.37/0.56  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.37/0.56  thf(t20_waybel_9, conjecture,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( l1_pre_topc @ A ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( l1_pre_topc @ B ) =>
% 0.37/0.56           ( ![C:$i]:
% 0.37/0.56             ( ( m1_subset_1 @
% 0.37/0.56                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.56               ( ![D:$i]:
% 0.37/0.56                 ( ( m1_subset_1 @
% 0.37/0.56                     D @ 
% 0.37/0.56                     ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.37/0.56                   ( ( ( ( g1_pre_topc @
% 0.37/0.56                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.37/0.56                         ( g1_pre_topc @
% 0.37/0.56                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.37/0.56                       ( ( C ) = ( D ) ) & ( v2_tops_2 @ C @ A ) ) =>
% 0.37/0.56                     ( v2_tops_2 @ D @ B ) ) ) ) ) ) ) ) ))).
% 0.37/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.56    (~( ![A:$i]:
% 0.37/0.56        ( ( l1_pre_topc @ A ) =>
% 0.37/0.56          ( ![B:$i]:
% 0.37/0.56            ( ( l1_pre_topc @ B ) =>
% 0.37/0.56              ( ![C:$i]:
% 0.37/0.56                ( ( m1_subset_1 @
% 0.37/0.56                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.56                  ( ![D:$i]:
% 0.37/0.56                    ( ( m1_subset_1 @
% 0.37/0.56                        D @ 
% 0.37/0.56                        ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.37/0.56                      ( ( ( ( g1_pre_topc @
% 0.37/0.56                              ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.37/0.56                            ( g1_pre_topc @
% 0.37/0.56                              ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.37/0.56                          ( ( C ) = ( D ) ) & ( v2_tops_2 @ C @ A ) ) =>
% 0.37/0.56                        ( v2_tops_2 @ D @ B ) ) ) ) ) ) ) ) ) )),
% 0.37/0.56    inference('cnf.neg', [status(esa)], [t20_waybel_9])).
% 0.37/0.56  thf('0', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_D @ 
% 0.37/0.56        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('1', plain, (((sk_C) = (sk_D))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('2', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_C @ 
% 0.37/0.56        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.37/0.56      inference('demod', [status(thm)], ['0', '1'])).
% 0.37/0.56  thf(dt_k7_setfam_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.37/0.56       ( m1_subset_1 @
% 0.37/0.56         ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.37/0.56  thf('3', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((m1_subset_1 @ (k7_setfam_1 @ X0 @ X1) @ 
% 0.37/0.56           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))
% 0.37/0.56          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0))))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 0.37/0.56  thf('4', plain,
% 0.37/0.56      ((m1_subset_1 @ (k7_setfam_1 @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.37/0.56        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['2', '3'])).
% 0.37/0.56  thf(t78_tops_2, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( l1_pre_topc @ A ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( m1_subset_1 @
% 0.37/0.56             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.56           ( ( v1_tops_2 @ B @ A ) <=> ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.37/0.56  thf('5', plain,
% 0.37/0.56      (![X11 : $i, X12 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X11 @ 
% 0.37/0.56             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12))))
% 0.37/0.56          | ~ (r1_tarski @ X11 @ (u1_pre_topc @ X12))
% 0.37/0.56          | (v1_tops_2 @ X11 @ X12)
% 0.37/0.56          | ~ (l1_pre_topc @ X12))),
% 0.37/0.56      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.37/0.56  thf('6', plain,
% 0.37/0.56      ((~ (l1_pre_topc @ sk_B)
% 0.37/0.56        | (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_B) @ sk_C) @ sk_B)
% 0.37/0.56        | ~ (r1_tarski @ (k7_setfam_1 @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.37/0.56             (u1_pre_topc @ sk_B)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['4', '5'])).
% 0.37/0.56  thf('7', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('8', plain,
% 0.37/0.56      (((v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_B) @ sk_C) @ sk_B)
% 0.37/0.56        | ~ (r1_tarski @ (k7_setfam_1 @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.37/0.56             (u1_pre_topc @ sk_B)))),
% 0.37/0.56      inference('demod', [status(thm)], ['6', '7'])).
% 0.37/0.56  thf('9', plain,
% 0.37/0.56      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.56         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(dt_u1_pre_topc, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( l1_pre_topc @ A ) =>
% 0.37/0.56       ( m1_subset_1 @
% 0.37/0.56         ( u1_pre_topc @ A ) @ 
% 0.37/0.56         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.37/0.56  thf('10', plain,
% 0.37/0.56      (![X4 : $i]:
% 0.37/0.56         ((m1_subset_1 @ (u1_pre_topc @ X4) @ 
% 0.37/0.56           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4))))
% 0.37/0.56          | ~ (l1_pre_topc @ X4))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.37/0.56  thf(free_g1_pre_topc, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.37/0.56       ( ![C:$i,D:$i]:
% 0.37/0.56         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 0.37/0.56           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.37/0.56  thf('11', plain,
% 0.37/0.56      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.37/0.56         (((g1_pre_topc @ X7 @ X8) != (g1_pre_topc @ X5 @ X6))
% 0.37/0.56          | ((X8) = (X6))
% 0.37/0.56          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X7))))),
% 0.37/0.56      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.37/0.56  thf('12', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.56         (~ (l1_pre_topc @ X0)
% 0.37/0.56          | ((u1_pre_topc @ X0) = (X1))
% 0.37/0.56          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.37/0.56              != (g1_pre_topc @ X2 @ X1)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['10', '11'])).
% 0.37/0.56  thf('13', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.56            != (g1_pre_topc @ X1 @ X0))
% 0.37/0.56          | ((u1_pre_topc @ sk_B) = (X0))
% 0.37/0.56          | ~ (l1_pre_topc @ sk_B))),
% 0.37/0.56      inference('sup-', [status(thm)], ['9', '12'])).
% 0.37/0.56  thf('14', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('15', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.56            != (g1_pre_topc @ X1 @ X0))
% 0.37/0.56          | ((u1_pre_topc @ sk_B) = (X0)))),
% 0.37/0.56      inference('demod', [status(thm)], ['13', '14'])).
% 0.37/0.56  thf('16', plain, (((u1_pre_topc @ sk_B) = (u1_pre_topc @ sk_A))),
% 0.37/0.56      inference('eq_res', [status(thm)], ['15'])).
% 0.37/0.56  thf('17', plain,
% 0.37/0.56      (((v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_B) @ sk_C) @ sk_B)
% 0.37/0.56        | ~ (r1_tarski @ (k7_setfam_1 @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.37/0.56             (u1_pre_topc @ sk_A)))),
% 0.37/0.56      inference('demod', [status(thm)], ['8', '16'])).
% 0.37/0.56  thf('18', plain,
% 0.37/0.56      ((m1_subset_1 @ (k7_setfam_1 @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.37/0.56        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['2', '3'])).
% 0.37/0.56  thf(t17_tops_2, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( l1_pre_topc @ A ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( m1_subset_1 @
% 0.37/0.56             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.56           ( ( v1_tops_2 @ B @ A ) <=>
% 0.37/0.56             ( v2_tops_2 @ ( k7_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.37/0.56  thf('19', plain,
% 0.37/0.56      (![X9 : $i, X10 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X9 @ 
% 0.37/0.56             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10))))
% 0.37/0.56          | ~ (v1_tops_2 @ X9 @ X10)
% 0.37/0.56          | (v2_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ X10) @ X9) @ X10)
% 0.37/0.56          | ~ (l1_pre_topc @ X10))),
% 0.37/0.56      inference('cnf', [status(esa)], [t17_tops_2])).
% 0.37/0.56  thf('20', plain,
% 0.37/0.56      ((~ (l1_pre_topc @ sk_B)
% 0.37/0.56        | (v2_tops_2 @ 
% 0.37/0.56           (k7_setfam_1 @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.56            (k7_setfam_1 @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.37/0.56           sk_B)
% 0.37/0.56        | ~ (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_B) @ sk_C) @ sk_B))),
% 0.37/0.56      inference('sup-', [status(thm)], ['18', '19'])).
% 0.37/0.56  thf('21', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('22', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_C @ 
% 0.37/0.56        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.37/0.56      inference('demod', [status(thm)], ['0', '1'])).
% 0.37/0.56  thf(involutiveness_k7_setfam_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.37/0.56       ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) = ( B ) ) ))).
% 0.37/0.56  thf('23', plain,
% 0.37/0.56      (![X2 : $i, X3 : $i]:
% 0.37/0.56         (((k7_setfam_1 @ X3 @ (k7_setfam_1 @ X3 @ X2)) = (X2))
% 0.37/0.56          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X3))))),
% 0.37/0.56      inference('cnf', [status(esa)], [involutiveness_k7_setfam_1])).
% 0.37/0.56  thf('24', plain,
% 0.37/0.56      (((k7_setfam_1 @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.56         (k7_setfam_1 @ (u1_struct_0 @ sk_B) @ sk_C)) = (sk_C))),
% 0.37/0.56      inference('sup-', [status(thm)], ['22', '23'])).
% 0.37/0.56  thf('25', plain,
% 0.37/0.56      (((v2_tops_2 @ sk_C @ sk_B)
% 0.37/0.56        | ~ (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_B) @ sk_C) @ sk_B))),
% 0.37/0.56      inference('demod', [status(thm)], ['20', '21', '24'])).
% 0.37/0.56  thf('26', plain, (~ (v2_tops_2 @ sk_D @ sk_B)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('27', plain, (((sk_C) = (sk_D))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('28', plain, (~ (v2_tops_2 @ sk_C @ sk_B)),
% 0.37/0.56      inference('demod', [status(thm)], ['26', '27'])).
% 0.37/0.56  thf('29', plain,
% 0.37/0.56      (~ (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_B) @ sk_C) @ sk_B)),
% 0.37/0.56      inference('clc', [status(thm)], ['25', '28'])).
% 0.37/0.56  thf('30', plain,
% 0.37/0.56      (~ (r1_tarski @ (k7_setfam_1 @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.37/0.56          (u1_pre_topc @ sk_A))),
% 0.37/0.56      inference('clc', [status(thm)], ['17', '29'])).
% 0.37/0.56  thf('31', plain, (((u1_pre_topc @ sk_B) = (u1_pre_topc @ sk_A))),
% 0.37/0.56      inference('eq_res', [status(thm)], ['15'])).
% 0.37/0.56  thf('32', plain,
% 0.37/0.56      (![X4 : $i]:
% 0.37/0.56         ((m1_subset_1 @ (u1_pre_topc @ X4) @ 
% 0.37/0.56           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4))))
% 0.37/0.56          | ~ (l1_pre_topc @ X4))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.37/0.56  thf('33', plain,
% 0.37/0.56      (((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.37/0.56         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))
% 0.37/0.56        | ~ (l1_pre_topc @ sk_B))),
% 0.37/0.56      inference('sup+', [status(thm)], ['31', '32'])).
% 0.37/0.56  thf('34', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('35', plain,
% 0.37/0.56      ((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.37/0.56        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.37/0.56      inference('demod', [status(thm)], ['33', '34'])).
% 0.37/0.56  thf('36', plain,
% 0.37/0.56      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.37/0.56         (((g1_pre_topc @ X7 @ X8) != (g1_pre_topc @ X5 @ X6))
% 0.37/0.56          | ((X7) = (X5))
% 0.37/0.56          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X7))))),
% 0.37/0.56      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.37/0.56  thf('37', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (((u1_struct_0 @ sk_B) = (X0))
% 0.37/0.56          | ((g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.37/0.56              != (g1_pre_topc @ X0 @ X1)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['35', '36'])).
% 0.37/0.56  thf('38', plain,
% 0.37/0.56      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.56         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('39', plain, (((u1_pre_topc @ sk_B) = (u1_pre_topc @ sk_A))),
% 0.37/0.56      inference('eq_res', [status(thm)], ['15'])).
% 0.37/0.56  thf('40', plain,
% 0.37/0.56      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.56         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 0.37/0.56      inference('demod', [status(thm)], ['38', '39'])).
% 0.37/0.56  thf('41', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         (((u1_struct_0 @ sk_B) = (X0))
% 0.37/0.56          | ((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.37/0.56              != (g1_pre_topc @ X0 @ X1)))),
% 0.37/0.56      inference('demod', [status(thm)], ['37', '40'])).
% 0.37/0.56  thf('42', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.37/0.56      inference('eq_res', [status(thm)], ['41'])).
% 0.37/0.56  thf('43', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_C @ 
% 0.37/0.56        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('44', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((m1_subset_1 @ (k7_setfam_1 @ X0 @ X1) @ 
% 0.37/0.56           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))
% 0.37/0.56          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0))))),
% 0.37/0.56      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 0.37/0.56  thf('45', plain,
% 0.37/0.56      ((m1_subset_1 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.37/0.56        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['43', '44'])).
% 0.37/0.56  thf('46', plain,
% 0.37/0.56      (![X11 : $i, X12 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X11 @ 
% 0.37/0.56             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12))))
% 0.37/0.56          | ~ (v1_tops_2 @ X11 @ X12)
% 0.37/0.56          | (r1_tarski @ X11 @ (u1_pre_topc @ X12))
% 0.37/0.56          | ~ (l1_pre_topc @ X12))),
% 0.37/0.56      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.37/0.56  thf('47', plain,
% 0.37/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.56        | (r1_tarski @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.37/0.56           (u1_pre_topc @ sk_A))
% 0.37/0.56        | ~ (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['45', '46'])).
% 0.37/0.56  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('49', plain,
% 0.37/0.56      ((m1_subset_1 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.37/0.56        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['43', '44'])).
% 0.37/0.56  thf('50', plain,
% 0.37/0.56      (![X9 : $i, X10 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X9 @ 
% 0.37/0.56             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10))))
% 0.37/0.56          | ~ (v2_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ X10) @ X9) @ X10)
% 0.37/0.56          | (v1_tops_2 @ X9 @ X10)
% 0.37/0.56          | ~ (l1_pre_topc @ X10))),
% 0.37/0.56      inference('cnf', [status(esa)], [t17_tops_2])).
% 0.37/0.56  thf('51', plain,
% 0.37/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.56        | (v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A)
% 0.37/0.56        | ~ (v2_tops_2 @ 
% 0.37/0.56             (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.56              (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C)) @ 
% 0.37/0.56             sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['49', '50'])).
% 0.37/0.56  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('53', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_C @ 
% 0.37/0.56        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('54', plain,
% 0.37/0.56      (![X2 : $i, X3 : $i]:
% 0.37/0.56         (((k7_setfam_1 @ X3 @ (k7_setfam_1 @ X3 @ X2)) = (X2))
% 0.37/0.56          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X3))))),
% 0.37/0.56      inference('cnf', [status(esa)], [involutiveness_k7_setfam_1])).
% 0.37/0.56  thf('55', plain,
% 0.37/0.56      (((k7_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.56         (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C)) = (sk_C))),
% 0.37/0.56      inference('sup-', [status(thm)], ['53', '54'])).
% 0.37/0.56  thf('56', plain, ((v2_tops_2 @ sk_C @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('57', plain,
% 0.37/0.56      ((v1_tops_2 @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A)),
% 0.37/0.56      inference('demod', [status(thm)], ['51', '52', '55', '56'])).
% 0.37/0.56  thf('58', plain,
% 0.37/0.56      ((r1_tarski @ (k7_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.37/0.56        (u1_pre_topc @ sk_A))),
% 0.37/0.56      inference('demod', [status(thm)], ['47', '48', '57'])).
% 0.37/0.56  thf('59', plain, ($false),
% 0.37/0.56      inference('demod', [status(thm)], ['30', '42', '58'])).
% 0.37/0.56  
% 0.37/0.56  % SZS output end Refutation
% 0.37/0.56  
% 0.37/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
