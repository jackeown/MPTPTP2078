%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.37GT2WhOU5

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:23 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 416 expanded)
%              Number of leaves         :   24 ( 126 expanded)
%              Depth                    :   15
%              Number of atoms          :  786 (6855 expanded)
%              Number of equality atoms :   15 ( 293 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_tops_2_type,type,(
    v2_tops_2: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    sk_C_1 = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(d2_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v2_tops_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( r2_hidden @ C @ B )
                 => ( v4_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( v4_pre_topc @ ( sk_C @ X7 @ X8 ) @ X8 )
      | ( v2_tops_2 @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_2])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v2_tops_2 @ sk_C_1 @ sk_B )
    | ~ ( v4_pre_topc @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v2_tops_2 @ sk_C_1 @ sk_B )
    | ~ ( v4_pre_topc @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ~ ( v2_tops_2 @ sk_D @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    sk_C_1 = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ~ ( v2_tops_2 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( v4_pre_topc @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_B ) ),
    inference(clc,[status(thm)],['6','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('12',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) ) )
      | ( m1_subset_1 @ ( sk_C @ X7 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( v2_tops_2 @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_2])).

thf('13',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v2_tops_2 @ sk_C_1 @ sk_B )
    | ( m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v2_tops_2 @ sk_C_1 @ sk_B )
    | ( m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ~ ( v2_tops_2 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('17',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('18',plain,(
    ! [X14: $i] :
      ( ( m1_pre_topc @ X14 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( m1_pre_topc @ X6 @ X5 )
      | ( m1_pre_topc @ X6 @ ( g1_pre_topc @ ( u1_struct_0 @ X5 ) @ ( u1_pre_topc @ X5 ) ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ ( g1_pre_topc @ ( u1_struct_0 @ X4 ) @ ( u1_pre_topc @ X4 ) ) )
      | ( m1_pre_topc @ X3 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( m1_pre_topc @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( m1_pre_topc @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_pre_topc @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['27','28'])).

thf(t35_borsuk_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('30',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( r1_tarski @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('31',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('34',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('38',plain,
    ( ( m1_pre_topc @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_pre_topc @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ ( g1_pre_topc @ ( u1_struct_0 @ X4 ) @ ( u1_pre_topc @ X4 ) ) )
      | ( m1_pre_topc @ X3 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('42',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( r1_tarski @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('46',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['35','48'])).

thf('50',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','49'])).

thf('51',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','49'])).

thf('52',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['35','48'])).

thf(t34_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( v4_pre_topc @ B @ A )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) )
                   => ( ( D = B )
                     => ( v4_pre_topc @ D @ C ) ) ) ) ) ) ) )).

thf('53',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v4_pre_topc @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v4_pre_topc @ X12 @ X13 )
      | ( X12 != X10 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t34_tops_2])).

thf('54',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_pre_topc @ X13 @ X11 )
      | ( v4_pre_topc @ X10 @ X13 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v4_pre_topc @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( v4_pre_topc @ X0 @ X1 )
      | ( v4_pre_topc @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['52','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( v4_pre_topc @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_B )
      | ~ ( v4_pre_topc @ ( sk_C @ sk_C_1 @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['51','55'])).

thf('57',plain,
    ( ~ ( v4_pre_topc @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_A )
    | ( v4_pre_topc @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['50','56'])).

thf('58',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','49'])).

thf('59',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( v2_tops_2 @ X7 @ X8 )
      | ~ ( r2_hidden @ X9 @ X7 )
      | ( v4_pre_topc @ X9 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_2])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( v2_tops_2 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v2_tops_2 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,
    ( ~ ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 )
    | ( v4_pre_topc @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['58','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('67',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) ) )
      | ( r2_hidden @ ( sk_C @ X7 @ X8 ) @ X7 )
      | ( v2_tops_2 @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_2])).

thf('68',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v2_tops_2 @ sk_C_1 @ sk_B )
    | ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( v2_tops_2 @ sk_C_1 @ sk_B )
    | ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ~ ( v2_tops_2 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('72',plain,(
    r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,(
    v4_pre_topc @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['65','72'])).

thf('74',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['42','43'])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v4_pre_topc @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['57','73','74','75'])).

thf('77',plain,(
    $false ),
    inference(demod,[status(thm)],['10','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.37GT2WhOU5
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:51:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 73 iterations in 0.038s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.49  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.21/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.49  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.49  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(v2_tops_2_type, type, v2_tops_2: $i > $i > $o).
% 0.21/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.49  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.21/0.49  thf(t20_waybel_9, conjecture,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_pre_topc @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( l1_pre_topc @ B ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( m1_subset_1 @
% 0.21/0.49                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.49               ( ![D:$i]:
% 0.21/0.49                 ( ( m1_subset_1 @
% 0.21/0.49                     D @ 
% 0.21/0.49                     ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.21/0.49                   ( ( ( ( g1_pre_topc @
% 0.21/0.49                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.21/0.49                         ( g1_pre_topc @
% 0.21/0.49                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.21/0.49                       ( ( C ) = ( D ) ) & ( v2_tops_2 @ C @ A ) ) =>
% 0.21/0.49                     ( v2_tops_2 @ D @ B ) ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]:
% 0.21/0.49        ( ( l1_pre_topc @ A ) =>
% 0.21/0.49          ( ![B:$i]:
% 0.21/0.49            ( ( l1_pre_topc @ B ) =>
% 0.21/0.49              ( ![C:$i]:
% 0.21/0.49                ( ( m1_subset_1 @
% 0.21/0.49                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.49                  ( ![D:$i]:
% 0.21/0.49                    ( ( m1_subset_1 @
% 0.21/0.49                        D @ 
% 0.21/0.49                        ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.21/0.49                      ( ( ( ( g1_pre_topc @
% 0.21/0.49                              ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.21/0.49                            ( g1_pre_topc @
% 0.21/0.49                              ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.21/0.49                          ( ( C ) = ( D ) ) & ( v2_tops_2 @ C @ A ) ) =>
% 0.21/0.49                        ( v2_tops_2 @ D @ B ) ) ) ) ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t20_waybel_9])).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_D @ 
% 0.21/0.49        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('1', plain, (((sk_C_1) = (sk_D))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_C_1 @ 
% 0.21/0.49        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.21/0.49      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.49  thf(d2_tops_2, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_pre_topc @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @
% 0.21/0.49             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.49           ( ( v2_tops_2 @ B @ A ) <=>
% 0.21/0.49             ( ![C:$i]:
% 0.21/0.49               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49                 ( ( r2_hidden @ C @ B ) => ( v4_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X7 @ 
% 0.21/0.49             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8))))
% 0.21/0.49          | ~ (v4_pre_topc @ (sk_C @ X7 @ X8) @ X8)
% 0.21/0.49          | (v2_tops_2 @ X7 @ X8)
% 0.21/0.49          | ~ (l1_pre_topc @ X8))),
% 0.21/0.49      inference('cnf', [status(esa)], [d2_tops_2])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      ((~ (l1_pre_topc @ sk_B)
% 0.21/0.49        | (v2_tops_2 @ sk_C_1 @ sk_B)
% 0.21/0.49        | ~ (v4_pre_topc @ (sk_C @ sk_C_1 @ sk_B) @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.49  thf('5', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (((v2_tops_2 @ sk_C_1 @ sk_B)
% 0.21/0.49        | ~ (v4_pre_topc @ (sk_C @ sk_C_1 @ sk_B) @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.49  thf('7', plain, (~ (v2_tops_2 @ sk_D @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('8', plain, (((sk_C_1) = (sk_D))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('9', plain, (~ (v2_tops_2 @ sk_C_1 @ sk_B)),
% 0.21/0.49      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.49  thf('10', plain, (~ (v4_pre_topc @ (sk_C @ sk_C_1 @ sk_B) @ sk_B)),
% 0.21/0.49      inference('clc', [status(thm)], ['6', '9'])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_C_1 @ 
% 0.21/0.49        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.21/0.49      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X7 @ 
% 0.21/0.49             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8))))
% 0.21/0.49          | (m1_subset_1 @ (sk_C @ X7 @ X8) @ 
% 0.21/0.49             (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.49          | (v2_tops_2 @ X7 @ X8)
% 0.21/0.49          | ~ (l1_pre_topc @ X8))),
% 0.21/0.49      inference('cnf', [status(esa)], [d2_tops_2])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      ((~ (l1_pre_topc @ sk_B)
% 0.21/0.49        | (v2_tops_2 @ sk_C_1 @ sk_B)
% 0.21/0.49        | (m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.21/0.49           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.49  thf('14', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (((v2_tops_2 @ sk_C_1 @ sk_B)
% 0.21/0.49        | (m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.21/0.49           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.21/0.49      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.49  thf('16', plain, (~ (v2_tops_2 @ sk_C_1 @ sk_B)),
% 0.21/0.49      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      ((m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.21/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.49      inference('clc', [status(thm)], ['15', '16'])).
% 0.21/0.49  thf(t2_tsep_1, axiom,
% 0.21/0.49    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      (![X14 : $i]: ((m1_pre_topc @ X14 @ X14) | ~ (l1_pre_topc @ X14))),
% 0.21/0.49      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.21/0.49  thf(t65_pre_topc, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_pre_topc @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( l1_pre_topc @ B ) =>
% 0.21/0.49           ( ( m1_pre_topc @ A @ B ) <=>
% 0.21/0.49             ( m1_pre_topc @
% 0.21/0.49               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (![X5 : $i, X6 : $i]:
% 0.21/0.49         (~ (l1_pre_topc @ X5)
% 0.21/0.49          | ~ (m1_pre_topc @ X6 @ X5)
% 0.21/0.49          | (m1_pre_topc @ X6 @ 
% 0.21/0.49             (g1_pre_topc @ (u1_struct_0 @ X5) @ (u1_pre_topc @ X5)))
% 0.21/0.49          | ~ (l1_pre_topc @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (l1_pre_topc @ X0)
% 0.21/0.49          | ~ (l1_pre_topc @ X0)
% 0.21/0.49          | (m1_pre_topc @ X0 @ 
% 0.21/0.49             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.21/0.49          | ~ (l1_pre_topc @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((m1_pre_topc @ X0 @ 
% 0.21/0.49           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.21/0.49          | ~ (l1_pre_topc @ X0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.49         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t59_pre_topc, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_pre_topc @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_pre_topc @
% 0.21/0.49             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.21/0.49           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      (![X3 : $i, X4 : $i]:
% 0.21/0.49         (~ (m1_pre_topc @ X3 @ 
% 0.21/0.49             (g1_pre_topc @ (u1_struct_0 @ X4) @ (u1_pre_topc @ X4)))
% 0.21/0.49          | (m1_pre_topc @ X3 @ X4)
% 0.21/0.49          | ~ (l1_pre_topc @ X4))),
% 0.21/0.49      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (m1_pre_topc @ X0 @ 
% 0.21/0.49             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.49          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.49          | (m1_pre_topc @ X0 @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.49  thf('25', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (m1_pre_topc @ X0 @ 
% 0.21/0.49             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.49          | (m1_pre_topc @ X0 @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.49  thf('27', plain, ((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_A @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['21', '26'])).
% 0.21/0.49  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('29', plain, ((m1_pre_topc @ sk_A @ sk_B)),
% 0.21/0.49      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.49  thf(t35_borsuk_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_pre_topc @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.49           ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.21/0.49  thf('30', plain,
% 0.21/0.49      (![X15 : $i, X16 : $i]:
% 0.21/0.49         (~ (m1_pre_topc @ X15 @ X16)
% 0.21/0.49          | (r1_tarski @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))
% 0.21/0.49          | ~ (l1_pre_topc @ X16))),
% 0.21/0.49      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.21/0.49  thf('31', plain,
% 0.21/0.49      ((~ (l1_pre_topc @ sk_B)
% 0.21/0.49        | (r1_tarski @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.49  thf('32', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('33', plain, ((r1_tarski @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.49  thf(d10_xboole_0, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.49  thf('34', plain,
% 0.21/0.49      (![X0 : $i, X2 : $i]:
% 0.21/0.49         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.49  thf('35', plain,
% 0.21/0.49      ((~ (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.21/0.49        | ((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.49  thf('36', plain,
% 0.21/0.49      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.49         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('37', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((m1_pre_topc @ X0 @ 
% 0.21/0.49           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.21/0.49          | ~ (l1_pre_topc @ X0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.49  thf('38', plain,
% 0.21/0.49      (((m1_pre_topc @ sk_B @ 
% 0.21/0.49         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.49        | ~ (l1_pre_topc @ sk_B))),
% 0.21/0.49      inference('sup+', [status(thm)], ['36', '37'])).
% 0.21/0.49  thf('39', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('40', plain,
% 0.21/0.49      ((m1_pre_topc @ sk_B @ 
% 0.21/0.49        (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['38', '39'])).
% 0.21/0.49  thf('41', plain,
% 0.21/0.49      (![X3 : $i, X4 : $i]:
% 0.21/0.49         (~ (m1_pre_topc @ X3 @ 
% 0.21/0.49             (g1_pre_topc @ (u1_struct_0 @ X4) @ (u1_pre_topc @ X4)))
% 0.21/0.49          | (m1_pre_topc @ X3 @ X4)
% 0.21/0.49          | ~ (l1_pre_topc @ X4))),
% 0.21/0.49      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.21/0.49  thf('42', plain, ((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_B @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.49  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('44', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['42', '43'])).
% 0.21/0.49  thf('45', plain,
% 0.21/0.49      (![X15 : $i, X16 : $i]:
% 0.21/0.49         (~ (m1_pre_topc @ X15 @ X16)
% 0.21/0.49          | (r1_tarski @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))
% 0.21/0.49          | ~ (l1_pre_topc @ X16))),
% 0.21/0.49      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.21/0.49  thf('46', plain,
% 0.21/0.49      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.49        | (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.49  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('48', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['46', '47'])).
% 0.21/0.49  thf('49', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['35', '48'])).
% 0.21/0.49  thf('50', plain,
% 0.21/0.49      ((m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.21/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['17', '49'])).
% 0.21/0.49  thf('51', plain,
% 0.21/0.49      ((m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.21/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['17', '49'])).
% 0.21/0.49  thf('52', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['35', '48'])).
% 0.21/0.49  thf(t34_tops_2, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_pre_topc @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( m1_pre_topc @ C @ A ) =>
% 0.21/0.49               ( ( v4_pre_topc @ B @ A ) =>
% 0.21/0.49                 ( ![D:$i]:
% 0.21/0.49                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.21/0.49                     ( ( ( D ) = ( B ) ) => ( v4_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('53', plain,
% 0.21/0.49      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.21/0.49          | ~ (v4_pre_topc @ X10 @ X11)
% 0.21/0.49          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.21/0.49          | (v4_pre_topc @ X12 @ X13)
% 0.21/0.49          | ((X12) != (X10))
% 0.21/0.49          | ~ (m1_pre_topc @ X13 @ X11)
% 0.21/0.49          | ~ (l1_pre_topc @ X11))),
% 0.21/0.49      inference('cnf', [status(esa)], [t34_tops_2])).
% 0.21/0.49  thf('54', plain,
% 0.21/0.49      (![X10 : $i, X11 : $i, X13 : $i]:
% 0.21/0.49         (~ (l1_pre_topc @ X11)
% 0.21/0.49          | ~ (m1_pre_topc @ X13 @ X11)
% 0.21/0.49          | (v4_pre_topc @ X10 @ X13)
% 0.21/0.49          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.21/0.49          | ~ (v4_pre_topc @ X10 @ X11)
% 0.21/0.49          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11))))),
% 0.21/0.49      inference('simplify', [status(thm)], ['53'])).
% 0.21/0.49  thf('55', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.21/0.49          | ~ (v4_pre_topc @ X0 @ X1)
% 0.21/0.49          | (v4_pre_topc @ X0 @ sk_B)
% 0.21/0.49          | ~ (m1_pre_topc @ sk_B @ X1)
% 0.21/0.49          | ~ (l1_pre_topc @ X1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['52', '54'])).
% 0.21/0.49  thf('56', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (l1_pre_topc @ X0)
% 0.21/0.49          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.21/0.49          | (v4_pre_topc @ (sk_C @ sk_C_1 @ sk_B) @ sk_B)
% 0.21/0.49          | ~ (v4_pre_topc @ (sk_C @ sk_C_1 @ sk_B) @ X0)
% 0.21/0.49          | ~ (m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.21/0.49               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['51', '55'])).
% 0.21/0.49  thf('57', plain,
% 0.21/0.49      ((~ (v4_pre_topc @ (sk_C @ sk_C_1 @ sk_B) @ sk_A)
% 0.21/0.49        | (v4_pre_topc @ (sk_C @ sk_C_1 @ sk_B) @ sk_B)
% 0.21/0.49        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.21/0.49        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['50', '56'])).
% 0.21/0.49  thf('58', plain,
% 0.21/0.49      ((m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.21/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['17', '49'])).
% 0.21/0.49  thf('59', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_C_1 @ 
% 0.21/0.49        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('60', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X7 @ 
% 0.21/0.49             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8))))
% 0.21/0.49          | ~ (v2_tops_2 @ X7 @ X8)
% 0.21/0.49          | ~ (r2_hidden @ X9 @ X7)
% 0.21/0.49          | (v4_pre_topc @ X9 @ X8)
% 0.21/0.49          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.49          | ~ (l1_pre_topc @ X8))),
% 0.21/0.49      inference('cnf', [status(esa)], [d2_tops_2])).
% 0.21/0.49  thf('61', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (l1_pre_topc @ sk_A)
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.49          | (v4_pre_topc @ X0 @ sk_A)
% 0.21/0.49          | ~ (r2_hidden @ X0 @ sk_C_1)
% 0.21/0.49          | ~ (v2_tops_2 @ sk_C_1 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['59', '60'])).
% 0.21/0.49  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('63', plain, ((v2_tops_2 @ sk_C_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('64', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.49          | (v4_pre_topc @ X0 @ sk_A)
% 0.21/0.49          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.21/0.49      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.21/0.49  thf('65', plain,
% 0.21/0.49      ((~ (r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1)
% 0.21/0.49        | (v4_pre_topc @ (sk_C @ sk_C_1 @ sk_B) @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['58', '64'])).
% 0.21/0.49  thf('66', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_C_1 @ 
% 0.21/0.49        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.21/0.49      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.49  thf('67', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X7 @ 
% 0.21/0.49             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8))))
% 0.21/0.49          | (r2_hidden @ (sk_C @ X7 @ X8) @ X7)
% 0.21/0.49          | (v2_tops_2 @ X7 @ X8)
% 0.21/0.49          | ~ (l1_pre_topc @ X8))),
% 0.21/0.49      inference('cnf', [status(esa)], [d2_tops_2])).
% 0.21/0.49  thf('68', plain,
% 0.21/0.49      ((~ (l1_pre_topc @ sk_B)
% 0.21/0.49        | (v2_tops_2 @ sk_C_1 @ sk_B)
% 0.21/0.49        | (r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['66', '67'])).
% 0.21/0.49  thf('69', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('70', plain,
% 0.21/0.49      (((v2_tops_2 @ sk_C_1 @ sk_B)
% 0.21/0.49        | (r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1))),
% 0.21/0.49      inference('demod', [status(thm)], ['68', '69'])).
% 0.21/0.49  thf('71', plain, (~ (v2_tops_2 @ sk_C_1 @ sk_B)),
% 0.21/0.49      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.49  thf('72', plain, ((r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1)),
% 0.21/0.49      inference('clc', [status(thm)], ['70', '71'])).
% 0.21/0.49  thf('73', plain, ((v4_pre_topc @ (sk_C @ sk_C_1 @ sk_B) @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['65', '72'])).
% 0.21/0.49  thf('74', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['42', '43'])).
% 0.21/0.49  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('76', plain, ((v4_pre_topc @ (sk_C @ sk_C_1 @ sk_B) @ sk_B)),
% 0.21/0.49      inference('demod', [status(thm)], ['57', '73', '74', '75'])).
% 0.21/0.49  thf('77', plain, ($false), inference('demod', [status(thm)], ['10', '76'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
