%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1646+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.F7AAaTnqis

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:55 EST 2020

% Result     : Theorem 4.19s
% Output     : Refutation 4.22s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 655 expanded)
%              Number of leaves         :   20 ( 185 expanded)
%              Depth                    :   20
%              Number of atoms          : 1000 (10924 expanded)
%              Number of equality atoms :    9 ( 123 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(v12_waybel_0_type,type,(
    v12_waybel_0: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(t26_waybel_0,conjecture,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( r2_hidden @ C @ B )
                 => ( v12_waybel_0 @ C @ A ) ) )
           => ( ( v12_waybel_0 @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A )
              & ( m1_subset_1 @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_orders_2 @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( r2_hidden @ C @ B )
                   => ( v12_waybel_0 @ C @ A ) ) )
             => ( ( v12_waybel_0 @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A )
                & ( m1_subset_1 @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t26_waybel_0])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( ( m1_subset_1 @ ( k5_setfam_1 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_setfam_1])).

thf('2',plain,(
    m1_subset_1 @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k5_setfam_1 @ A @ B )
        = ( k3_tarski @ B ) ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k5_setfam_1 @ X14 @ X13 )
        = ( k3_tarski @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('5',plain,
    ( ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k3_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ ( k3_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf(d19_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v12_waybel_0 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( ( r2_hidden @ C @ B )
                        & ( r1_orders_2 @ A @ D @ C ) )
                     => ( r2_hidden @ D @ B ) ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 ) @ X0 )
      | ( v12_waybel_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d19_waybel_0])).

thf('8',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( v12_waybel_0 @ ( k3_tarski @ sk_B ) @ sk_A )
    | ~ ( r2_hidden @ ( sk_D @ ( k3_tarski @ sk_B ) @ sk_A ) @ ( k3_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v12_waybel_0 @ ( k3_tarski @ sk_B ) @ sk_A )
    | ~ ( r2_hidden @ ( sk_D @ ( k3_tarski @ sk_B ) @ sk_A ) @ ( k3_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( v12_waybel_0 @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( m1_subset_1 @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ~ ( v12_waybel_0 @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ~ ( v12_waybel_0 @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,
    ( ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k3_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('14',plain,
    ( ~ ( v12_waybel_0 @ ( k3_tarski @ sk_B ) @ sk_A )
   <= ~ ( v12_waybel_0 @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ ( k3_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('16',plain,
    ( ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k3_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('17',plain,
    ( ~ ( m1_subset_1 @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['11'])).

thf('18',plain,
    ( ~ ( m1_subset_1 @ ( k3_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,
    ( ~ ( v12_waybel_0 @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( m1_subset_1 @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['11'])).

thf('21',plain,(
    ~ ( v12_waybel_0 @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ( v12_waybel_0 @ ( k3_tarski @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['14','21'])).

thf('23',plain,(
    ~ ( r2_hidden @ ( sk_D @ ( k3_tarski @ sk_B ) @ sk_A ) @ ( k3_tarski @ sk_B ) ) ),
    inference(clc,[status(thm)],['10','22'])).

thf('24',plain,(
    m1_subset_1 @ ( k3_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( v12_waybel_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d19_waybel_0])).

thf('26',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( v12_waybel_0 @ ( k3_tarski @ sk_B ) @ sk_A )
    | ( r2_hidden @ ( sk_C @ ( k3_tarski @ sk_B ) @ sk_A ) @ ( k3_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v12_waybel_0 @ ( k3_tarski @ sk_B ) @ sk_A )
    | ( r2_hidden @ ( sk_C @ ( k3_tarski @ sk_B ) @ sk_A ) @ ( k3_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ~ ( v12_waybel_0 @ ( k3_tarski @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['14','21'])).

thf('30',plain,(
    r2_hidden @ ( sk_C @ ( k3_tarski @ sk_B ) @ sk_A ) @ ( k3_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['28','29'])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('31',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ ( sk_D_2 @ X8 @ X5 ) @ X5 )
      | ( X7
       != ( k3_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('32',plain,(
    ! [X5: $i,X8: $i] :
      ( ( r2_hidden @ ( sk_D_2 @ X8 @ X5 ) @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k3_tarski @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    r2_hidden @ ( sk_D_2 @ ( sk_C @ ( k3_tarski @ sk_B ) @ sk_A ) @ sk_B ) @ sk_B ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    m1_subset_1 @ ( k3_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( r1_orders_2 @ X1 @ ( sk_D @ X0 @ X1 ) @ ( sk_C @ X0 @ X1 ) )
      | ( v12_waybel_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d19_waybel_0])).

thf('36',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( v12_waybel_0 @ ( k3_tarski @ sk_B ) @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k3_tarski @ sk_B ) @ sk_A ) @ ( sk_C @ ( k3_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v12_waybel_0 @ ( k3_tarski @ sk_B ) @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k3_tarski @ sk_B ) @ sk_A ) @ ( sk_C @ ( k3_tarski @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( v12_waybel_0 @ ( k3_tarski @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['14','21'])).

thf('40',plain,(
    r1_orders_2 @ sk_A @ ( sk_D @ ( k3_tarski @ sk_B ) @ sk_A ) @ ( sk_C @ ( k3_tarski @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    r2_hidden @ ( sk_C @ ( k3_tarski @ sk_B ) @ sk_A ) @ ( k3_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('42',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ ( sk_D_2 @ X8 @ X5 ) )
      | ( X7
       != ( k3_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('43',plain,(
    ! [X5: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ ( sk_D_2 @ X8 @ X5 ) )
      | ~ ( r2_hidden @ X8 @ ( k3_tarski @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    r2_hidden @ ( sk_C @ ( k3_tarski @ sk_B ) @ sk_A ) @ ( sk_D_2 @ ( sk_C @ ( k3_tarski @ sk_B ) @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,(
    r2_hidden @ ( sk_D_2 @ ( sk_C @ ( k3_tarski @ sk_B ) @ sk_A ) @ sk_B ) @ sk_B ),
    inference('sup-',[status(thm)],['30','32'])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('47',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( m1_subset_1 @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ ( sk_D_2 @ ( sk_C @ ( k3_tarski @ sk_B ) @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( v12_waybel_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( r2_hidden @ X2 @ X0 )
      | ~ ( r1_orders_2 @ X1 @ X2 @ X3 )
      | ~ ( r2_hidden @ X3 @ X0 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d19_waybel_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( sk_D_2 @ ( sk_C @ ( k3_tarski @ sk_B ) @ sk_A ) @ sk_B ) )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( sk_D_2 @ ( sk_C @ ( k3_tarski @ sk_B ) @ sk_A ) @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v12_waybel_0 @ ( sk_D_2 @ ( sk_C @ ( k3_tarski @ sk_B ) @ sk_A ) @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( sk_D_2 @ ( sk_C @ ( k3_tarski @ sk_B ) @ sk_A ) @ sk_B ) )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( sk_D_2 @ ( sk_C @ ( k3_tarski @ sk_B ) @ sk_A ) @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v12_waybel_0 @ ( sk_D_2 @ ( sk_C @ ( k3_tarski @ sk_B ) @ sk_A ) @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ ( sk_D_2 @ ( sk_C @ ( k3_tarski @ sk_B ) @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('55',plain,(
    ! [X18: $i] :
      ( ~ ( r2_hidden @ X18 @ sk_B )
      | ( v12_waybel_0 @ X18 @ sk_A )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( v12_waybel_0 @ ( sk_D_2 @ ( sk_C @ ( k3_tarski @ sk_B ) @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( r2_hidden @ ( sk_D_2 @ ( sk_C @ ( k3_tarski @ sk_B ) @ sk_A ) @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    r2_hidden @ ( sk_D_2 @ ( sk_C @ ( k3_tarski @ sk_B ) @ sk_A ) @ sk_B ) @ sk_B ),
    inference('sup-',[status(thm)],['30','32'])).

thf('58',plain,(
    v12_waybel_0 @ ( sk_D_2 @ ( sk_C @ ( k3_tarski @ sk_B ) @ sk_A ) @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( sk_D_2 @ ( sk_C @ ( k3_tarski @ sk_B ) @ sk_A ) @ sk_B ) )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( sk_D_2 @ ( sk_C @ ( k3_tarski @ sk_B ) @ sk_A ) @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['53','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( sk_D_2 @ ( sk_C @ ( k3_tarski @ sk_B ) @ sk_A ) @ sk_B ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ ( sk_C @ ( k3_tarski @ sk_B ) @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_C @ ( k3_tarski @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['44','59'])).

thf('61',plain,(
    r2_hidden @ ( sk_C @ ( k3_tarski @ sk_B ) @ sk_A ) @ ( k3_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('62',plain,(
    m1_subset_1 @ ( k3_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('63',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( m1_subset_1 @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k3_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ ( sk_C @ ( k3_tarski @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( sk_D_2 @ ( sk_C @ ( k3_tarski @ sk_B ) @ sk_A ) @ sk_B ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ ( sk_C @ ( k3_tarski @ sk_B ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['60','65'])).

thf('67',plain,
    ( ( r2_hidden @ ( sk_D @ ( k3_tarski @ sk_B ) @ sk_A ) @ ( sk_D_2 @ ( sk_C @ ( k3_tarski @ sk_B ) @ sk_A ) @ sk_B ) )
    | ~ ( m1_subset_1 @ ( sk_D @ ( k3_tarski @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','66'])).

thf('68',plain,(
    m1_subset_1 @ ( k3_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ( v12_waybel_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d19_waybel_0])).

thf('70',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( v12_waybel_0 @ ( k3_tarski @ sk_B ) @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( k3_tarski @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( v12_waybel_0 @ ( k3_tarski @ sk_B ) @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ ( k3_tarski @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ~ ( v12_waybel_0 @ ( k3_tarski @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['14','21'])).

thf('74',plain,(
    m1_subset_1 @ ( sk_D @ ( k3_tarski @ sk_B ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,(
    r2_hidden @ ( sk_D @ ( k3_tarski @ sk_B ) @ sk_A ) @ ( sk_D_2 @ ( sk_C @ ( k3_tarski @ sk_B ) @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['67','74'])).

thf('76',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( r2_hidden @ X6 @ X7 )
      | ( X7
       != ( k3_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('77',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ ( k3_tarski @ X5 ) )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_D_2 @ ( sk_C @ ( k3_tarski @ sk_B ) @ sk_A ) @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_D @ ( k3_tarski @ sk_B ) @ sk_A ) @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['75','77'])).

thf('79',plain,(
    r2_hidden @ ( sk_D @ ( k3_tarski @ sk_B ) @ sk_A ) @ ( k3_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['33','78'])).

thf('80',plain,(
    $false ),
    inference(demod,[status(thm)],['23','79'])).


%------------------------------------------------------------------------------
