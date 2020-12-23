%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT2052+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WsyAo8bYWt

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 620 expanded)
%              Number of leaves         :   17 ( 170 expanded)
%              Depth                    :   24
%              Number of atoms          :  836 (9460 expanded)
%              Number of equality atoms :   18 ( 128 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(a_2_1_yellow19_type,type,(
    a_2_1_yellow19: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t11_yellow19,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( r2_hidden @ C @ ( k2_yellow19 @ A @ B ) )
            <=> ( ( r1_waybel_0 @ A @ B @ C )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_struct_0 @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( l1_waybel_0 @ B @ A ) )
           => ! [C: $i] :
                ( ( r2_hidden @ C @ ( k2_yellow19 @ A @ B ) )
              <=> ( ( r1_waybel_0 @ A @ B @ C )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t11_yellow19])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_waybel_0 @ sk_A @ sk_B @ sk_C )
    | ( r2_hidden @ sk_C @ ( k2_yellow19 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( r1_waybel_0 @ sk_A @ sk_B @ sk_C )
   <= ( r1_waybel_0 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,
    ( ( r2_hidden @ sk_C @ ( k2_yellow19 @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_C @ ( k2_yellow19 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['1'])).

thf('4',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_yellow19,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ( ( k2_yellow19 @ A @ B )
            = ( a_2_1_yellow19 @ A @ B ) ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ( ( k2_yellow19 @ X1 @ X0 )
        = ( a_2_1_yellow19 @ X1 @ X0 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_yellow19])).

thf('6',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k2_yellow19 @ sk_A @ sk_B )
      = ( a_2_1_yellow19 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_yellow19 @ sk_A @ sk_B )
      = ( a_2_1_yellow19 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_yellow19 @ sk_A @ sk_B )
      = ( a_2_1_yellow19 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( k2_yellow19 @ sk_A @ sk_B )
    = ( a_2_1_yellow19 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['10','11'])).

thf(fraenkel_a_2_1_yellow19,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ B )
        & ( l1_struct_0 @ B )
        & ~ ( v2_struct_0 @ C )
        & ( l1_waybel_0 @ C @ B ) )
     => ( ( r2_hidden @ A @ ( a_2_1_yellow19 @ B @ C ) )
      <=> ? [D: $i] :
            ( ( r1_waybel_0 @ B @ C @ D )
            & ( A = D )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( l1_struct_0 @ X2 )
      | ( v2_struct_0 @ X2 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_waybel_0 @ X3 @ X2 )
      | ( r1_waybel_0 @ X2 @ X3 @ ( sk_D @ X3 @ X2 @ X4 ) )
      | ~ ( r2_hidden @ X4 @ ( a_2_1_yellow19 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_yellow19])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_yellow19 @ sk_A @ sk_B ) )
      | ( r1_waybel_0 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_A @ X0 ) )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_yellow19 @ sk_A @ sk_B ) )
      | ( r1_waybel_0 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ ( sk_D @ sk_B @ sk_A @ sk_C ) ) )
   <= ( r2_hidden @ sk_C @ ( k2_yellow19 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','17'])).

thf('19',plain,
    ( ( r2_hidden @ sk_C @ ( k2_yellow19 @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_C @ ( k2_yellow19 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['1'])).

thf('20',plain,
    ( ( k2_yellow19 @ sk_A @ sk_B )
    = ( a_2_1_yellow19 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('21',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( l1_struct_0 @ X2 )
      | ( v2_struct_0 @ X2 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_waybel_0 @ X3 @ X2 )
      | ( X4
        = ( sk_D @ X3 @ X2 @ X4 ) )
      | ~ ( r2_hidden @ X4 @ ( a_2_1_yellow19 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_yellow19])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_yellow19 @ sk_A @ sk_B ) )
      | ( X0
        = ( sk_D @ sk_B @ sk_A @ X0 ) )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_yellow19 @ sk_A @ sk_B ) )
      | ( X0
        = ( sk_D @ sk_B @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( sk_C
        = ( sk_D @ sk_B @ sk_A @ sk_C ) ) )
   <= ( r2_hidden @ sk_C @ ( k2_yellow19 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( ( sk_C
        = ( sk_D @ sk_B @ sk_A @ sk_C ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r2_hidden @ sk_C @ ( k2_yellow19 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( sk_C
      = ( sk_D @ sk_B @ sk_A @ sk_C ) )
   <= ( r2_hidden @ sk_C @ ( k2_yellow19 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_waybel_0 @ sk_A @ sk_B @ sk_C ) )
   <= ( r2_hidden @ sk_C @ ( k2_yellow19 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( ( r1_waybel_0 @ sk_A @ sk_B @ sk_C )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r2_hidden @ sk_C @ ( k2_yellow19 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( r1_waybel_0 @ sk_A @ sk_B @ sk_C )
   <= ( r2_hidden @ sk_C @ ( k2_yellow19 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_waybel_0 @ sk_A @ sk_B @ sk_C )
    | ~ ( r2_hidden @ sk_C @ ( k2_yellow19 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ~ ( r1_waybel_0 @ sk_A @ sk_B @ sk_C )
   <= ~ ( r1_waybel_0 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['36'])).

thf('38',plain,
    ( ( r1_waybel_0 @ sk_A @ sk_B @ sk_C )
    | ~ ( r2_hidden @ sk_C @ ( k2_yellow19 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,
    ( ( r2_hidden @ sk_C @ ( k2_yellow19 @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_C @ ( k2_yellow19 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['1'])).

thf('40',plain,
    ( ( k2_yellow19 @ sk_A @ sk_B )
    = ( a_2_1_yellow19 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('41',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( l1_struct_0 @ X2 )
      | ( v2_struct_0 @ X2 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_waybel_0 @ X3 @ X2 )
      | ( m1_subset_1 @ ( sk_D @ X3 @ X2 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( r2_hidden @ X4 @ ( a_2_1_yellow19 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_yellow19])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_yellow19 @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ ( sk_D @ sk_B @ sk_A @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_yellow19 @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ ( sk_D @ sk_B @ sk_A @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ sk_B @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( r2_hidden @ sk_C @ ( k2_yellow19 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','45'])).

thf('47',plain,
    ( ( sk_C
      = ( sk_D @ sk_B @ sk_A @ sk_C ) )
   <= ( r2_hidden @ sk_C @ ( k2_yellow19 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('48',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( r2_hidden @ sk_C @ ( k2_yellow19 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r2_hidden @ sk_C @ ( k2_yellow19 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k2_yellow19 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,
    ( ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['36'])).

thf('54',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r2_hidden @ sk_C @ ( k2_yellow19 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( r2_hidden @ sk_C @ ( k2_yellow19 @ sk_A @ sk_B ) )
    | ~ ( r1_waybel_0 @ sk_A @ sk_B @ sk_C )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['36'])).

thf('56',plain,
    ( ( r1_waybel_0 @ sk_A @ sk_B @ sk_C )
    | ( r2_hidden @ sk_C @ ( k2_yellow19 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['1'])).

thf('57',plain,(
    r1_waybel_0 @ sk_A @ sk_B @ sk_C ),
    inference('sat_resolution*',[status(thm)],['38','54','55','56'])).

thf('58',plain,(
    r1_waybel_0 @ sk_A @ sk_B @ sk_C ),
    inference(simpl_trail,[status(thm)],['2','57'])).

thf('59',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ sk_C @ ( k2_yellow19 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['59'])).

thf('61',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ sk_C @ ( k2_yellow19 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['59'])).

thf('62',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['38','54','55','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['60','62'])).

thf('64',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( l1_struct_0 @ X2 )
      | ( v2_struct_0 @ X2 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_waybel_0 @ X3 @ X2 )
      | ( r2_hidden @ X4 @ ( a_2_1_yellow19 @ X2 @ X3 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( X4 != X5 )
      | ~ ( r1_waybel_0 @ X2 @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_yellow19])).

thf('65',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ~ ( r1_waybel_0 @ X2 @ X3 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( r2_hidden @ X5 @ ( a_2_1_yellow19 @ X2 @ X3 ) )
      | ~ ( l1_waybel_0 @ X3 @ X2 )
      | ( v2_struct_0 @ X3 )
      | ( v2_struct_0 @ X2 )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( r2_hidden @ sk_C @ ( a_2_1_yellow19 @ sk_A @ X0 ) )
      | ~ ( r1_waybel_0 @ sk_A @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['63','65'])).

thf('67',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( r2_hidden @ sk_C @ ( a_2_1_yellow19 @ sk_A @ X0 ) )
      | ~ ( r1_waybel_0 @ sk_A @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( r2_hidden @ sk_C @ ( a_2_1_yellow19 @ sk_A @ sk_B ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['58','68'])).

thf('70',plain,
    ( ( k2_yellow19 @ sk_A @ sk_B )
    = ( a_2_1_yellow19 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('71',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( r2_hidden @ sk_C @ ( k2_yellow19 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,
    ( ~ ( r2_hidden @ sk_C @ ( k2_yellow19 @ sk_A @ sk_B ) )
   <= ~ ( r2_hidden @ sk_C @ ( k2_yellow19 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['36'])).

thf('74',plain,(
    ~ ( r2_hidden @ sk_C @ ( k2_yellow19 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['38','54','55'])).

thf('75',plain,(
    ~ ( r2_hidden @ sk_C @ ( k2_yellow19 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['72','75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v2_struct_0 @ sk_B ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,(
    $false ),
    inference(demod,[status(thm)],['0','78'])).


%------------------------------------------------------------------------------
