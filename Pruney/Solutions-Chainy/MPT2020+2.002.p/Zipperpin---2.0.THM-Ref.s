%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hKZ1mKopSb

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:23 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 511 expanded)
%              Number of leaves         :   19 ( 148 expanded)
%              Depth                    :   18
%              Number of atoms          :  750 (9092 expanded)
%              Number of equality atoms :   33 ( 627 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(t19_waybel_9,conjecture,(
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
                      & ( v1_tops_2 @ C @ A ) )
                   => ( v1_tops_2 @ D @ B ) ) ) ) ) ) )).

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
                        & ( v1_tops_2 @ C @ A ) )
                     => ( v1_tops_2 @ D @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t19_waybel_9])).

thf('0',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X2: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X2 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) ) )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(free_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_pre_topc @ A @ B )
            = ( g1_pre_topc @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( g1_pre_topc @ X5 @ X6 )
       != ( g1_pre_topc @ X3 @ X4 ) )
      | ( X6 = X4 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_pre_topc @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( g1_pre_topc @ X1 @ X0 ) )
      | ( ( u1_pre_topc @ sk_B )
        = X0 )
      | ~ ( l1_pre_topc @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( g1_pre_topc @ X1 @ X0 ) )
      | ( ( u1_pre_topc @ sk_B )
        = X0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( u1_pre_topc @ sk_B )
    = ( u1_pre_topc @ sk_A ) ),
    inference(eq_res,[status(thm)],['7'])).

thf('9',plain,(
    ! [X2: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X2 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) ) )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('10',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( ( g1_pre_topc @ X5 @ X6 )
       != ( g1_pre_topc @ X3 @ X4 ) )
      | ( X5 = X3 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_B )
        = X0 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
       != ( g1_pre_topc @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( u1_pre_topc @ sk_B )
    = ( u1_pre_topc @ sk_A ) ),
    inference(eq_res,[status(thm)],['7'])).

thf('17',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_B )
        = X0 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( g1_pre_topc @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['18'])).

thf(d1_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_tops_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( r2_hidden @ C @ B )
                 => ( v3_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('20',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) ) )
      | ( m1_subset_1 @ ( sk_C @ X7 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( v1_tops_2 @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v1_tops_2 @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['18'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v1_tops_2 @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_tops_2 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','24'])).

thf('26',plain,(
    ~ ( v1_tops_2 @ sk_D @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    sk_C_1 = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ~ ( v1_tops_2 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['25','28'])).

thf('30',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['18'])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ X1 ) )
      | ( v3_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v3_pre_topc @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( u1_pre_topc @ sk_B )
    = ( u1_pre_topc @ sk_A ) ),
    inference(eq_res,[status(thm)],['7'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ~ ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ( v3_pre_topc @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['29','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['18'])).

thf('39',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( v3_pre_topc @ ( sk_C @ X7 @ X8 ) @ X8 )
      | ( v1_tops_2 @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v1_tops_2 @ X0 @ sk_B )
      | ~ ( v3_pre_topc @ ( sk_C @ X0 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v1_tops_2 @ X0 @ sk_B )
      | ~ ( v3_pre_topc @ ( sk_C @ X0 @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( v3_pre_topc @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_B )
    | ( v1_tops_2 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['37','42'])).

thf('44',plain,(
    ~ ( v1_tops_2 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('45',plain,(
    ~ ( v3_pre_topc @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_B ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(clc,[status(thm)],['36','45'])).

thf('47',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['25','28'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( v3_pre_topc @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( u1_pre_topc @ X1 ) )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('49',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['25','28'])).

thf('53',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( v1_tops_2 @ X7 @ X8 )
      | ~ ( r2_hidden @ X9 @ X7 )
      | ( v3_pre_topc @ X9 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( v1_tops_2 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_tops_2 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,
    ( ~ ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 )
    | ( v3_pre_topc @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['52','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    sk_C_1 = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) ) )
      | ( r2_hidden @ ( sk_C @ X7 @ X8 ) @ X7 )
      | ( v1_tops_2 @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('64',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v1_tops_2 @ sk_C_1 @ sk_B )
    | ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v1_tops_2 @ sk_C_1 @ sk_B )
    | ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ~ ( v1_tops_2 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('68',plain,(
    r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    v3_pre_topc @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['59','68'])).

thf('70',plain,(
    r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['51','69'])).

thf('71',plain,(
    $false ),
    inference(demod,[status(thm)],['46','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hKZ1mKopSb
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:16:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 96 iterations in 0.045s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.20/0.50  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.50  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.20/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.50  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.20/0.50  thf(t19_waybel_9, conjecture,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( l1_pre_topc @ B ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( m1_subset_1 @
% 0.20/0.50                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.50               ( ![D:$i]:
% 0.20/0.50                 ( ( m1_subset_1 @
% 0.20/0.50                     D @ 
% 0.20/0.50                     ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.20/0.50                   ( ( ( ( g1_pre_topc @
% 0.20/0.50                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.20/0.50                         ( g1_pre_topc @
% 0.20/0.50                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.20/0.50                       ( ( C ) = ( D ) ) & ( v1_tops_2 @ C @ A ) ) =>
% 0.20/0.50                     ( v1_tops_2 @ D @ B ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]:
% 0.20/0.50        ( ( l1_pre_topc @ A ) =>
% 0.20/0.50          ( ![B:$i]:
% 0.20/0.50            ( ( l1_pre_topc @ B ) =>
% 0.20/0.50              ( ![C:$i]:
% 0.20/0.50                ( ( m1_subset_1 @
% 0.20/0.50                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.50                  ( ![D:$i]:
% 0.20/0.50                    ( ( m1_subset_1 @
% 0.20/0.50                        D @ 
% 0.20/0.50                        ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.20/0.50                      ( ( ( ( g1_pre_topc @
% 0.20/0.50                              ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.20/0.50                            ( g1_pre_topc @
% 0.20/0.50                              ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.20/0.50                          ( ( C ) = ( D ) ) & ( v1_tops_2 @ C @ A ) ) =>
% 0.20/0.50                        ( v1_tops_2 @ D @ B ) ) ) ) ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t19_waybel_9])).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_C_1 @ 
% 0.20/0.50        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.50         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(dt_u1_pre_topc, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( m1_subset_1 @
% 0.20/0.50         ( u1_pre_topc @ A ) @ 
% 0.20/0.50         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (![X2 : $i]:
% 0.20/0.50         ((m1_subset_1 @ (u1_pre_topc @ X2) @ 
% 0.20/0.50           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2))))
% 0.20/0.50          | ~ (l1_pre_topc @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.20/0.50  thf(free_g1_pre_topc, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.50       ( ![C:$i,D:$i]:
% 0.20/0.50         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 0.20/0.50           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.50         (((g1_pre_topc @ X5 @ X6) != (g1_pre_topc @ X3 @ X4))
% 0.20/0.50          | ((X6) = (X4))
% 0.20/0.50          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X5))))),
% 0.20/0.50      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (~ (l1_pre_topc @ X0)
% 0.20/0.50          | ((u1_pre_topc @ X0) = (X1))
% 0.20/0.50          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.20/0.50              != (g1_pre_topc @ X2 @ X1)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.50            != (g1_pre_topc @ X1 @ X0))
% 0.20/0.50          | ((u1_pre_topc @ sk_B) = (X0))
% 0.20/0.50          | ~ (l1_pre_topc @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['1', '4'])).
% 0.20/0.50  thf('6', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.50            != (g1_pre_topc @ X1 @ X0))
% 0.20/0.50          | ((u1_pre_topc @ sk_B) = (X0)))),
% 0.20/0.50      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.50  thf('8', plain, (((u1_pre_topc @ sk_B) = (u1_pre_topc @ sk_A))),
% 0.20/0.50      inference('eq_res', [status(thm)], ['7'])).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (![X2 : $i]:
% 0.20/0.50         ((m1_subset_1 @ (u1_pre_topc @ X2) @ 
% 0.20/0.50           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2))))
% 0.20/0.50          | ~ (l1_pre_topc @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.20/0.50         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))
% 0.20/0.50        | ~ (l1_pre_topc @ sk_B))),
% 0.20/0.50      inference('sup+', [status(thm)], ['8', '9'])).
% 0.20/0.50  thf('11', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      ((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.20/0.50        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.20/0.50      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.50         (((g1_pre_topc @ X5 @ X6) != (g1_pre_topc @ X3 @ X4))
% 0.20/0.50          | ((X5) = (X3))
% 0.20/0.50          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X5))))),
% 0.20/0.50      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (((u1_struct_0 @ sk_B) = (X0))
% 0.20/0.50          | ((g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.20/0.50              != (g1_pre_topc @ X0 @ X1)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.50         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('16', plain, (((u1_pre_topc @ sk_B) = (u1_pre_topc @ sk_A))),
% 0.20/0.50      inference('eq_res', [status(thm)], ['7'])).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.50         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (((u1_struct_0 @ sk_B) = (X0))
% 0.20/0.50          | ((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.50              != (g1_pre_topc @ X0 @ X1)))),
% 0.20/0.50      inference('demod', [status(thm)], ['14', '17'])).
% 0.20/0.50  thf('19', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('eq_res', [status(thm)], ['18'])).
% 0.20/0.50  thf(d1_tops_2, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @
% 0.20/0.50             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.50           ( ( v1_tops_2 @ B @ A ) <=>
% 0.20/0.50             ( ![C:$i]:
% 0.20/0.50               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50                 ( ( r2_hidden @ C @ B ) => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      (![X7 : $i, X8 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X7 @ 
% 0.20/0.50             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8))))
% 0.20/0.50          | (m1_subset_1 @ (sk_C @ X7 @ X8) @ 
% 0.20/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.50          | (v1_tops_2 @ X7 @ X8)
% 0.20/0.50          | ~ (l1_pre_topc @ X8))),
% 0.20/0.50      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X0 @ 
% 0.20/0.50             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.50          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.50          | (v1_tops_2 @ X0 @ sk_B)
% 0.20/0.50          | (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ 
% 0.20/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.50  thf('22', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('23', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('eq_res', [status(thm)], ['18'])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X0 @ 
% 0.20/0.50             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.50          | (v1_tops_2 @ X0 @ sk_B)
% 0.20/0.50          | (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ 
% 0.20/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.50      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      (((m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.20/0.50         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50        | (v1_tops_2 @ sk_C_1 @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['0', '24'])).
% 0.20/0.50  thf('26', plain, (~ (v1_tops_2 @ sk_D @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('27', plain, (((sk_C_1) = (sk_D))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('28', plain, (~ (v1_tops_2 @ sk_C_1 @ sk_B)),
% 0.20/0.50      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      ((m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.20/0.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('clc', [status(thm)], ['25', '28'])).
% 0.20/0.50  thf('30', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('eq_res', [status(thm)], ['18'])).
% 0.20/0.50  thf(d5_pre_topc, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.50           ( ( v3_pre_topc @ B @ A ) <=>
% 0.20/0.50             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.20/0.50          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ X1))
% 0.20/0.50          | (v3_pre_topc @ X0 @ X1)
% 0.20/0.50          | ~ (l1_pre_topc @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.20/0.50  thf('32', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.50          | (v3_pre_topc @ X0 @ sk_B)
% 0.20/0.50          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.50  thf('33', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('34', plain, (((u1_pre_topc @ sk_B) = (u1_pre_topc @ sk_A))),
% 0.20/0.50      inference('eq_res', [status(thm)], ['7'])).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50          | (v3_pre_topc @ X0 @ sk_B)
% 0.20/0.50          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      ((~ (r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.20/0.50        | (v3_pre_topc @ (sk_C @ sk_C_1 @ sk_B) @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['29', '35'])).
% 0.20/0.50  thf('37', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_C_1 @ 
% 0.20/0.50        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('38', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('eq_res', [status(thm)], ['18'])).
% 0.20/0.50  thf('39', plain,
% 0.20/0.50      (![X7 : $i, X8 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X7 @ 
% 0.20/0.50             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8))))
% 0.20/0.50          | ~ (v3_pre_topc @ (sk_C @ X7 @ X8) @ X8)
% 0.20/0.50          | (v1_tops_2 @ X7 @ X8)
% 0.20/0.50          | ~ (l1_pre_topc @ X8))),
% 0.20/0.50      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.20/0.50  thf('40', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X0 @ 
% 0.20/0.50             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.50          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.50          | (v1_tops_2 @ X0 @ sk_B)
% 0.20/0.50          | ~ (v3_pre_topc @ (sk_C @ X0 @ sk_B) @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.50  thf('41', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('42', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X0 @ 
% 0.20/0.50             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.50          | (v1_tops_2 @ X0 @ sk_B)
% 0.20/0.50          | ~ (v3_pre_topc @ (sk_C @ X0 @ sk_B) @ sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['40', '41'])).
% 0.20/0.50  thf('43', plain,
% 0.20/0.50      ((~ (v3_pre_topc @ (sk_C @ sk_C_1 @ sk_B) @ sk_B)
% 0.20/0.50        | (v1_tops_2 @ sk_C_1 @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['37', '42'])).
% 0.20/0.50  thf('44', plain, (~ (v1_tops_2 @ sk_C_1 @ sk_B)),
% 0.20/0.50      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.50  thf('45', plain, (~ (v3_pre_topc @ (sk_C @ sk_C_1 @ sk_B) @ sk_B)),
% 0.20/0.50      inference('clc', [status(thm)], ['43', '44'])).
% 0.20/0.50  thf('46', plain,
% 0.20/0.50      (~ (r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ (u1_pre_topc @ sk_A))),
% 0.20/0.50      inference('clc', [status(thm)], ['36', '45'])).
% 0.20/0.50  thf('47', plain,
% 0.20/0.50      ((m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.20/0.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('clc', [status(thm)], ['25', '28'])).
% 0.20/0.50  thf('48', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.20/0.50          | ~ (v3_pre_topc @ X0 @ X1)
% 0.20/0.50          | (r2_hidden @ X0 @ (u1_pre_topc @ X1))
% 0.20/0.50          | ~ (l1_pre_topc @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.20/0.50  thf('49', plain,
% 0.20/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.50        | (r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.20/0.50        | ~ (v3_pre_topc @ (sk_C @ sk_C_1 @ sk_B) @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.50  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('51', plain,
% 0.20/0.50      (((r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ (u1_pre_topc @ sk_A))
% 0.20/0.50        | ~ (v3_pre_topc @ (sk_C @ sk_C_1 @ sk_B) @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['49', '50'])).
% 0.20/0.50  thf('52', plain,
% 0.20/0.50      ((m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.20/0.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.50      inference('clc', [status(thm)], ['25', '28'])).
% 0.20/0.50  thf('53', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_C_1 @ 
% 0.20/0.50        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('54', plain,
% 0.20/0.50      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X7 @ 
% 0.20/0.50             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8))))
% 0.20/0.50          | ~ (v1_tops_2 @ X7 @ X8)
% 0.20/0.50          | ~ (r2_hidden @ X9 @ X7)
% 0.20/0.50          | (v3_pre_topc @ X9 @ X8)
% 0.20/0.50          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.20/0.50          | ~ (l1_pre_topc @ X8))),
% 0.20/0.50      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.20/0.50  thf('55', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (l1_pre_topc @ sk_A)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50          | (v3_pre_topc @ X0 @ sk_A)
% 0.20/0.50          | ~ (r2_hidden @ X0 @ sk_C_1)
% 0.20/0.50          | ~ (v1_tops_2 @ sk_C_1 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.50  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('57', plain, ((v1_tops_2 @ sk_C_1 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('58', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.50          | (v3_pre_topc @ X0 @ sk_A)
% 0.20/0.50          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.20/0.50      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.20/0.50  thf('59', plain,
% 0.20/0.50      ((~ (r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1)
% 0.20/0.50        | (v3_pre_topc @ (sk_C @ sk_C_1 @ sk_B) @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['52', '58'])).
% 0.20/0.50  thf('60', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_D @ 
% 0.20/0.50        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('61', plain, (((sk_C_1) = (sk_D))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('62', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_C_1 @ 
% 0.20/0.50        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.20/0.50      inference('demod', [status(thm)], ['60', '61'])).
% 0.20/0.50  thf('63', plain,
% 0.20/0.50      (![X7 : $i, X8 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X7 @ 
% 0.20/0.50             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8))))
% 0.20/0.50          | (r2_hidden @ (sk_C @ X7 @ X8) @ X7)
% 0.20/0.50          | (v1_tops_2 @ X7 @ X8)
% 0.20/0.50          | ~ (l1_pre_topc @ X8))),
% 0.20/0.50      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.20/0.50  thf('64', plain,
% 0.20/0.50      ((~ (l1_pre_topc @ sk_B)
% 0.20/0.50        | (v1_tops_2 @ sk_C_1 @ sk_B)
% 0.20/0.50        | (r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['62', '63'])).
% 0.20/0.50  thf('65', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('66', plain,
% 0.20/0.50      (((v1_tops_2 @ sk_C_1 @ sk_B)
% 0.20/0.50        | (r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1))),
% 0.20/0.50      inference('demod', [status(thm)], ['64', '65'])).
% 0.20/0.50  thf('67', plain, (~ (v1_tops_2 @ sk_C_1 @ sk_B)),
% 0.20/0.50      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.50  thf('68', plain, ((r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1)),
% 0.20/0.50      inference('clc', [status(thm)], ['66', '67'])).
% 0.20/0.50  thf('69', plain, ((v3_pre_topc @ (sk_C @ sk_C_1 @ sk_B) @ sk_A)),
% 0.20/0.50      inference('demod', [status(thm)], ['59', '68'])).
% 0.20/0.50  thf('70', plain,
% 0.20/0.50      ((r2_hidden @ (sk_C @ sk_C_1 @ sk_B) @ (u1_pre_topc @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['51', '69'])).
% 0.20/0.50  thf('71', plain, ($false), inference('demod', [status(thm)], ['46', '70'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
