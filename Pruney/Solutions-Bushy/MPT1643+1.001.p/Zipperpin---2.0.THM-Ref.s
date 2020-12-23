%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1643+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RULrozpfR7

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:54 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 391 expanded)
%              Number of leaves         :   25 ( 118 expanded)
%              Depth                    :   25
%              Number of atoms          : 1413 (4975 expanded)
%              Number of equality atoms :    4 (  11 expanded)
%              Maximal formula depth    :   17 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v12_waybel_0_type,type,(
    v12_waybel_0: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(k3_waybel_0_type,type,(
    k3_waybel_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t23_waybel_0,conjecture,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v12_waybel_0 @ B @ A )
          <=> ( r1_tarski @ ( k3_waybel_0 @ A @ B ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_orders_2 @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v12_waybel_0 @ B @ A )
            <=> ( r1_tarski @ ( k3_waybel_0 @ A @ B ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t23_waybel_0])).

thf('0',plain,
    ( ~ ( r1_tarski @ ( k3_waybel_0 @ sk_A @ sk_B ) @ sk_B )
    | ~ ( v12_waybel_0 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ ( k3_waybel_0 @ sk_A @ sk_B ) @ sk_B )
   <= ~ ( r1_tarski @ ( k3_waybel_0 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_tarski @ ( k3_waybel_0 @ sk_A @ sk_B ) @ sk_B )
    | ~ ( v12_waybel_0 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('4',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( r2_hidden @ ( sk_C @ X11 @ X12 ) @ X11 )
      | ( v12_waybel_0 @ X11 @ X12 )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d19_waybel_0])).

thf('5',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( v12_waybel_0 @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v12_waybel_0 @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( r1_orders_2 @ X12 @ ( sk_D_1 @ X11 @ X12 ) @ ( sk_C @ X11 @ X12 ) )
      | ( v12_waybel_0 @ X11 @ X12 )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d19_waybel_0])).

thf('10',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( v12_waybel_0 @ sk_B @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_B @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( v12_waybel_0 @ sk_B @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( sk_D_1 @ sk_B @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m1_subset_1 @ ( sk_C @ X11 @ X12 ) @ ( u1_struct_0 @ X12 ) )
      | ( v12_waybel_0 @ X11 @ X12 )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d19_waybel_0])).

thf('15',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( v12_waybel_0 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( v12_waybel_0 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(d15_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( k3_waybel_0 @ A @ B ) )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r2_hidden @ D @ C )
                    <=> ? [E: $i] :
                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                          & ( r1_orders_2 @ A @ D @ E )
                          & ( r2_hidden @ E @ B ) ) ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ D @ B @ A )
    <=> ( ( r2_hidden @ E @ B )
        & ( r1_orders_2 @ A @ D @ E )
        & ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X0 @ X2 @ X1 @ X4 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X4 ) )
      | ~ ( r1_orders_2 @ X4 @ X2 @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v12_waybel_0 @ sk_B @ sk_A )
      | ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ X0 )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ ( sk_C @ sk_B @ sk_A ) )
      | ( zip_tseitin_0 @ ( sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v12_waybel_0 @ sk_B @ sk_A )
      | ( zip_tseitin_0 @ ( sk_C @ sk_B @ sk_A ) @ ( sk_D_1 @ sk_B @ sk_A ) @ X0 @ sk_A )
      | ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ X0 )
      | ( v12_waybel_0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ X0 )
      | ( zip_tseitin_0 @ ( sk_C @ sk_B @ sk_A ) @ ( sk_D_1 @ sk_B @ sk_A ) @ X0 @ sk_A )
      | ( v12_waybel_0 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( v12_waybel_0 @ sk_B @ sk_A )
    | ( v12_waybel_0 @ sk_B @ sk_A )
    | ( zip_tseitin_0 @ ( sk_C @ sk_B @ sk_A ) @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['7','21'])).

thf('23',plain,
    ( ( zip_tseitin_0 @ ( sk_C @ sk_B @ sk_A ) @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B @ sk_A )
    | ( v12_waybel_0 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_waybel_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k3_waybel_0 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('25',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_orders_2 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( m1_subset_1 @ ( k3_waybel_0 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_waybel_0])).

thf('26',plain,
    ( ( m1_subset_1 @ ( k3_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ ( k3_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( k3_waybel_0 @ A @ B ) )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r2_hidden @ D @ C )
                    <=> ? [E: $i] :
                          ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ) ) ) )).

thf('29',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( X7
       != ( k3_waybel_0 @ X6 @ X5 ) )
      | ( r2_hidden @ X8 @ X7 )
      | ~ ( zip_tseitin_0 @ X9 @ X8 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X6 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('30',plain,(
    ! [X5: $i,X6: $i,X8: $i,X9: $i] :
      ( ~ ( l1_orders_2 @ X6 )
      | ~ ( m1_subset_1 @ ( k3_waybel_0 @ X6 @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X6 ) )
      | ~ ( zip_tseitin_0 @ X9 @ X8 @ X5 @ X6 )
      | ( r2_hidden @ X8 @ ( k3_waybel_0 @ X6 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ ( k3_waybel_0 @ sk_A @ sk_B ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k3_waybel_0 @ sk_A @ sk_B ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,
    ( ( v12_waybel_0 @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ ( k3_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X11 @ X12 ) @ ( u1_struct_0 @ X12 ) )
      | ( v12_waybel_0 @ X11 @ X12 )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d19_waybel_0])).

thf('38',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( v12_waybel_0 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( v12_waybel_0 @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ ( k3_waybel_0 @ sk_A @ sk_B ) )
    | ( v12_waybel_0 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['35','40'])).

thf('42',plain,
    ( ( r1_tarski @ ( k3_waybel_0 @ sk_A @ sk_B ) @ sk_B )
    | ( v12_waybel_0 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( r1_tarski @ ( k3_waybel_0 @ sk_A @ sk_B ) @ sk_B )
   <= ( r1_tarski @ ( k3_waybel_0 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['42'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('44',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ( r2_hidden @ X15 @ X17 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('45',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ sk_B )
        | ~ ( r2_hidden @ X0 @ ( k3_waybel_0 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ ( k3_waybel_0 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ( v12_waybel_0 @ sk_B @ sk_A )
      | ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B ) )
   <= ( r1_tarski @ ( k3_waybel_0 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['41','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( r2_hidden @ ( sk_D_1 @ X11 @ X12 ) @ X11 )
      | ( v12_waybel_0 @ X11 @ X12 )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d19_waybel_0])).

thf('49',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( v12_waybel_0 @ sk_B @ sk_A )
    | ~ ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v12_waybel_0 @ sk_B @ sk_A )
    | ~ ( r2_hidden @ ( sk_D_1 @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( v12_waybel_0 @ sk_B @ sk_A )
   <= ( r1_tarski @ ( k3_waybel_0 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(clc,[status(thm)],['46','51'])).

thf('53',plain,
    ( ~ ( v12_waybel_0 @ sk_B @ sk_A )
   <= ~ ( v12_waybel_0 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('54',plain,
    ( ( v12_waybel_0 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ ( k3_waybel_0 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ~ ( r1_tarski @ ( k3_waybel_0 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','54'])).

thf('56',plain,(
    ~ ( r1_tarski @ ( k3_waybel_0 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','55'])).

thf('57',plain,(
    ! [X16: $i,X18: $i] :
      ( ( r1_tarski @ X16 @ X18 )
      | ( r2_hidden @ ( sk_C_1 @ X18 @ X16 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('58',plain,(
    m1_subset_1 @ ( k3_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('59',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( X7
       != ( k3_waybel_0 @ X6 @ X5 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X8 @ X5 @ X6 ) @ X8 @ X5 @ X6 )
      | ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X6 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('60',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( l1_orders_2 @ X6 )
      | ~ ( m1_subset_1 @ ( k3_waybel_0 @ X6 @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X6 ) )
      | ~ ( r2_hidden @ X8 @ ( k3_waybel_0 @ X6 @ X5 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X8 @ X5 @ X6 ) @ X8 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k3_waybel_0 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_E_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k3_waybel_0 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    m1_subset_1 @ ( k3_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('66',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( m1_subset_1 @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k3_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_waybel_0 @ sk_A @ sk_B ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_waybel_0 @ sk_A @ sk_B ) @ X0 )
      | ( zip_tseitin_0 @ ( sk_E_1 @ ( sk_C_1 @ X0 @ ( k3_waybel_0 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ ( sk_C_1 @ X0 @ ( k3_waybel_0 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X3 ) )
      | ~ ( zip_tseitin_0 @ X0 @ X2 @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_waybel_0 @ sk_A @ sk_B ) @ X0 )
      | ( m1_subset_1 @ ( sk_E_1 @ ( sk_C_1 @ X0 @ ( k3_waybel_0 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_waybel_0 @ sk_A @ sk_B ) @ X0 )
      | ( zip_tseitin_0 @ ( sk_E_1 @ ( sk_C_1 @ X0 @ ( k3_waybel_0 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ ( sk_C_1 @ X0 @ ( k3_waybel_0 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','68'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_orders_2 @ X3 @ X2 @ X0 )
      | ~ ( zip_tseitin_0 @ X0 @ X2 @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_waybel_0 @ sk_A @ sk_B ) @ X0 )
      | ( r1_orders_2 @ sk_A @ ( sk_C_1 @ X0 @ ( k3_waybel_0 @ sk_A @ sk_B ) ) @ ( sk_E_1 @ ( sk_C_1 @ X0 @ ( k3_waybel_0 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X16: $i,X18: $i] :
      ( ( r1_tarski @ X16 @ X18 )
      | ( r2_hidden @ ( sk_C_1 @ X18 @ X16 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k3_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_waybel_0 @ sk_A @ sk_B ) @ X0 )
      | ( m1_subset_1 @ ( sk_C_1 @ X0 @ ( k3_waybel_0 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( v12_waybel_0 @ sk_B @ sk_A )
   <= ( v12_waybel_0 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['42'])).

thf('79',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v12_waybel_0 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ( r2_hidden @ X13 @ X11 )
      | ~ ( r1_orders_2 @ X12 @ X13 @ X14 )
      | ~ ( r2_hidden @ X14 @ X11 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d19_waybel_0])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ X0 )
      | ( r2_hidden @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v12_waybel_0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ X0 )
      | ( r2_hidden @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v12_waybel_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
        | ~ ( r2_hidden @ X1 @ sk_B )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v12_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['78','83'])).

thf('85',plain,
    ( ( v12_waybel_0 @ sk_B @ sk_A )
    | ( r1_tarski @ ( k3_waybel_0 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(split,[status(esa)],['42'])).

thf('86',plain,(
    v12_waybel_0 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','54','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['84','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_waybel_0 @ sk_A @ sk_B ) @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ ( sk_C_1 @ X0 @ ( k3_waybel_0 @ sk_A @ sk_B ) ) @ X1 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ ( k3_waybel_0 @ sk_A @ sk_B ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['77','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_waybel_0 @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ ( k3_waybel_0 @ sk_A @ sk_B ) ) @ sk_B )
      | ~ ( r2_hidden @ ( sk_E_1 @ ( sk_C_1 @ X0 @ ( k3_waybel_0 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_E_1 @ ( sk_C_1 @ X0 @ ( k3_waybel_0 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ ( k3_waybel_0 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_E_1 @ ( sk_C_1 @ X0 @ ( k3_waybel_0 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ ( sk_E_1 @ ( sk_C_1 @ X0 @ ( k3_waybel_0 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ sk_B )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ ( k3_waybel_0 @ sk_A @ sk_B ) ) @ sk_B )
      | ( r1_tarski @ ( k3_waybel_0 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_waybel_0 @ sk_A @ sk_B ) @ X0 )
      | ( r1_tarski @ ( k3_waybel_0 @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ ( k3_waybel_0 @ sk_A @ sk_B ) ) @ sk_B )
      | ~ ( r2_hidden @ ( sk_E_1 @ ( sk_C_1 @ X0 @ ( k3_waybel_0 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['71','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_E_1 @ ( sk_C_1 @ X0 @ ( k3_waybel_0 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ sk_B )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ ( k3_waybel_0 @ sk_A @ sk_B ) ) @ sk_B )
      | ( r1_tarski @ ( k3_waybel_0 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_waybel_0 @ sk_A @ sk_B ) @ X0 )
      | ( zip_tseitin_0 @ ( sk_E_1 @ ( sk_C_1 @ X0 @ ( k3_waybel_0 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ ( sk_C_1 @ X0 @ ( k3_waybel_0 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','68'])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X2 @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_waybel_0 @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_C_1 @ X0 @ ( k3_waybel_0 @ sk_A @ sk_B ) ) @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_waybel_0 @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ ( k3_waybel_0 @ sk_A @ sk_B ) ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['92','95'])).

thf('97',plain,(
    ! [X16: $i,X18: $i] :
      ( ( r1_tarski @ X16 @ X18 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X18 @ X16 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('98',plain,
    ( ( r1_tarski @ ( k3_waybel_0 @ sk_A @ sk_B ) @ sk_B )
    | ( r1_tarski @ ( k3_waybel_0 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    r1_tarski @ ( k3_waybel_0 @ sk_A @ sk_B ) @ sk_B ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    $false ),
    inference(demod,[status(thm)],['56','99'])).


%------------------------------------------------------------------------------
