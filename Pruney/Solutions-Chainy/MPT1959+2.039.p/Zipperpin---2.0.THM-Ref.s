%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LvSuqSUVFk

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:15 EST 2020

% Result     : Theorem 0.97s
% Output     : Refutation 0.97s
% Verified   : 
% Statistics : Number of formulae       :  182 ( 665 expanded)
%              Number of leaves         :   37 ( 212 expanded)
%              Depth                    :   27
%              Number of atoms          : 1718 (9675 expanded)
%              Number of equality atoms :   39 (  77 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_waybel_0_type,type,(
    k4_waybel_0: $i > $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_yellow_0_type,type,(
    v1_yellow_0: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(t8_waybel_7,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_yellow_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v2_waybel_0 @ B @ A )
            & ( v13_waybel_0 @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) )
          <=> ~ ( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( v1_yellow_0 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( v2_waybel_0 @ B @ A )
              & ( v13_waybel_0 @ B @ A )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) )
            <=> ~ ( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t8_waybel_7])).

thf('0',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X14: $i,X16: $i] :
      ( ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('8',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t8_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ A )
               => ( ( r2_hidden @ D @ B )
                <=> ( r2_hidden @ D @ C ) ) )
           => ( B = C ) ) ) ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( X9 = X7 )
      | ( r2_hidden @ ( sk_D @ X7 @ X9 @ X8 ) @ X9 )
      | ( r2_hidden @ ( sk_D @ X7 @ X9 @ X8 ) @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t8_subset_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('14',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( X9 = X7 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X9 @ X8 ) @ X9 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X9 @ X8 ) @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t8_subset_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('19',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['16','21'])).

thf('23',plain,
    ( ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['11','22'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('24',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ X10 @ X11 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('25',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t44_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_yellow_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( r1_orders_2 @ A @ ( k3_yellow_0 @ A ) @ B ) ) ) )).

thf('26',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ( r1_orders_2 @ X22 @ ( k3_yellow_0 @ X22 ) @ X21 )
      | ~ ( l1_orders_2 @ X22 )
      | ~ ( v1_yellow_0 @ X22 )
      | ~ ( v5_orders_2 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t44_yellow_0])).

thf('27',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_yellow_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['27','28','29','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(dt_k3_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('35',plain,(
    ! [X20: $i] :
      ( ( m1_subset_1 @ ( k3_yellow_0 @ X20 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_orders_2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_0])).

thf(d16_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( k4_waybel_0 @ A @ B ) )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r2_hidden @ D @ C )
                    <=> ? [E: $i] :
                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                          & ( r1_orders_2 @ A @ E @ D )
                          & ( r2_hidden @ E @ B ) ) ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ D @ B @ A )
    <=> ( ( r2_hidden @ E @ B )
        & ( r1_orders_2 @ A @ E @ D )
        & ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) ) ) )).

thf('36',plain,(
    ! [X23: $i,X24: $i,X25: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X23 @ X25 @ X24 @ X27 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X27 ) )
      | ~ ( r1_orders_2 @ X27 @ X23 @ X25 )
      | ~ ( r2_hidden @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_hidden @ ( k3_yellow_0 @ X0 ) @ X1 )
      | ~ ( r1_orders_2 @ X0 @ ( k3_yellow_0 @ X0 ) @ X2 )
      | ( zip_tseitin_0 @ ( k3_yellow_0 @ X0 ) @ X2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ ( k3_yellow_0 @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 )
        | ~ ( l1_orders_2 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ ( k3_yellow_0 @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( sk_B
        = ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_0 @ ( k3_yellow_0 @ sk_A ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['33','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v13_waybel_0 @ B @ A )
          <=> ( r1_tarski @ ( k4_waybel_0 @ A @ B ) @ B ) ) ) ) )).

thf('43',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( v13_waybel_0 @ X34 @ X35 )
      | ( r1_tarski @ ( k4_waybel_0 @ X35 @ X34 ) @ X34 )
      | ~ ( l1_orders_2 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t24_waybel_0])).

thf('44',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( r1_tarski @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_B )
    | ~ ( v13_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v13_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    r1_tarski @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    ! [X14: $i,X16: $i] :
      ( ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('49',plain,(
    m1_subset_1 @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('51',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( X9 = X7 )
      | ( m1_subset_1 @ ( sk_D @ X7 @ X9 @ X8 ) @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t8_subset_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k4_waybel_0 @ sk_A @ sk_B )
      = sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_B @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('54',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('55',plain,
    ( ( ( k4_waybel_0 @ sk_A @ sk_B )
      = sk_B )
    | ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ ( sk_D @ sk_B @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_B ) @ sk_B )
    | ( ( k4_waybel_0 @ sk_A @ sk_B )
      = sk_B ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ X10 @ X11 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ( r1_orders_2 @ X22 @ ( k3_yellow_0 @ X22 ) @ X21 )
      | ~ ( l1_orders_2 @ X22 )
      | ~ ( v1_yellow_0 @ X22 )
      | ~ ( v5_orders_2 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t44_yellow_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v1_yellow_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_C @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_C @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['64','65','66','67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_C @ X0 @ sk_B ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ ( k3_yellow_0 @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('72',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( zip_tseitin_0 @ ( k3_yellow_0 @ sk_A ) @ ( sk_C @ X0 @ sk_B ) @ sk_B @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('74',plain,(
    r1_tarski @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k4_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k4_waybel_0 @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k4_waybel_0 @ sk_A @ sk_B ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['73','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k4_waybel_0 @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k4_waybel_0 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('81',plain,
    ( ( r1_tarski @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    r1_tarski @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X14: $i,X16: $i] :
      ( ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('84',plain,(
    m1_subset_1 @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

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
                  = ( k4_waybel_0 @ A @ B ) )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r2_hidden @ D @ C )
                    <=> ? [E: $i] :
                          ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ) ) ) )).

thf('85',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( X30
       != ( k4_waybel_0 @ X29 @ X28 ) )
      | ( r2_hidden @ X31 @ X30 )
      | ~ ( zip_tseitin_0 @ X32 @ X31 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X29 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( l1_orders_2 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('86',plain,(
    ! [X28: $i,X29: $i,X31: $i,X32: $i] :
      ( ~ ( l1_orders_2 @ X29 )
      | ~ ( m1_subset_1 @ ( k4_waybel_0 @ X29 @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X29 ) )
      | ~ ( zip_tseitin_0 @ X32 @ X31 @ X28 @ X29 )
      | ( r2_hidden @ X31 @ ( k4_waybel_0 @ X29 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ ( k4_waybel_0 @ sk_A @ sk_B ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['84','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k4_waybel_0 @ sk_A @ sk_B ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ~ ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k4_waybel_0 @ sk_A @ sk_B ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['72','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('93',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k4_waybel_0 @ sk_A @ sk_B ) )
        | ( r1_tarski @ sk_B @ X0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('95',plain,
    ( ( ( r1_tarski @ sk_B @ ( k4_waybel_0 @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_B @ ( k4_waybel_0 @ sk_A @ sk_B ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( r1_tarski @ sk_B @ ( k4_waybel_0 @ sk_A @ sk_B ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('98',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k4_waybel_0 @ sk_A @ sk_B ) )
        | ~ ( r2_hidden @ X0 @ sk_B ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( ( ( k4_waybel_0 @ sk_A @ sk_B )
        = sk_B )
      | ( r2_hidden @ ( sk_D @ sk_B @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_B ) @ ( k4_waybel_0 @ sk_A @ sk_B ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['57','98'])).

thf('100',plain,(
    m1_subset_1 @ ( k4_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('102',plain,
    ( ( ( k4_waybel_0 @ sk_A @ sk_B )
      = sk_B )
    | ~ ( r2_hidden @ ( sk_D @ sk_B @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_B ) @ ( k4_waybel_0 @ sk_A @ sk_B ) )
    | ~ ( r2_hidden @ ( sk_D @ sk_B @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k4_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('104',plain,
    ( ~ ( r2_hidden @ ( sk_D @ sk_B @ ( k4_waybel_0 @ sk_A @ sk_B ) @ sk_B ) @ ( k4_waybel_0 @ sk_A @ sk_B ) )
    | ( ( k4_waybel_0 @ sk_A @ sk_B )
      = sk_B ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( ( k4_waybel_0 @ sk_A @ sk_B )
      = sk_B )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['99','104'])).

thf('106',plain,(
    ! [X28: $i,X29: $i,X31: $i,X32: $i] :
      ( ~ ( l1_orders_2 @ X29 )
      | ~ ( m1_subset_1 @ ( k4_waybel_0 @ X29 @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X29 ) )
      | ~ ( zip_tseitin_0 @ X32 @ X31 @ X28 @ X29 )
      | ( r2_hidden @ X31 @ ( k4_waybel_0 @ X29 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('107',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r2_hidden @ X0 @ ( k4_waybel_0 @ sk_A @ sk_B ) )
        | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( l1_orders_2 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( ( k4_waybel_0 @ sk_A @ sk_B )
      = sk_B )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['99','104'])).

thf('111',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_hidden @ X0 @ sk_B )
        | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_B @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['107','108','109','110','111'])).

thf('113',plain,
    ( ( ( sk_B
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['41','112'])).

thf('114',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('115',plain,
    ( ( ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
      | ( sk_B
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['113','114'])).

thf('116',plain,
    ( ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['16','21'])).

thf('117',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['115','116'])).

thf('118',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['118'])).

thf('120',plain,
    ( ( v1_subset_1 @ sk_B @ sk_B )
   <= ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      & ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['117','119'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('121',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( v1_subset_1 @ X37 @ X36 )
      | ( X37 != X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('122',plain,(
    ! [X36: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( v1_subset_1 @ X36 @ X36 ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('124',plain,(
    ! [X36: $i] :
      ~ ( v1_subset_1 @ X36 @ X36 ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['120','124'])).

thf('126',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['118'])).

thf('127',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    ! [X36: $i,X37: $i] :
      ( ( X37 = X36 )
      | ( v1_subset_1 @ X37 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('129',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,
    ( ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('131',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X20: $i] :
      ( ( m1_subset_1 @ ( k3_yellow_0 @ X20 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_orders_2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_0])).

thf('133',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( k3_yellow_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,
    ( ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['131','134'])).

thf('136',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('137',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
      | ( v1_xboole_0 @ sk_B ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['135','136','137'])).

thf('139',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['138','139'])).

thf('141',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['118'])).

thf('142',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','125','126','142'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LvSuqSUVFk
% 0.13/0.35  % Computer   : n021.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:49:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.97/1.17  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.97/1.17  % Solved by: fo/fo7.sh
% 0.97/1.17  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.97/1.17  % done 1104 iterations in 0.734s
% 0.97/1.17  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.97/1.17  % SZS output start Refutation
% 0.97/1.17  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.97/1.17  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.97/1.17  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.97/1.17  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.97/1.17  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.97/1.17  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.97/1.17  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.97/1.17  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.97/1.17  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.97/1.17  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.97/1.17  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.97/1.17  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.97/1.17  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.97/1.17  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.97/1.17  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.97/1.17  thf(sk_A_type, type, sk_A: $i).
% 0.97/1.17  thf(k4_waybel_0_type, type, k4_waybel_0: $i > $i > $i).
% 0.97/1.17  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.97/1.17  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.97/1.17  thf(sk_B_type, type, sk_B: $i).
% 0.97/1.17  thf(v1_yellow_0_type, type, v1_yellow_0: $i > $o).
% 0.97/1.17  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.97/1.17  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.97/1.17  thf(t8_waybel_7, conjecture,
% 0.97/1.17    (![A:$i]:
% 0.97/1.17     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.97/1.17         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 0.97/1.17         ( l1_orders_2 @ A ) ) =>
% 0.97/1.17       ( ![B:$i]:
% 0.97/1.17         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.97/1.17             ( v13_waybel_0 @ B @ A ) & 
% 0.97/1.17             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.97/1.17           ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 0.97/1.17             ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ))).
% 0.97/1.17  thf(zf_stmt_0, negated_conjecture,
% 0.97/1.17    (~( ![A:$i]:
% 0.97/1.17        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.97/1.17            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 0.97/1.17            ( l1_orders_2 @ A ) ) =>
% 0.97/1.17          ( ![B:$i]:
% 0.97/1.17            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.97/1.17                ( v13_waybel_0 @ B @ A ) & 
% 0.97/1.17                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.97/1.17              ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 0.97/1.17                ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.97/1.17    inference('cnf.neg', [status(esa)], [t8_waybel_7])).
% 0.97/1.17  thf('0', plain,
% 0.97/1.17      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)
% 0.97/1.17        | ~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('1', plain,
% 0.97/1.17      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.97/1.17       ~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.97/1.17      inference('split', [status(esa)], ['0'])).
% 0.97/1.17  thf('2', plain,
% 0.97/1.17      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf(d3_tarski, axiom,
% 0.97/1.17    (![A:$i,B:$i]:
% 0.97/1.17     ( ( r1_tarski @ A @ B ) <=>
% 0.97/1.17       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.97/1.17  thf('3', plain,
% 0.97/1.17      (![X1 : $i, X3 : $i]:
% 0.97/1.17         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.97/1.17      inference('cnf', [status(esa)], [d3_tarski])).
% 0.97/1.17  thf('4', plain,
% 0.97/1.17      (![X1 : $i, X3 : $i]:
% 0.97/1.17         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.97/1.17      inference('cnf', [status(esa)], [d3_tarski])).
% 0.97/1.17  thf('5', plain,
% 0.97/1.17      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.97/1.17      inference('sup-', [status(thm)], ['3', '4'])).
% 0.97/1.17  thf('6', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.97/1.17      inference('simplify', [status(thm)], ['5'])).
% 0.97/1.17  thf(t3_subset, axiom,
% 0.97/1.17    (![A:$i,B:$i]:
% 0.97/1.17     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.97/1.17  thf('7', plain,
% 0.97/1.17      (![X14 : $i, X16 : $i]:
% 0.97/1.17         ((m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X14 @ X16))),
% 0.97/1.17      inference('cnf', [status(esa)], [t3_subset])).
% 0.97/1.17  thf('8', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.97/1.17      inference('sup-', [status(thm)], ['6', '7'])).
% 0.97/1.17  thf(t8_subset_1, axiom,
% 0.97/1.17    (![A:$i,B:$i]:
% 0.97/1.17     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.97/1.17       ( ![C:$i]:
% 0.97/1.17         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.97/1.17           ( ( ![D:$i]:
% 0.97/1.17               ( ( m1_subset_1 @ D @ A ) =>
% 0.97/1.17                 ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.97/1.17             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.97/1.17  thf('9', plain,
% 0.97/1.17      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.97/1.17         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.97/1.17          | ((X9) = (X7))
% 0.97/1.17          | (r2_hidden @ (sk_D @ X7 @ X9 @ X8) @ X9)
% 0.97/1.17          | (r2_hidden @ (sk_D @ X7 @ X9 @ X8) @ X7)
% 0.97/1.17          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.97/1.17      inference('cnf', [status(esa)], [t8_subset_1])).
% 0.97/1.17  thf('10', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i]:
% 0.97/1.17         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.97/1.17          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.97/1.17          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 0.97/1.17          | ((X1) = (X0)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['8', '9'])).
% 0.97/1.17  thf('11', plain,
% 0.97/1.17      ((((sk_B) = (u1_struct_0 @ sk_A))
% 0.97/1.17        | (r2_hidden @ 
% 0.97/1.17           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_B)
% 0.97/1.17        | (r2_hidden @ 
% 0.97/1.17           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.97/1.17           (u1_struct_0 @ sk_A)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['2', '10'])).
% 0.97/1.17  thf('12', plain,
% 0.97/1.17      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('13', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.97/1.17      inference('sup-', [status(thm)], ['6', '7'])).
% 0.97/1.17  thf('14', plain,
% 0.97/1.17      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.97/1.17         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.97/1.17          | ((X9) = (X7))
% 0.97/1.17          | ~ (r2_hidden @ (sk_D @ X7 @ X9 @ X8) @ X9)
% 0.97/1.17          | ~ (r2_hidden @ (sk_D @ X7 @ X9 @ X8) @ X7)
% 0.97/1.17          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.97/1.17      inference('cnf', [status(esa)], [t8_subset_1])).
% 0.97/1.17  thf('15', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i]:
% 0.97/1.17         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.97/1.17          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.97/1.17          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 0.97/1.17          | ((X1) = (X0)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['13', '14'])).
% 0.97/1.17  thf('16', plain,
% 0.97/1.17      ((((sk_B) = (u1_struct_0 @ sk_A))
% 0.97/1.17        | ~ (r2_hidden @ 
% 0.97/1.17             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_B)
% 0.97/1.17        | ~ (r2_hidden @ 
% 0.97/1.17             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.97/1.17             (u1_struct_0 @ sk_A)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['12', '15'])).
% 0.97/1.17  thf('17', plain,
% 0.97/1.17      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('18', plain,
% 0.97/1.17      (![X14 : $i, X15 : $i]:
% 0.97/1.17         ((r1_tarski @ X14 @ X15) | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.97/1.17      inference('cnf', [status(esa)], [t3_subset])).
% 0.97/1.17  thf('19', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.97/1.17      inference('sup-', [status(thm)], ['17', '18'])).
% 0.97/1.17  thf('20', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.17         (~ (r2_hidden @ X0 @ X1)
% 0.97/1.17          | (r2_hidden @ X0 @ X2)
% 0.97/1.17          | ~ (r1_tarski @ X1 @ X2))),
% 0.97/1.17      inference('cnf', [status(esa)], [d3_tarski])).
% 0.97/1.17  thf('21', plain,
% 0.97/1.17      (![X0 : $i]:
% 0.97/1.17         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.97/1.17      inference('sup-', [status(thm)], ['19', '20'])).
% 0.97/1.17  thf('22', plain,
% 0.97/1.17      ((~ (r2_hidden @ 
% 0.97/1.17           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_B)
% 0.97/1.17        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.97/1.17      inference('clc', [status(thm)], ['16', '21'])).
% 0.97/1.17  thf('23', plain,
% 0.97/1.17      (((r2_hidden @ 
% 0.97/1.17         (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.97/1.17         (u1_struct_0 @ sk_A))
% 0.97/1.17        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.97/1.17      inference('clc', [status(thm)], ['11', '22'])).
% 0.97/1.17  thf(t1_subset, axiom,
% 0.97/1.17    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.97/1.17  thf('24', plain,
% 0.97/1.17      (![X10 : $i, X11 : $i]:
% 0.97/1.17         ((m1_subset_1 @ X10 @ X11) | ~ (r2_hidden @ X10 @ X11))),
% 0.97/1.17      inference('cnf', [status(esa)], [t1_subset])).
% 0.97/1.17  thf('25', plain,
% 0.97/1.17      ((((sk_B) = (u1_struct_0 @ sk_A))
% 0.97/1.17        | (m1_subset_1 @ 
% 0.97/1.17           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.97/1.17           (u1_struct_0 @ sk_A)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['23', '24'])).
% 0.97/1.17  thf(t44_yellow_0, axiom,
% 0.97/1.17    (![A:$i]:
% 0.97/1.17     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 0.97/1.17         ( v1_yellow_0 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.97/1.17       ( ![B:$i]:
% 0.97/1.17         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.97/1.17           ( r1_orders_2 @ A @ ( k3_yellow_0 @ A ) @ B ) ) ) ))).
% 0.97/1.17  thf('26', plain,
% 0.97/1.17      (![X21 : $i, X22 : $i]:
% 0.97/1.17         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 0.97/1.17          | (r1_orders_2 @ X22 @ (k3_yellow_0 @ X22) @ X21)
% 0.97/1.17          | ~ (l1_orders_2 @ X22)
% 0.97/1.17          | ~ (v1_yellow_0 @ X22)
% 0.97/1.17          | ~ (v5_orders_2 @ X22)
% 0.97/1.17          | (v2_struct_0 @ X22))),
% 0.97/1.17      inference('cnf', [status(esa)], [t44_yellow_0])).
% 0.97/1.17  thf('27', plain,
% 0.97/1.17      ((((sk_B) = (u1_struct_0 @ sk_A))
% 0.97/1.17        | (v2_struct_0 @ sk_A)
% 0.97/1.17        | ~ (v5_orders_2 @ sk_A)
% 0.97/1.17        | ~ (v1_yellow_0 @ sk_A)
% 0.97/1.17        | ~ (l1_orders_2 @ sk_A)
% 0.97/1.17        | (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 0.97/1.17           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.97/1.17      inference('sup-', [status(thm)], ['25', '26'])).
% 0.97/1.17  thf('28', plain, ((v5_orders_2 @ sk_A)),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('29', plain, ((v1_yellow_0 @ sk_A)),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('30', plain, ((l1_orders_2 @ sk_A)),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('31', plain,
% 0.97/1.17      ((((sk_B) = (u1_struct_0 @ sk_A))
% 0.97/1.17        | (v2_struct_0 @ sk_A)
% 0.97/1.17        | (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 0.97/1.17           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.97/1.17      inference('demod', [status(thm)], ['27', '28', '29', '30'])).
% 0.97/1.17  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('33', plain,
% 0.97/1.17      (((r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 0.97/1.17         (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.97/1.17        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.97/1.17      inference('clc', [status(thm)], ['31', '32'])).
% 0.97/1.17  thf('34', plain,
% 0.97/1.17      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.97/1.17         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.97/1.17      inference('split', [status(esa)], ['0'])).
% 0.97/1.17  thf(dt_k3_yellow_0, axiom,
% 0.97/1.17    (![A:$i]:
% 0.97/1.17     ( ( l1_orders_2 @ A ) =>
% 0.97/1.17       ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 0.97/1.17  thf('35', plain,
% 0.97/1.17      (![X20 : $i]:
% 0.97/1.17         ((m1_subset_1 @ (k3_yellow_0 @ X20) @ (u1_struct_0 @ X20))
% 0.97/1.17          | ~ (l1_orders_2 @ X20))),
% 0.97/1.17      inference('cnf', [status(esa)], [dt_k3_yellow_0])).
% 0.97/1.17  thf(d16_waybel_0, axiom,
% 0.97/1.17    (![A:$i]:
% 0.97/1.17     ( ( l1_orders_2 @ A ) =>
% 0.97/1.17       ( ![B:$i]:
% 0.97/1.17         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.97/1.17           ( ![C:$i]:
% 0.97/1.17             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.97/1.17               ( ( ( C ) = ( k4_waybel_0 @ A @ B ) ) <=>
% 0.97/1.17                 ( ![D:$i]:
% 0.97/1.17                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.97/1.17                     ( ( r2_hidden @ D @ C ) <=>
% 0.97/1.17                       ( ?[E:$i]:
% 0.97/1.17                         ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) & 
% 0.97/1.17                           ( r1_orders_2 @ A @ E @ D ) & ( r2_hidden @ E @ B ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.97/1.17  thf(zf_stmt_1, axiom,
% 0.97/1.17    (![E:$i,D:$i,B:$i,A:$i]:
% 0.97/1.17     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 0.97/1.17       ( ( r2_hidden @ E @ B ) & ( r1_orders_2 @ A @ E @ D ) & 
% 0.97/1.17         ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) ) ))).
% 0.97/1.17  thf('36', plain,
% 0.97/1.17      (![X23 : $i, X24 : $i, X25 : $i, X27 : $i]:
% 0.97/1.17         ((zip_tseitin_0 @ X23 @ X25 @ X24 @ X27)
% 0.97/1.17          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X27))
% 0.97/1.17          | ~ (r1_orders_2 @ X27 @ X23 @ X25)
% 0.97/1.17          | ~ (r2_hidden @ X23 @ X24))),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.97/1.17  thf('37', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.17         (~ (l1_orders_2 @ X0)
% 0.97/1.17          | ~ (r2_hidden @ (k3_yellow_0 @ X0) @ X1)
% 0.97/1.17          | ~ (r1_orders_2 @ X0 @ (k3_yellow_0 @ X0) @ X2)
% 0.97/1.17          | (zip_tseitin_0 @ (k3_yellow_0 @ X0) @ X2 @ X1 @ X0))),
% 0.97/1.17      inference('sup-', [status(thm)], ['35', '36'])).
% 0.97/1.17  thf('38', plain,
% 0.97/1.17      ((![X0 : $i]:
% 0.97/1.17          ((zip_tseitin_0 @ (k3_yellow_0 @ sk_A) @ X0 @ sk_B @ sk_A)
% 0.97/1.17           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 0.97/1.17           | ~ (l1_orders_2 @ sk_A)))
% 0.97/1.17         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['34', '37'])).
% 0.97/1.17  thf('39', plain, ((l1_orders_2 @ sk_A)),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('40', plain,
% 0.97/1.17      ((![X0 : $i]:
% 0.97/1.17          ((zip_tseitin_0 @ (k3_yellow_0 @ sk_A) @ X0 @ sk_B @ sk_A)
% 0.97/1.17           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)))
% 0.97/1.17         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.97/1.17      inference('demod', [status(thm)], ['38', '39'])).
% 0.97/1.17  thf('41', plain,
% 0.97/1.17      (((((sk_B) = (u1_struct_0 @ sk_A))
% 0.97/1.17         | (zip_tseitin_0 @ (k3_yellow_0 @ sk_A) @ 
% 0.97/1.17            (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.97/1.17            sk_B @ sk_A)))
% 0.97/1.17         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['33', '40'])).
% 0.97/1.17  thf('42', plain,
% 0.97/1.17      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf(t24_waybel_0, axiom,
% 0.97/1.17    (![A:$i]:
% 0.97/1.17     ( ( l1_orders_2 @ A ) =>
% 0.97/1.17       ( ![B:$i]:
% 0.97/1.17         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.97/1.17           ( ( v13_waybel_0 @ B @ A ) <=>
% 0.97/1.17             ( r1_tarski @ ( k4_waybel_0 @ A @ B ) @ B ) ) ) ) ))).
% 0.97/1.17  thf('43', plain,
% 0.97/1.17      (![X34 : $i, X35 : $i]:
% 0.97/1.17         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.97/1.17          | ~ (v13_waybel_0 @ X34 @ X35)
% 0.97/1.17          | (r1_tarski @ (k4_waybel_0 @ X35 @ X34) @ X34)
% 0.97/1.17          | ~ (l1_orders_2 @ X35))),
% 0.97/1.17      inference('cnf', [status(esa)], [t24_waybel_0])).
% 0.97/1.17  thf('44', plain,
% 0.97/1.17      ((~ (l1_orders_2 @ sk_A)
% 0.97/1.17        | (r1_tarski @ (k4_waybel_0 @ sk_A @ sk_B) @ sk_B)
% 0.97/1.17        | ~ (v13_waybel_0 @ sk_B @ sk_A))),
% 0.97/1.17      inference('sup-', [status(thm)], ['42', '43'])).
% 0.97/1.17  thf('45', plain, ((l1_orders_2 @ sk_A)),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('46', plain, ((v13_waybel_0 @ sk_B @ sk_A)),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('47', plain, ((r1_tarski @ (k4_waybel_0 @ sk_A @ sk_B) @ sk_B)),
% 0.97/1.17      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.97/1.17  thf('48', plain,
% 0.97/1.17      (![X14 : $i, X16 : $i]:
% 0.97/1.17         ((m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X14 @ X16))),
% 0.97/1.17      inference('cnf', [status(esa)], [t3_subset])).
% 0.97/1.17  thf('49', plain,
% 0.97/1.17      ((m1_subset_1 @ (k4_waybel_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 0.97/1.17      inference('sup-', [status(thm)], ['47', '48'])).
% 0.97/1.17  thf('50', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.97/1.17      inference('sup-', [status(thm)], ['6', '7'])).
% 0.97/1.17  thf('51', plain,
% 0.97/1.17      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.97/1.17         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.97/1.17          | ((X9) = (X7))
% 0.97/1.17          | (m1_subset_1 @ (sk_D @ X7 @ X9 @ X8) @ X8)
% 0.97/1.17          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.97/1.17      inference('cnf', [status(esa)], [t8_subset_1])).
% 0.97/1.17  thf('52', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i]:
% 0.97/1.17         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.97/1.17          | (m1_subset_1 @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.97/1.17          | ((X1) = (X0)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['50', '51'])).
% 0.97/1.17  thf('53', plain,
% 0.97/1.17      ((((k4_waybel_0 @ sk_A @ sk_B) = (sk_B))
% 0.97/1.17        | (m1_subset_1 @ (sk_D @ sk_B @ (k4_waybel_0 @ sk_A @ sk_B) @ sk_B) @ 
% 0.97/1.17           sk_B))),
% 0.97/1.17      inference('sup-', [status(thm)], ['49', '52'])).
% 0.97/1.17  thf(t2_subset, axiom,
% 0.97/1.17    (![A:$i,B:$i]:
% 0.97/1.17     ( ( m1_subset_1 @ A @ B ) =>
% 0.97/1.17       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.97/1.17  thf('54', plain,
% 0.97/1.17      (![X12 : $i, X13 : $i]:
% 0.97/1.17         ((r2_hidden @ X12 @ X13)
% 0.97/1.17          | (v1_xboole_0 @ X13)
% 0.97/1.17          | ~ (m1_subset_1 @ X12 @ X13))),
% 0.97/1.17      inference('cnf', [status(esa)], [t2_subset])).
% 0.97/1.17  thf('55', plain,
% 0.97/1.17      ((((k4_waybel_0 @ sk_A @ sk_B) = (sk_B))
% 0.97/1.17        | (v1_xboole_0 @ sk_B)
% 0.97/1.17        | (r2_hidden @ (sk_D @ sk_B @ (k4_waybel_0 @ sk_A @ sk_B) @ sk_B) @ 
% 0.97/1.17           sk_B))),
% 0.97/1.17      inference('sup-', [status(thm)], ['53', '54'])).
% 0.97/1.17  thf('56', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('57', plain,
% 0.97/1.17      (((r2_hidden @ (sk_D @ sk_B @ (k4_waybel_0 @ sk_A @ sk_B) @ sk_B) @ sk_B)
% 0.97/1.17        | ((k4_waybel_0 @ sk_A @ sk_B) = (sk_B)))),
% 0.97/1.17      inference('clc', [status(thm)], ['55', '56'])).
% 0.97/1.17  thf('58', plain,
% 0.97/1.17      (![X1 : $i, X3 : $i]:
% 0.97/1.17         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.97/1.17      inference('cnf', [status(esa)], [d3_tarski])).
% 0.97/1.17  thf('59', plain,
% 0.97/1.17      (![X0 : $i]:
% 0.97/1.17         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.97/1.17      inference('sup-', [status(thm)], ['19', '20'])).
% 0.97/1.17  thf('60', plain,
% 0.97/1.17      (![X0 : $i]:
% 0.97/1.17         ((r1_tarski @ sk_B @ X0)
% 0.97/1.17          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['58', '59'])).
% 0.97/1.17  thf('61', plain,
% 0.97/1.17      (![X10 : $i, X11 : $i]:
% 0.97/1.17         ((m1_subset_1 @ X10 @ X11) | ~ (r2_hidden @ X10 @ X11))),
% 0.97/1.17      inference('cnf', [status(esa)], [t1_subset])).
% 0.97/1.17  thf('62', plain,
% 0.97/1.17      (![X0 : $i]:
% 0.97/1.17         ((r1_tarski @ sk_B @ X0)
% 0.97/1.17          | (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['60', '61'])).
% 0.97/1.17  thf('63', plain,
% 0.97/1.17      (![X21 : $i, X22 : $i]:
% 0.97/1.17         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 0.97/1.17          | (r1_orders_2 @ X22 @ (k3_yellow_0 @ X22) @ X21)
% 0.97/1.17          | ~ (l1_orders_2 @ X22)
% 0.97/1.17          | ~ (v1_yellow_0 @ X22)
% 0.97/1.17          | ~ (v5_orders_2 @ X22)
% 0.97/1.17          | (v2_struct_0 @ X22))),
% 0.97/1.17      inference('cnf', [status(esa)], [t44_yellow_0])).
% 0.97/1.17  thf('64', plain,
% 0.97/1.17      (![X0 : $i]:
% 0.97/1.17         ((r1_tarski @ sk_B @ X0)
% 0.97/1.17          | (v2_struct_0 @ sk_A)
% 0.97/1.17          | ~ (v5_orders_2 @ sk_A)
% 0.97/1.17          | ~ (v1_yellow_0 @ sk_A)
% 0.97/1.17          | ~ (l1_orders_2 @ sk_A)
% 0.97/1.17          | (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ (sk_C @ X0 @ sk_B)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['62', '63'])).
% 0.97/1.17  thf('65', plain, ((v5_orders_2 @ sk_A)),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('66', plain, ((v1_yellow_0 @ sk_A)),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('67', plain, ((l1_orders_2 @ sk_A)),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('68', plain,
% 0.97/1.17      (![X0 : $i]:
% 0.97/1.17         ((r1_tarski @ sk_B @ X0)
% 0.97/1.17          | (v2_struct_0 @ sk_A)
% 0.97/1.17          | (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ (sk_C @ X0 @ sk_B)))),
% 0.97/1.17      inference('demod', [status(thm)], ['64', '65', '66', '67'])).
% 0.97/1.17  thf('69', plain, (~ (v2_struct_0 @ sk_A)),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('70', plain,
% 0.97/1.17      (![X0 : $i]:
% 0.97/1.17         ((r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ (sk_C @ X0 @ sk_B))
% 0.97/1.17          | (r1_tarski @ sk_B @ X0))),
% 0.97/1.17      inference('clc', [status(thm)], ['68', '69'])).
% 0.97/1.17  thf('71', plain,
% 0.97/1.17      ((![X0 : $i]:
% 0.97/1.17          ((zip_tseitin_0 @ (k3_yellow_0 @ sk_A) @ X0 @ sk_B @ sk_A)
% 0.97/1.17           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)))
% 0.97/1.17         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.97/1.17      inference('demod', [status(thm)], ['38', '39'])).
% 0.97/1.17  thf('72', plain,
% 0.97/1.17      ((![X0 : $i]:
% 0.97/1.17          ((r1_tarski @ sk_B @ X0)
% 0.97/1.17           | (zip_tseitin_0 @ (k3_yellow_0 @ sk_A) @ (sk_C @ X0 @ sk_B) @ 
% 0.97/1.17              sk_B @ sk_A)))
% 0.97/1.17         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['70', '71'])).
% 0.97/1.17  thf('73', plain,
% 0.97/1.17      (![X1 : $i, X3 : $i]:
% 0.97/1.17         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.97/1.17      inference('cnf', [status(esa)], [d3_tarski])).
% 0.97/1.17  thf('74', plain, ((r1_tarski @ (k4_waybel_0 @ sk_A @ sk_B) @ sk_B)),
% 0.97/1.17      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.97/1.17  thf('75', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.17         (~ (r2_hidden @ X0 @ X1)
% 0.97/1.17          | (r2_hidden @ X0 @ X2)
% 0.97/1.17          | ~ (r1_tarski @ X1 @ X2))),
% 0.97/1.17      inference('cnf', [status(esa)], [d3_tarski])).
% 0.97/1.17  thf('76', plain,
% 0.97/1.17      (![X0 : $i]:
% 0.97/1.17         ((r2_hidden @ X0 @ sk_B)
% 0.97/1.17          | ~ (r2_hidden @ X0 @ (k4_waybel_0 @ sk_A @ sk_B)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['74', '75'])).
% 0.97/1.17  thf('77', plain,
% 0.97/1.17      (![X0 : $i]:
% 0.97/1.17         ((r1_tarski @ (k4_waybel_0 @ sk_A @ sk_B) @ X0)
% 0.97/1.17          | (r2_hidden @ (sk_C @ X0 @ (k4_waybel_0 @ sk_A @ sk_B)) @ sk_B))),
% 0.97/1.17      inference('sup-', [status(thm)], ['73', '76'])).
% 0.97/1.17  thf('78', plain,
% 0.97/1.17      (![X0 : $i]:
% 0.97/1.17         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.97/1.17      inference('sup-', [status(thm)], ['19', '20'])).
% 0.97/1.17  thf('79', plain,
% 0.97/1.17      (![X0 : $i]:
% 0.97/1.17         ((r1_tarski @ (k4_waybel_0 @ sk_A @ sk_B) @ X0)
% 0.97/1.17          | (r2_hidden @ (sk_C @ X0 @ (k4_waybel_0 @ sk_A @ sk_B)) @ 
% 0.97/1.17             (u1_struct_0 @ sk_A)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['77', '78'])).
% 0.97/1.17  thf('80', plain,
% 0.97/1.17      (![X1 : $i, X3 : $i]:
% 0.97/1.17         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.97/1.17      inference('cnf', [status(esa)], [d3_tarski])).
% 0.97/1.17  thf('81', plain,
% 0.97/1.17      (((r1_tarski @ (k4_waybel_0 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.97/1.17        | (r1_tarski @ (k4_waybel_0 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['79', '80'])).
% 0.97/1.17  thf('82', plain,
% 0.97/1.17      ((r1_tarski @ (k4_waybel_0 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.97/1.17      inference('simplify', [status(thm)], ['81'])).
% 0.97/1.17  thf('83', plain,
% 0.97/1.17      (![X14 : $i, X16 : $i]:
% 0.97/1.17         ((m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X14 @ X16))),
% 0.97/1.17      inference('cnf', [status(esa)], [t3_subset])).
% 0.97/1.17  thf('84', plain,
% 0.97/1.17      ((m1_subset_1 @ (k4_waybel_0 @ sk_A @ sk_B) @ 
% 0.97/1.17        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['82', '83'])).
% 0.97/1.17  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.97/1.17  thf(zf_stmt_3, axiom,
% 0.97/1.17    (![A:$i]:
% 0.97/1.17     ( ( l1_orders_2 @ A ) =>
% 0.97/1.17       ( ![B:$i]:
% 0.97/1.17         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.97/1.17           ( ![C:$i]:
% 0.97/1.17             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.97/1.17               ( ( ( C ) = ( k4_waybel_0 @ A @ B ) ) <=>
% 0.97/1.17                 ( ![D:$i]:
% 0.97/1.17                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.97/1.17                     ( ( r2_hidden @ D @ C ) <=>
% 0.97/1.17                       ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.97/1.17  thf('85', plain,
% 0.97/1.17      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.97/1.17         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.97/1.17          | ((X30) != (k4_waybel_0 @ X29 @ X28))
% 0.97/1.17          | (r2_hidden @ X31 @ X30)
% 0.97/1.17          | ~ (zip_tseitin_0 @ X32 @ X31 @ X28 @ X29)
% 0.97/1.17          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X29))
% 0.97/1.17          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.97/1.17          | ~ (l1_orders_2 @ X29))),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.97/1.17  thf('86', plain,
% 0.97/1.17      (![X28 : $i, X29 : $i, X31 : $i, X32 : $i]:
% 0.97/1.17         (~ (l1_orders_2 @ X29)
% 0.97/1.17          | ~ (m1_subset_1 @ (k4_waybel_0 @ X29 @ X28) @ 
% 0.97/1.17               (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.97/1.17          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X29))
% 0.97/1.17          | ~ (zip_tseitin_0 @ X32 @ X31 @ X28 @ X29)
% 0.97/1.17          | (r2_hidden @ X31 @ (k4_waybel_0 @ X29 @ X28))
% 0.97/1.17          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29))))),
% 0.97/1.17      inference('simplify', [status(thm)], ['85'])).
% 0.97/1.17  thf('87', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i]:
% 0.97/1.17         (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.97/1.17          | (r2_hidden @ X0 @ (k4_waybel_0 @ sk_A @ sk_B))
% 0.97/1.17          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_B @ sk_A)
% 0.97/1.17          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.97/1.17          | ~ (l1_orders_2 @ sk_A))),
% 0.97/1.17      inference('sup-', [status(thm)], ['84', '86'])).
% 0.97/1.17  thf('88', plain,
% 0.97/1.17      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('89', plain, ((l1_orders_2 @ sk_A)),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('90', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i]:
% 0.97/1.17         ((r2_hidden @ X0 @ (k4_waybel_0 @ sk_A @ sk_B))
% 0.97/1.17          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_B @ sk_A)
% 0.97/1.17          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.97/1.17      inference('demod', [status(thm)], ['87', '88', '89'])).
% 0.97/1.17  thf('91', plain,
% 0.97/1.17      ((![X0 : $i]:
% 0.97/1.17          ((r1_tarski @ sk_B @ X0)
% 0.97/1.17           | ~ (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.97/1.17           | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k4_waybel_0 @ sk_A @ sk_B))))
% 0.97/1.17         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['72', '90'])).
% 0.97/1.17  thf('92', plain,
% 0.97/1.17      (![X0 : $i]:
% 0.97/1.17         ((r1_tarski @ sk_B @ X0)
% 0.97/1.17          | (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['60', '61'])).
% 0.97/1.17  thf('93', plain,
% 0.97/1.17      ((![X0 : $i]:
% 0.97/1.17          ((r2_hidden @ (sk_C @ X0 @ sk_B) @ (k4_waybel_0 @ sk_A @ sk_B))
% 0.97/1.17           | (r1_tarski @ sk_B @ X0)))
% 0.97/1.17         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.97/1.17      inference('clc', [status(thm)], ['91', '92'])).
% 0.97/1.17  thf('94', plain,
% 0.97/1.17      (![X1 : $i, X3 : $i]:
% 0.97/1.17         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.97/1.17      inference('cnf', [status(esa)], [d3_tarski])).
% 0.97/1.17  thf('95', plain,
% 0.97/1.17      ((((r1_tarski @ sk_B @ (k4_waybel_0 @ sk_A @ sk_B))
% 0.97/1.17         | (r1_tarski @ sk_B @ (k4_waybel_0 @ sk_A @ sk_B))))
% 0.97/1.17         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['93', '94'])).
% 0.97/1.17  thf('96', plain,
% 0.97/1.17      (((r1_tarski @ sk_B @ (k4_waybel_0 @ sk_A @ sk_B)))
% 0.97/1.17         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.97/1.17      inference('simplify', [status(thm)], ['95'])).
% 0.97/1.17  thf('97', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.17         (~ (r2_hidden @ X0 @ X1)
% 0.97/1.17          | (r2_hidden @ X0 @ X2)
% 0.97/1.17          | ~ (r1_tarski @ X1 @ X2))),
% 0.97/1.17      inference('cnf', [status(esa)], [d3_tarski])).
% 0.97/1.17  thf('98', plain,
% 0.97/1.17      ((![X0 : $i]:
% 0.97/1.17          ((r2_hidden @ X0 @ (k4_waybel_0 @ sk_A @ sk_B))
% 0.97/1.17           | ~ (r2_hidden @ X0 @ sk_B)))
% 0.97/1.17         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['96', '97'])).
% 0.97/1.17  thf('99', plain,
% 0.97/1.17      (((((k4_waybel_0 @ sk_A @ sk_B) = (sk_B))
% 0.97/1.17         | (r2_hidden @ (sk_D @ sk_B @ (k4_waybel_0 @ sk_A @ sk_B) @ sk_B) @ 
% 0.97/1.17            (k4_waybel_0 @ sk_A @ sk_B))))
% 0.97/1.17         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['57', '98'])).
% 0.97/1.17  thf('100', plain,
% 0.97/1.17      ((m1_subset_1 @ (k4_waybel_0 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 0.97/1.17      inference('sup-', [status(thm)], ['47', '48'])).
% 0.97/1.17  thf('101', plain,
% 0.97/1.17      (![X0 : $i, X1 : $i]:
% 0.97/1.17         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.97/1.17          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.97/1.17          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 0.97/1.17          | ((X1) = (X0)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['13', '14'])).
% 0.97/1.17  thf('102', plain,
% 0.97/1.17      ((((k4_waybel_0 @ sk_A @ sk_B) = (sk_B))
% 0.97/1.17        | ~ (r2_hidden @ (sk_D @ sk_B @ (k4_waybel_0 @ sk_A @ sk_B) @ sk_B) @ 
% 0.97/1.17             (k4_waybel_0 @ sk_A @ sk_B))
% 0.97/1.17        | ~ (r2_hidden @ (sk_D @ sk_B @ (k4_waybel_0 @ sk_A @ sk_B) @ sk_B) @ 
% 0.97/1.17             sk_B))),
% 0.97/1.17      inference('sup-', [status(thm)], ['100', '101'])).
% 0.97/1.17  thf('103', plain,
% 0.97/1.17      (![X0 : $i]:
% 0.97/1.17         ((r2_hidden @ X0 @ sk_B)
% 0.97/1.17          | ~ (r2_hidden @ X0 @ (k4_waybel_0 @ sk_A @ sk_B)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['74', '75'])).
% 0.97/1.17  thf('104', plain,
% 0.97/1.17      ((~ (r2_hidden @ (sk_D @ sk_B @ (k4_waybel_0 @ sk_A @ sk_B) @ sk_B) @ 
% 0.97/1.17           (k4_waybel_0 @ sk_A @ sk_B))
% 0.97/1.17        | ((k4_waybel_0 @ sk_A @ sk_B) = (sk_B)))),
% 0.97/1.17      inference('clc', [status(thm)], ['102', '103'])).
% 0.97/1.17  thf('105', plain,
% 0.97/1.17      ((((k4_waybel_0 @ sk_A @ sk_B) = (sk_B)))
% 0.97/1.17         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.97/1.17      inference('clc', [status(thm)], ['99', '104'])).
% 0.97/1.17  thf('106', plain,
% 0.97/1.17      (![X28 : $i, X29 : $i, X31 : $i, X32 : $i]:
% 0.97/1.17         (~ (l1_orders_2 @ X29)
% 0.97/1.17          | ~ (m1_subset_1 @ (k4_waybel_0 @ X29 @ X28) @ 
% 0.97/1.17               (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.97/1.17          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X29))
% 0.97/1.17          | ~ (zip_tseitin_0 @ X32 @ X31 @ X28 @ X29)
% 0.97/1.17          | (r2_hidden @ X31 @ (k4_waybel_0 @ X29 @ X28))
% 0.97/1.17          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29))))),
% 0.97/1.17      inference('simplify', [status(thm)], ['85'])).
% 0.97/1.17  thf('107', plain,
% 0.97/1.17      ((![X0 : $i, X1 : $i]:
% 0.97/1.17          (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.97/1.17           | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.97/1.17           | (r2_hidden @ X0 @ (k4_waybel_0 @ sk_A @ sk_B))
% 0.97/1.17           | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_B @ sk_A)
% 0.97/1.17           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.97/1.17           | ~ (l1_orders_2 @ sk_A)))
% 0.97/1.17         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['105', '106'])).
% 0.97/1.17  thf('108', plain,
% 0.97/1.17      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('109', plain,
% 0.97/1.17      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('110', plain,
% 0.97/1.17      ((((k4_waybel_0 @ sk_A @ sk_B) = (sk_B)))
% 0.97/1.17         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.97/1.17      inference('clc', [status(thm)], ['99', '104'])).
% 0.97/1.17  thf('111', plain, ((l1_orders_2 @ sk_A)),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('112', plain,
% 0.97/1.17      ((![X0 : $i, X1 : $i]:
% 0.97/1.17          ((r2_hidden @ X0 @ sk_B)
% 0.97/1.17           | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_B @ sk_A)
% 0.97/1.17           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 0.97/1.17         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.97/1.17      inference('demod', [status(thm)], ['107', '108', '109', '110', '111'])).
% 0.97/1.17  thf('113', plain,
% 0.97/1.17      (((((sk_B) = (u1_struct_0 @ sk_A))
% 0.97/1.17         | ~ (m1_subset_1 @ 
% 0.97/1.17              (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.97/1.17              (u1_struct_0 @ sk_A))
% 0.97/1.17         | (r2_hidden @ 
% 0.97/1.17            (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_B)))
% 0.97/1.17         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['41', '112'])).
% 0.97/1.17  thf('114', plain,
% 0.97/1.17      ((((sk_B) = (u1_struct_0 @ sk_A))
% 0.97/1.17        | (m1_subset_1 @ 
% 0.97/1.17           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.97/1.17           (u1_struct_0 @ sk_A)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['23', '24'])).
% 0.97/1.17  thf('115', plain,
% 0.97/1.17      ((((r2_hidden @ 
% 0.97/1.17          (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_B)
% 0.97/1.17         | ((sk_B) = (u1_struct_0 @ sk_A))))
% 0.97/1.17         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.97/1.17      inference('clc', [status(thm)], ['113', '114'])).
% 0.97/1.17  thf('116', plain,
% 0.97/1.17      ((~ (r2_hidden @ 
% 0.97/1.17           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_B)
% 0.97/1.17        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.97/1.17      inference('clc', [status(thm)], ['16', '21'])).
% 0.97/1.17  thf('117', plain,
% 0.97/1.17      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.97/1.17         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.97/1.17      inference('clc', [status(thm)], ['115', '116'])).
% 0.97/1.17  thf('118', plain,
% 0.97/1.17      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)
% 0.97/1.17        | (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('119', plain,
% 0.97/1.17      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.97/1.17         <= (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.97/1.17      inference('split', [status(esa)], ['118'])).
% 0.97/1.17  thf('120', plain,
% 0.97/1.17      (((v1_subset_1 @ sk_B @ sk_B))
% 0.97/1.17         <= (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))) & 
% 0.97/1.17             ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.97/1.17      inference('sup+', [status(thm)], ['117', '119'])).
% 0.97/1.17  thf(d7_subset_1, axiom,
% 0.97/1.17    (![A:$i,B:$i]:
% 0.97/1.17     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.97/1.17       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.97/1.17  thf('121', plain,
% 0.97/1.17      (![X36 : $i, X37 : $i]:
% 0.97/1.17         (~ (v1_subset_1 @ X37 @ X36)
% 0.97/1.17          | ((X37) != (X36))
% 0.97/1.17          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36)))),
% 0.97/1.17      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.97/1.17  thf('122', plain,
% 0.97/1.17      (![X36 : $i]:
% 0.97/1.17         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X36))
% 0.97/1.17          | ~ (v1_subset_1 @ X36 @ X36))),
% 0.97/1.17      inference('simplify', [status(thm)], ['121'])).
% 0.97/1.17  thf('123', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.97/1.17      inference('sup-', [status(thm)], ['6', '7'])).
% 0.97/1.17  thf('124', plain, (![X36 : $i]: ~ (v1_subset_1 @ X36 @ X36)),
% 0.97/1.17      inference('demod', [status(thm)], ['122', '123'])).
% 0.97/1.17  thf('125', plain,
% 0.97/1.17      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.97/1.17       ~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['120', '124'])).
% 0.97/1.17  thf('126', plain,
% 0.97/1.17      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.97/1.17       ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.97/1.17      inference('split', [status(esa)], ['118'])).
% 0.97/1.17  thf('127', plain,
% 0.97/1.17      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('128', plain,
% 0.97/1.17      (![X36 : $i, X37 : $i]:
% 0.97/1.17         (((X37) = (X36))
% 0.97/1.17          | (v1_subset_1 @ X37 @ X36)
% 0.97/1.17          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36)))),
% 0.97/1.17      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.97/1.17  thf('129', plain,
% 0.97/1.17      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.97/1.17        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['127', '128'])).
% 0.97/1.17  thf('130', plain,
% 0.97/1.17      ((~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.97/1.17         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.97/1.17      inference('split', [status(esa)], ['0'])).
% 0.97/1.17  thf('131', plain,
% 0.97/1.17      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.97/1.17         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.97/1.17      inference('sup-', [status(thm)], ['129', '130'])).
% 0.97/1.17  thf('132', plain,
% 0.97/1.17      (![X20 : $i]:
% 0.97/1.17         ((m1_subset_1 @ (k3_yellow_0 @ X20) @ (u1_struct_0 @ X20))
% 0.97/1.17          | ~ (l1_orders_2 @ X20))),
% 0.97/1.17      inference('cnf', [status(esa)], [dt_k3_yellow_0])).
% 0.97/1.17  thf('133', plain,
% 0.97/1.17      (![X12 : $i, X13 : $i]:
% 0.97/1.17         ((r2_hidden @ X12 @ X13)
% 0.97/1.17          | (v1_xboole_0 @ X13)
% 0.97/1.17          | ~ (m1_subset_1 @ X12 @ X13))),
% 0.97/1.17      inference('cnf', [status(esa)], [t2_subset])).
% 0.97/1.17  thf('134', plain,
% 0.97/1.17      (![X0 : $i]:
% 0.97/1.17         (~ (l1_orders_2 @ X0)
% 0.97/1.17          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.97/1.17          | (r2_hidden @ (k3_yellow_0 @ X0) @ (u1_struct_0 @ X0)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['132', '133'])).
% 0.97/1.17  thf('135', plain,
% 0.97/1.17      ((((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)
% 0.97/1.17         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.97/1.17         | ~ (l1_orders_2 @ sk_A)))
% 0.97/1.17         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.97/1.17      inference('sup+', [status(thm)], ['131', '134'])).
% 0.97/1.17  thf('136', plain,
% 0.97/1.17      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.97/1.17         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.97/1.17      inference('sup-', [status(thm)], ['129', '130'])).
% 0.97/1.17  thf('137', plain, ((l1_orders_2 @ sk_A)),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('138', plain,
% 0.97/1.17      ((((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B) | (v1_xboole_0 @ sk_B)))
% 0.97/1.17         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.97/1.17      inference('demod', [status(thm)], ['135', '136', '137'])).
% 0.97/1.17  thf('139', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.97/1.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.17  thf('140', plain,
% 0.97/1.17      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.97/1.17         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.97/1.17      inference('clc', [status(thm)], ['138', '139'])).
% 0.97/1.17  thf('141', plain,
% 0.97/1.17      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.97/1.17         <= (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.97/1.17      inference('split', [status(esa)], ['118'])).
% 0.97/1.17  thf('142', plain,
% 0.97/1.17      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.97/1.17       ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.97/1.17      inference('sup-', [status(thm)], ['140', '141'])).
% 0.97/1.17  thf('143', plain, ($false),
% 0.97/1.17      inference('sat_resolution*', [status(thm)], ['1', '125', '126', '142'])).
% 0.97/1.17  
% 0.97/1.17  % SZS output end Refutation
% 0.97/1.17  
% 0.97/1.18  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
