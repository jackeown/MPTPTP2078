%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kclZzy7wfq

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:15 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 214 expanded)
%              Number of leaves         :   32 (  74 expanded)
%              Depth                    :   16
%              Number of atoms          :  910 (2904 expanded)
%              Number of equality atoms :   23 (  37 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_yellow_0_type,type,(
    v1_yellow_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

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

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ( X6
       != ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('10',plain,(
    ! [X15: $i,X16: $i] :
      ( ( m1_subset_1 @ X15 @ X16 )
      | ~ ( r2_hidden @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('11',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

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

thf('12',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( X14 = X12 )
      | ( m1_subset_1 @ ( sk_D @ X12 @ X14 @ X13 ) @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t8_subset_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','13'])).

thf(t44_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_yellow_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( r1_orders_2 @ A @ ( k3_yellow_0 @ A ) @ B ) ) ) )).

thf('15',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ( r1_orders_2 @ X24 @ ( k3_yellow_0 @ X24 ) @ X23 )
      | ~ ( l1_orders_2 @ X24 )
      | ~ ( v1_yellow_0 @ X24 )
      | ~ ( v5_orders_2 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t44_yellow_0])).

thf('16',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_yellow_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17','18','19'])).

thf('21',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('25',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ( r2_hidden @ X9 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X15: $i,X16: $i] :
      ( ( m1_subset_1 @ X15 @ X16 )
      | ~ ( r2_hidden @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('29',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d20_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v13_waybel_0 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( ( r2_hidden @ C @ B )
                        & ( r1_orders_2 @ A @ C @ D ) )
                     => ( r2_hidden @ D @ B ) ) ) ) ) ) ) )).

thf('31',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v13_waybel_0 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X26 ) )
      | ( r2_hidden @ X27 @ X25 )
      | ~ ( r1_orders_2 @ X26 @ X28 @ X27 )
      | ~ ( r2_hidden @ X28 @ X25 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X26 ) )
      | ~ ( l1_orders_2 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d20_waybel_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v13_waybel_0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v13_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 )
        | ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['29','35'])).

thf('37',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('38',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( sk_B
        = ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['22','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('42',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( X14 = X12 )
      | ~ ( r2_hidden @ ( sk_D @ X12 @ X14 @ X13 ) @ X14 )
      | ~ ( r2_hidden @ ( sk_D @ X12 @ X14 @ X13 ) @ X12 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t8_subset_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('46',plain,
    ( ~ ( r2_hidden @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ~ ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['39','46'])).

thf('48',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','13'])).

thf('49',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['50'])).

thf('52',plain,
    ( ( v1_subset_1 @ sk_B @ sk_B )
   <= ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      & ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['49','51'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('53',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_subset_1 @ X30 @ X29 )
      | ( X30 != X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('54',plain,(
    ! [X29: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X29 ) )
      | ~ ( v1_subset_1 @ X29 @ X29 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('56',plain,(
    ! [X29: $i] :
      ~ ( v1_subset_1 @ X29 @ X29 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','56'])).

thf('58',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['50'])).

thf('59',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X29: $i,X30: $i] :
      ( ( X30 = X29 )
      | ( v1_subset_1 @ X30 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('61',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('63',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf(dt_k3_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('64',plain,(
    ! [X22: $i] :
      ( ( m1_subset_1 @ ( k3_yellow_0 @ X22 ) @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_orders_2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('65',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r2_hidden @ X17 @ X18 )
      | ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( k3_yellow_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['63','66'])).

thf('68',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('69',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
      | ( v1_xboole_0 @ sk_B ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['50'])).

thf('74',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','57','58','74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kclZzy7wfq
% 0.15/0.37  % Computer   : n010.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 12:53:15 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.45/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.66  % Solved by: fo/fo7.sh
% 0.45/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.66  % done 233 iterations in 0.182s
% 0.45/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.66  % SZS output start Refutation
% 0.45/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.66  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.45/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.66  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.45/0.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.66  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.45/0.66  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.66  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.45/0.66  thf(v1_yellow_0_type, type, v1_yellow_0: $i > $o).
% 0.45/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.66  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.66  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.45/0.66  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.45/0.66  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.45/0.66  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.45/0.66  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.45/0.66  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.45/0.66  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.45/0.66  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.45/0.66  thf(t8_waybel_7, conjecture,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.45/0.66         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 0.45/0.66         ( l1_orders_2 @ A ) ) =>
% 0.45/0.66       ( ![B:$i]:
% 0.45/0.66         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.45/0.66             ( v13_waybel_0 @ B @ A ) & 
% 0.45/0.66             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.66           ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 0.45/0.66             ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ))).
% 0.45/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.66    (~( ![A:$i]:
% 0.45/0.66        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.45/0.66            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 0.45/0.66            ( l1_orders_2 @ A ) ) =>
% 0.45/0.66          ( ![B:$i]:
% 0.45/0.66            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.45/0.66                ( v13_waybel_0 @ B @ A ) & 
% 0.45/0.66                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.45/0.66              ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 0.45/0.66                ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.45/0.66    inference('cnf.neg', [status(esa)], [t8_waybel_7])).
% 0.45/0.66  thf('0', plain,
% 0.45/0.66      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)
% 0.45/0.66        | ~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('1', plain,
% 0.45/0.66      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.45/0.66       ~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('split', [status(esa)], ['0'])).
% 0.45/0.66  thf('2', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(d3_tarski, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( r1_tarski @ A @ B ) <=>
% 0.45/0.66       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.45/0.66  thf('3', plain,
% 0.45/0.66      (![X1 : $i, X3 : $i]:
% 0.45/0.66         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.45/0.66      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.66  thf('4', plain,
% 0.45/0.66      (![X1 : $i, X3 : $i]:
% 0.45/0.66         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.45/0.66      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.66  thf('5', plain,
% 0.45/0.66      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['3', '4'])).
% 0.45/0.66  thf('6', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.45/0.66      inference('simplify', [status(thm)], ['5'])).
% 0.45/0.66  thf(d1_zfmisc_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.45/0.66       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.45/0.66  thf('7', plain,
% 0.45/0.66      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.45/0.66         (~ (r1_tarski @ X4 @ X5)
% 0.45/0.66          | (r2_hidden @ X4 @ X6)
% 0.45/0.66          | ((X6) != (k1_zfmisc_1 @ X5)))),
% 0.45/0.66      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.45/0.66  thf('8', plain,
% 0.45/0.66      (![X4 : $i, X5 : $i]:
% 0.45/0.66         ((r2_hidden @ X4 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X4 @ X5))),
% 0.45/0.66      inference('simplify', [status(thm)], ['7'])).
% 0.45/0.66  thf('9', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['6', '8'])).
% 0.45/0.66  thf(t1_subset, axiom,
% 0.45/0.66    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.45/0.66  thf('10', plain,
% 0.45/0.66      (![X15 : $i, X16 : $i]:
% 0.45/0.66         ((m1_subset_1 @ X15 @ X16) | ~ (r2_hidden @ X15 @ X16))),
% 0.45/0.66      inference('cnf', [status(esa)], [t1_subset])).
% 0.45/0.66  thf('11', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['9', '10'])).
% 0.45/0.66  thf(t8_subset_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.66       ( ![C:$i]:
% 0.45/0.66         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.66           ( ( ![D:$i]:
% 0.45/0.66               ( ( m1_subset_1 @ D @ A ) =>
% 0.45/0.66                 ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.45/0.66             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.45/0.66  thf('12', plain,
% 0.45/0.66      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.45/0.66          | ((X14) = (X12))
% 0.45/0.66          | (m1_subset_1 @ (sk_D @ X12 @ X14 @ X13) @ X13)
% 0.45/0.66          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 0.45/0.66      inference('cnf', [status(esa)], [t8_subset_1])).
% 0.45/0.66  thf('13', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.45/0.66          | (m1_subset_1 @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.45/0.66          | ((X1) = (X0)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['11', '12'])).
% 0.45/0.66  thf('14', plain,
% 0.45/0.66      ((((sk_B) = (u1_struct_0 @ sk_A))
% 0.45/0.66        | (m1_subset_1 @ 
% 0.45/0.66           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.45/0.66           (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['2', '13'])).
% 0.45/0.66  thf(t44_yellow_0, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 0.45/0.66         ( v1_yellow_0 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.45/0.66       ( ![B:$i]:
% 0.45/0.66         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.66           ( r1_orders_2 @ A @ ( k3_yellow_0 @ A ) @ B ) ) ) ))).
% 0.45/0.66  thf('15', plain,
% 0.45/0.66      (![X23 : $i, X24 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 0.45/0.66          | (r1_orders_2 @ X24 @ (k3_yellow_0 @ X24) @ X23)
% 0.45/0.66          | ~ (l1_orders_2 @ X24)
% 0.45/0.66          | ~ (v1_yellow_0 @ X24)
% 0.45/0.66          | ~ (v5_orders_2 @ X24)
% 0.45/0.66          | (v2_struct_0 @ X24))),
% 0.45/0.66      inference('cnf', [status(esa)], [t44_yellow_0])).
% 0.45/0.66  thf('16', plain,
% 0.45/0.66      ((((sk_B) = (u1_struct_0 @ sk_A))
% 0.45/0.66        | (v2_struct_0 @ sk_A)
% 0.45/0.66        | ~ (v5_orders_2 @ sk_A)
% 0.45/0.66        | ~ (v1_yellow_0 @ sk_A)
% 0.45/0.66        | ~ (l1_orders_2 @ sk_A)
% 0.45/0.66        | (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 0.45/0.66           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['14', '15'])).
% 0.45/0.66  thf('17', plain, ((v5_orders_2 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('18', plain, ((v1_yellow_0 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('19', plain, ((l1_orders_2 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('20', plain,
% 0.45/0.66      ((((sk_B) = (u1_struct_0 @ sk_A))
% 0.45/0.66        | (v2_struct_0 @ sk_A)
% 0.45/0.66        | (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 0.45/0.66           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.45/0.66      inference('demod', [status(thm)], ['16', '17', '18', '19'])).
% 0.45/0.66  thf('21', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('22', plain,
% 0.45/0.66      (((r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 0.45/0.66         (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.45/0.66        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('clc', [status(thm)], ['20', '21'])).
% 0.45/0.66  thf('23', plain,
% 0.45/0.66      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.45/0.66         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.45/0.66      inference('split', [status(esa)], ['0'])).
% 0.45/0.66  thf('24', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(l3_subset_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.66       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.45/0.66  thf('25', plain,
% 0.45/0.66      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.45/0.66         (~ (r2_hidden @ X9 @ X10)
% 0.45/0.66          | (r2_hidden @ X9 @ X11)
% 0.45/0.66          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.45/0.66      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.45/0.66  thf('26', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.45/0.66      inference('sup-', [status(thm)], ['24', '25'])).
% 0.45/0.66  thf('27', plain,
% 0.45/0.66      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 0.45/0.66         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['23', '26'])).
% 0.45/0.66  thf('28', plain,
% 0.45/0.66      (![X15 : $i, X16 : $i]:
% 0.45/0.66         ((m1_subset_1 @ X15 @ X16) | ~ (r2_hidden @ X15 @ X16))),
% 0.45/0.66      inference('cnf', [status(esa)], [t1_subset])).
% 0.45/0.66  thf('29', plain,
% 0.45/0.66      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 0.45/0.66         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['27', '28'])).
% 0.45/0.66  thf('30', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(d20_waybel_0, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( l1_orders_2 @ A ) =>
% 0.45/0.66       ( ![B:$i]:
% 0.45/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.66           ( ( v13_waybel_0 @ B @ A ) <=>
% 0.45/0.66             ( ![C:$i]:
% 0.45/0.66               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.66                 ( ![D:$i]:
% 0.45/0.66                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.66                     ( ( ( r2_hidden @ C @ B ) & ( r1_orders_2 @ A @ C @ D ) ) =>
% 0.45/0.66                       ( r2_hidden @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.66  thf('31', plain,
% 0.45/0.66      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.45/0.66          | ~ (v13_waybel_0 @ X25 @ X26)
% 0.45/0.66          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X26))
% 0.45/0.66          | (r2_hidden @ X27 @ X25)
% 0.45/0.66          | ~ (r1_orders_2 @ X26 @ X28 @ X27)
% 0.45/0.66          | ~ (r2_hidden @ X28 @ X25)
% 0.45/0.66          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X26))
% 0.45/0.66          | ~ (l1_orders_2 @ X26))),
% 0.45/0.66      inference('cnf', [status(esa)], [d20_waybel_0])).
% 0.45/0.66  thf('32', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (l1_orders_2 @ sk_A)
% 0.45/0.66          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.45/0.66          | ~ (r2_hidden @ X0 @ sk_B)
% 0.45/0.66          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.45/0.66          | (r2_hidden @ X1 @ sk_B)
% 0.45/0.66          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.45/0.66          | ~ (v13_waybel_0 @ sk_B @ sk_A))),
% 0.45/0.66      inference('sup-', [status(thm)], ['30', '31'])).
% 0.45/0.66  thf('33', plain, ((l1_orders_2 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('34', plain, ((v13_waybel_0 @ sk_B @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('35', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.45/0.66          | ~ (r2_hidden @ X0 @ sk_B)
% 0.45/0.66          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.45/0.66          | (r2_hidden @ X1 @ sk_B)
% 0.45/0.66          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.45/0.66  thf('36', plain,
% 0.45/0.66      ((![X0 : $i]:
% 0.45/0.66          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.45/0.66           | (r2_hidden @ X0 @ sk_B)
% 0.45/0.66           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 0.45/0.66           | ~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))
% 0.45/0.66         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['29', '35'])).
% 0.45/0.66  thf('37', plain,
% 0.45/0.66      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.45/0.66         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.45/0.66      inference('split', [status(esa)], ['0'])).
% 0.45/0.66  thf('38', plain,
% 0.45/0.66      ((![X0 : $i]:
% 0.45/0.66          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.45/0.66           | (r2_hidden @ X0 @ sk_B)
% 0.45/0.66           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)))
% 0.45/0.66         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.45/0.66      inference('demod', [status(thm)], ['36', '37'])).
% 0.45/0.66  thf('39', plain,
% 0.45/0.66      (((((sk_B) = (u1_struct_0 @ sk_A))
% 0.45/0.66         | (r2_hidden @ 
% 0.45/0.66            (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_B)
% 0.45/0.66         | ~ (m1_subset_1 @ 
% 0.45/0.66              (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.45/0.66              (u1_struct_0 @ sk_A))))
% 0.45/0.66         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['22', '38'])).
% 0.45/0.66  thf('40', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('41', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['9', '10'])).
% 0.45/0.66  thf('42', plain,
% 0.45/0.66      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.45/0.66          | ((X14) = (X12))
% 0.45/0.66          | ~ (r2_hidden @ (sk_D @ X12 @ X14 @ X13) @ X14)
% 0.45/0.66          | ~ (r2_hidden @ (sk_D @ X12 @ X14 @ X13) @ X12)
% 0.45/0.66          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 0.45/0.66      inference('cnf', [status(esa)], [t8_subset_1])).
% 0.45/0.66  thf('43', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.45/0.66          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.45/0.66          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 0.45/0.66          | ((X1) = (X0)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['41', '42'])).
% 0.45/0.66  thf('44', plain,
% 0.45/0.66      ((((sk_B) = (u1_struct_0 @ sk_A))
% 0.45/0.66        | ~ (r2_hidden @ 
% 0.45/0.66             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_B)
% 0.45/0.66        | ~ (r2_hidden @ 
% 0.45/0.66             (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.45/0.66             (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['40', '43'])).
% 0.45/0.66  thf('45', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.45/0.66      inference('sup-', [status(thm)], ['24', '25'])).
% 0.45/0.66  thf('46', plain,
% 0.45/0.66      ((~ (r2_hidden @ 
% 0.45/0.66           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_B)
% 0.45/0.66        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('clc', [status(thm)], ['44', '45'])).
% 0.45/0.66  thf('47', plain,
% 0.45/0.66      (((~ (m1_subset_1 @ 
% 0.45/0.66            (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.45/0.66            (u1_struct_0 @ sk_A))
% 0.45/0.66         | ((sk_B) = (u1_struct_0 @ sk_A))))
% 0.45/0.66         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.45/0.66      inference('clc', [status(thm)], ['39', '46'])).
% 0.45/0.66  thf('48', plain,
% 0.45/0.66      ((((sk_B) = (u1_struct_0 @ sk_A))
% 0.45/0.66        | (m1_subset_1 @ 
% 0.45/0.66           (sk_D @ (u1_struct_0 @ sk_A) @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.45/0.66           (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['2', '13'])).
% 0.45/0.66  thf('49', plain,
% 0.45/0.66      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.45/0.66         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.45/0.66      inference('clc', [status(thm)], ['47', '48'])).
% 0.45/0.66  thf('50', plain,
% 0.45/0.66      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)
% 0.45/0.66        | (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('51', plain,
% 0.45/0.66      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.45/0.66         <= (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.45/0.66      inference('split', [status(esa)], ['50'])).
% 0.45/0.66  thf('52', plain,
% 0.45/0.66      (((v1_subset_1 @ sk_B @ sk_B))
% 0.45/0.66         <= (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))) & 
% 0.45/0.66             ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['49', '51'])).
% 0.45/0.66  thf(d7_subset_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.66       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.45/0.66  thf('53', plain,
% 0.45/0.66      (![X29 : $i, X30 : $i]:
% 0.45/0.66         (~ (v1_subset_1 @ X30 @ X29)
% 0.45/0.66          | ((X30) != (X29))
% 0.45/0.66          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29)))),
% 0.45/0.66      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.45/0.66  thf('54', plain,
% 0.45/0.66      (![X29 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X29))
% 0.45/0.66          | ~ (v1_subset_1 @ X29 @ X29))),
% 0.45/0.66      inference('simplify', [status(thm)], ['53'])).
% 0.45/0.66  thf('55', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['9', '10'])).
% 0.45/0.66  thf('56', plain, (![X29 : $i]: ~ (v1_subset_1 @ X29 @ X29)),
% 0.45/0.66      inference('demod', [status(thm)], ['54', '55'])).
% 0.45/0.66  thf('57', plain,
% 0.45/0.66      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.45/0.66       ~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['52', '56'])).
% 0.45/0.66  thf('58', plain,
% 0.45/0.66      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.45/0.66       ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('split', [status(esa)], ['50'])).
% 0.45/0.66  thf('59', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('60', plain,
% 0.45/0.66      (![X29 : $i, X30 : $i]:
% 0.45/0.66         (((X30) = (X29))
% 0.45/0.66          | (v1_subset_1 @ X30 @ X29)
% 0.45/0.66          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29)))),
% 0.45/0.66      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.45/0.66  thf('61', plain,
% 0.45/0.66      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.45/0.66        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['59', '60'])).
% 0.45/0.66  thf('62', plain,
% 0.45/0.66      ((~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.45/0.66         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.45/0.66      inference('split', [status(esa)], ['0'])).
% 0.45/0.66  thf('63', plain,
% 0.45/0.66      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.45/0.66         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['61', '62'])).
% 0.45/0.66  thf(dt_k3_yellow_0, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( l1_orders_2 @ A ) =>
% 0.45/0.66       ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 0.45/0.66  thf('64', plain,
% 0.45/0.66      (![X22 : $i]:
% 0.45/0.66         ((m1_subset_1 @ (k3_yellow_0 @ X22) @ (u1_struct_0 @ X22))
% 0.45/0.66          | ~ (l1_orders_2 @ X22))),
% 0.45/0.66      inference('cnf', [status(esa)], [dt_k3_yellow_0])).
% 0.45/0.66  thf(t2_subset, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( m1_subset_1 @ A @ B ) =>
% 0.45/0.66       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.45/0.66  thf('65', plain,
% 0.45/0.66      (![X17 : $i, X18 : $i]:
% 0.45/0.66         ((r2_hidden @ X17 @ X18)
% 0.45/0.66          | (v1_xboole_0 @ X18)
% 0.45/0.66          | ~ (m1_subset_1 @ X17 @ X18))),
% 0.45/0.66      inference('cnf', [status(esa)], [t2_subset])).
% 0.45/0.66  thf('66', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (l1_orders_2 @ X0)
% 0.45/0.66          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.45/0.66          | (r2_hidden @ (k3_yellow_0 @ X0) @ (u1_struct_0 @ X0)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['64', '65'])).
% 0.45/0.66  thf('67', plain,
% 0.45/0.66      ((((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)
% 0.45/0.66         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.66         | ~ (l1_orders_2 @ sk_A)))
% 0.45/0.66         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.45/0.66      inference('sup+', [status(thm)], ['63', '66'])).
% 0.45/0.66  thf('68', plain,
% 0.45/0.66      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.45/0.66         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['61', '62'])).
% 0.45/0.66  thf('69', plain, ((l1_orders_2 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('70', plain,
% 0.45/0.66      ((((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B) | (v1_xboole_0 @ sk_B)))
% 0.45/0.66         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.45/0.66      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.45/0.66  thf('71', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('72', plain,
% 0.45/0.66      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.45/0.66         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.45/0.66      inference('clc', [status(thm)], ['70', '71'])).
% 0.45/0.66  thf('73', plain,
% 0.45/0.66      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.45/0.66         <= (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.45/0.66      inference('split', [status(esa)], ['50'])).
% 0.45/0.66  thf('74', plain,
% 0.45/0.66      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.45/0.66       ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['72', '73'])).
% 0.45/0.66  thf('75', plain, ($false),
% 0.45/0.66      inference('sat_resolution*', [status(thm)], ['1', '57', '58', '74'])).
% 0.45/0.66  
% 0.45/0.66  % SZS output end Refutation
% 0.45/0.66  
% 0.48/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
