%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yuyD8dDPjK

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:04 EST 2020

% Result     : Theorem 0.99s
% Output     : Refutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 639 expanded)
%              Number of leaves         :   24 ( 188 expanded)
%              Depth                    :   21
%              Number of atoms          : 2169 (13945 expanded)
%              Number of equality atoms :   18 (  88 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m3_yellow_6_type,type,(
    m3_yellow_6: $i > $i > $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(t33_yellow_6,conjecture,(
    ! [A: $i,B: $i] :
      ( ( l1_struct_0 @ B )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v4_relat_1 @ C @ A )
            & ( v1_funct_1 @ C )
            & ( v1_partfun1 @ C @ A ) )
         => ( ( m3_yellow_6 @ C @ A @ B )
          <=> ! [D: $i] :
                ( ( r2_hidden @ D @ A )
               => ( ~ ( v2_struct_0 @ ( k1_funct_1 @ C @ D ) )
                  & ( v4_orders_2 @ ( k1_funct_1 @ C @ D ) )
                  & ( v7_waybel_0 @ ( k1_funct_1 @ C @ D ) )
                  & ( l1_waybel_0 @ ( k1_funct_1 @ C @ D ) @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( l1_struct_0 @ B )
       => ! [C: $i] :
            ( ( ( v1_relat_1 @ C )
              & ( v4_relat_1 @ C @ A )
              & ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) )
           => ( ( m3_yellow_6 @ C @ A @ B )
            <=> ! [D: $i] :
                  ( ( r2_hidden @ D @ A )
                 => ( ~ ( v2_struct_0 @ ( k1_funct_1 @ C @ D ) )
                    & ( v4_orders_2 @ ( k1_funct_1 @ C @ D ) )
                    & ( v7_waybel_0 @ ( k1_funct_1 @ C @ D ) )
                    & ( l1_waybel_0 @ ( k1_funct_1 @ C @ D ) @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_yellow_6])).

thf('0',plain,(
    ! [X16: $i] :
      ( ~ ( r2_hidden @ X16 @ sk_A )
      | ( v4_orders_2 @ ( k1_funct_1 @ sk_C_1 @ X16 ) )
      | ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X16: $i] :
        ( ~ ( r2_hidden @ X16 @ sk_A )
        | ( v4_orders_2 @ ( k1_funct_1 @ sk_C_1 @ X16 ) ) )
    | ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X16: $i] :
      ( ~ ( r2_hidden @ X16 @ sk_A )
      | ( l1_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ X16 ) @ sk_B )
      | ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B )
   <= ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    v4_relat_1 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ~ ( l1_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ sk_D_3 ) @ sk_B )
    | ~ ( v7_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ sk_D_3 ) )
    | ~ ( v4_orders_2 @ ( k1_funct_1 @ sk_C_1 @ sk_D_3 ) )
    | ( v2_struct_0 @ ( k1_funct_1 @ sk_C_1 @ sk_D_3 ) )
    | ~ ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v2_struct_0 @ ( k1_funct_1 @ sk_C_1 @ sk_D_3 ) )
   <= ( v2_struct_0 @ ( k1_funct_1 @ sk_C_1 @ sk_D_3 ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( r2_hidden @ sk_D_3 @ sk_A )
    | ~ ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r2_hidden @ sk_D_3 @ sk_A )
   <= ( r2_hidden @ sk_D_3 @ sk_A ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,(
    v1_partfun1 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_partfun1 @ X8 @ X7 )
      | ( ( k1_relat_1 @ X8 )
        = X7 )
      | ~ ( v4_relat_1 @ X8 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v4_relat_1 @ sk_C_1 @ sk_A )
    | ( ( k1_relat_1 @ sk_C_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v4_relat_1 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference(demod,[status(thm)],['11','12','13'])).

thf(d5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_relat_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ? [D: $i] :
                  ( ( C
                    = ( k1_funct_1 @ A @ D ) )
                  & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X1: $i,X3: $i,X5: $i,X6: $i] :
      ( ( X3
       != ( k2_relat_1 @ X1 ) )
      | ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k1_relat_1 @ X1 ) )
      | ( X5
       != ( k1_funct_1 @ X1 @ X6 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('16',plain,(
    ! [X1: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r2_hidden @ X6 @ ( k1_relat_1 @ X1 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X1 @ X6 ) @ ( k2_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ ( k2_relat_1 @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_D_3 ) @ ( k2_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','20'])).

thf(d15_yellow_6,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_struct_0 @ B )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v4_relat_1 @ C @ A )
            & ( v1_funct_1 @ C )
            & ( v1_partfun1 @ C @ A ) )
         => ( ( m3_yellow_6 @ C @ A @ B )
          <=> ! [D: $i] :
                ( ( r2_hidden @ D @ ( k2_relat_1 @ C ) )
               => ( ~ ( v2_struct_0 @ D )
                  & ( v4_orders_2 @ D )
                  & ( v7_waybel_0 @ D )
                  & ( l1_waybel_0 @ D @ B ) ) ) ) ) ) )).

thf('22',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v4_relat_1 @ X9 @ X10 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_partfun1 @ X9 @ X10 )
      | ~ ( m3_yellow_6 @ X9 @ X10 @ X11 )
      | ~ ( v2_struct_0 @ X12 )
      | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X9 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d15_yellow_6])).

thf('23',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( l1_struct_0 @ X0 )
        | ~ ( v2_struct_0 @ ( k1_funct_1 @ sk_C_1 @ sk_D_3 ) )
        | ~ ( m3_yellow_6 @ sk_C_1 @ X1 @ X0 )
        | ~ ( v1_partfun1 @ sk_C_1 @ X1 )
        | ~ ( v1_funct_1 @ sk_C_1 )
        | ~ ( v4_relat_1 @ sk_C_1 @ X1 )
        | ~ ( v1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( l1_struct_0 @ X0 )
        | ~ ( v2_struct_0 @ ( k1_funct_1 @ sk_C_1 @ sk_D_3 ) )
        | ~ ( m3_yellow_6 @ sk_C_1 @ X1 @ X0 )
        | ~ ( v1_partfun1 @ sk_C_1 @ X1 )
        | ~ ( v4_relat_1 @ sk_C_1 @ X1 ) )
   <= ( r2_hidden @ sk_D_3 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v4_relat_1 @ sk_C_1 @ X0 )
        | ~ ( v1_partfun1 @ sk_C_1 @ X0 )
        | ~ ( m3_yellow_6 @ sk_C_1 @ X0 @ X1 )
        | ~ ( l1_struct_0 @ X1 ) )
   <= ( ( v2_struct_0 @ ( k1_funct_1 @ sk_C_1 @ sk_D_3 ) )
      & ( r2_hidden @ sk_D_3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','26'])).

thf('28',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_struct_0 @ X0 )
        | ~ ( m3_yellow_6 @ sk_C_1 @ sk_A @ X0 )
        | ~ ( v1_partfun1 @ sk_C_1 @ sk_A ) )
   <= ( ( v2_struct_0 @ ( k1_funct_1 @ sk_C_1 @ sk_D_3 ) )
      & ( r2_hidden @ sk_D_3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','27'])).

thf('29',plain,(
    v1_partfun1 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_struct_0 @ X0 )
        | ~ ( m3_yellow_6 @ sk_C_1 @ sk_A @ X0 ) )
   <= ( ( v2_struct_0 @ ( k1_funct_1 @ sk_C_1 @ sk_D_3 ) )
      & ( r2_hidden @ sk_D_3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( l1_struct_0 @ sk_B )
   <= ( ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B )
      & ( v2_struct_0 @ ( k1_funct_1 @ sk_C_1 @ sk_D_3 ) )
      & ( r2_hidden @ sk_D_3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','30'])).

thf('32',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ~ ( v2_struct_0 @ ( k1_funct_1 @ sk_C_1 @ sk_D_3 ) )
    | ~ ( r2_hidden @ sk_D_3 @ sk_A )
    | ~ ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B )
   <= ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('35',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_D_3 ) @ ( k2_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','20'])).

thf('36',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v4_relat_1 @ X9 @ X10 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_partfun1 @ X9 @ X10 )
      | ~ ( m3_yellow_6 @ X9 @ X10 @ X11 )
      | ( v7_waybel_0 @ X12 )
      | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X9 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d15_yellow_6])).

thf('37',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( l1_struct_0 @ X0 )
        | ( v7_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ sk_D_3 ) )
        | ~ ( m3_yellow_6 @ sk_C_1 @ X1 @ X0 )
        | ~ ( v1_partfun1 @ sk_C_1 @ X1 )
        | ~ ( v1_funct_1 @ sk_C_1 )
        | ~ ( v4_relat_1 @ sk_C_1 @ X1 )
        | ~ ( v1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( l1_struct_0 @ X0 )
        | ( v7_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ sk_D_3 ) )
        | ~ ( m3_yellow_6 @ sk_C_1 @ X1 @ X0 )
        | ~ ( v1_partfun1 @ sk_C_1 @ X1 )
        | ~ ( v4_relat_1 @ sk_C_1 @ X1 ) )
   <= ( r2_hidden @ sk_D_3 @ sk_A ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ( ~ ( v4_relat_1 @ sk_C_1 @ sk_A )
      | ~ ( v1_partfun1 @ sk_C_1 @ sk_A )
      | ( v7_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ sk_D_3 ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_D_3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','40'])).

thf('42',plain,(
    v4_relat_1 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_partfun1 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( v7_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ sk_D_3 ) )
   <= ( ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_D_3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42','43','44'])).

thf('46',plain,
    ( ~ ( v7_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ sk_D_3 ) )
   <= ~ ( v7_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ sk_D_3 ) ) ),
    inference(split,[status(esa)],['5'])).

thf('47',plain,
    ( ( v7_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ sk_D_3 ) )
    | ~ ( r2_hidden @ sk_D_3 @ sk_A )
    | ~ ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B )
   <= ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('49',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_D_3 ) @ ( k2_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','20'])).

thf('50',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v4_relat_1 @ X9 @ X10 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_partfun1 @ X9 @ X10 )
      | ~ ( m3_yellow_6 @ X9 @ X10 @ X11 )
      | ( v4_orders_2 @ X12 )
      | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X9 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d15_yellow_6])).

thf('51',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( l1_struct_0 @ X0 )
        | ( v4_orders_2 @ ( k1_funct_1 @ sk_C_1 @ sk_D_3 ) )
        | ~ ( m3_yellow_6 @ sk_C_1 @ X1 @ X0 )
        | ~ ( v1_partfun1 @ sk_C_1 @ X1 )
        | ~ ( v1_funct_1 @ sk_C_1 )
        | ~ ( v4_relat_1 @ sk_C_1 @ X1 )
        | ~ ( v1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( l1_struct_0 @ X0 )
        | ( v4_orders_2 @ ( k1_funct_1 @ sk_C_1 @ sk_D_3 ) )
        | ~ ( m3_yellow_6 @ sk_C_1 @ X1 @ X0 )
        | ~ ( v1_partfun1 @ sk_C_1 @ X1 )
        | ~ ( v4_relat_1 @ sk_C_1 @ X1 ) )
   <= ( r2_hidden @ sk_D_3 @ sk_A ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,
    ( ( ~ ( v4_relat_1 @ sk_C_1 @ sk_A )
      | ~ ( v1_partfun1 @ sk_C_1 @ sk_A )
      | ( v4_orders_2 @ ( k1_funct_1 @ sk_C_1 @ sk_D_3 ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_D_3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','54'])).

thf('56',plain,(
    v4_relat_1 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_partfun1 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( v4_orders_2 @ ( k1_funct_1 @ sk_C_1 @ sk_D_3 ) )
   <= ( ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_D_3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56','57','58'])).

thf('60',plain,
    ( ~ ( v4_orders_2 @ ( k1_funct_1 @ sk_C_1 @ sk_D_3 ) )
   <= ~ ( v4_orders_2 @ ( k1_funct_1 @ sk_C_1 @ sk_D_3 ) ) ),
    inference(split,[status(esa)],['5'])).

thf('61',plain,
    ( ( v4_orders_2 @ ( k1_funct_1 @ sk_C_1 @ sk_D_3 ) )
    | ~ ( r2_hidden @ sk_D_3 @ sk_A )
    | ~ ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B )
   <= ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('63',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_D_3 ) @ ( k2_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','20'])).

thf('64',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v4_relat_1 @ X9 @ X10 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_partfun1 @ X9 @ X10 )
      | ~ ( m3_yellow_6 @ X9 @ X10 @ X11 )
      | ( l1_waybel_0 @ X12 @ X11 )
      | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X9 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d15_yellow_6])).

thf('65',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( l1_struct_0 @ X0 )
        | ( l1_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ sk_D_3 ) @ X0 )
        | ~ ( m3_yellow_6 @ sk_C_1 @ X1 @ X0 )
        | ~ ( v1_partfun1 @ sk_C_1 @ X1 )
        | ~ ( v1_funct_1 @ sk_C_1 )
        | ~ ( v4_relat_1 @ sk_C_1 @ X1 )
        | ~ ( v1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( l1_struct_0 @ X0 )
        | ( l1_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ sk_D_3 ) @ X0 )
        | ~ ( m3_yellow_6 @ sk_C_1 @ X1 @ X0 )
        | ~ ( v1_partfun1 @ sk_C_1 @ X1 )
        | ~ ( v4_relat_1 @ sk_C_1 @ X1 ) )
   <= ( r2_hidden @ sk_D_3 @ sk_A ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,
    ( ( ~ ( v4_relat_1 @ sk_C_1 @ sk_A )
      | ~ ( v1_partfun1 @ sk_C_1 @ sk_A )
      | ( l1_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ sk_D_3 ) @ sk_B )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_D_3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['62','68'])).

thf('70',plain,(
    v4_relat_1 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_partfun1 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( l1_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ sk_D_3 ) @ sk_B )
   <= ( ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_D_3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70','71','72'])).

thf('74',plain,
    ( ~ ( l1_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ sk_D_3 ) @ sk_B )
   <= ~ ( l1_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ sk_D_3 ) @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('75',plain,
    ( ( l1_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ sk_D_3 ) @ sk_B )
    | ~ ( r2_hidden @ sk_D_3 @ sk_A )
    | ~ ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( r2_hidden @ sk_D_3 @ sk_A )
    | ~ ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['7'])).

thf('77',plain,
    ( ( v2_struct_0 @ ( k1_funct_1 @ sk_C_1 @ sk_D_3 ) )
    | ~ ( l1_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ sk_D_3 ) @ sk_B )
    | ~ ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B )
    | ~ ( v7_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ sk_D_3 ) )
    | ~ ( v4_orders_2 @ ( k1_funct_1 @ sk_C_1 @ sk_D_3 ) ) ),
    inference(split,[status(esa)],['5'])).

thf('78',plain,(
    ! [X16: $i] :
      ( ~ ( r2_hidden @ X16 @ sk_A )
      | ~ ( v2_struct_0 @ ( k1_funct_1 @ sk_C_1 @ X16 ) )
      | ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ! [X16: $i] :
        ( ~ ( r2_hidden @ X16 @ sk_A )
        | ~ ( v2_struct_0 @ ( k1_funct_1 @ sk_C_1 @ X16 ) ) )
    | ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['78'])).

thf('80',plain,
    ( ! [X16: $i] :
        ( ~ ( r2_hidden @ X16 @ sk_A )
        | ( l1_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ X16 ) @ sk_B ) )
    | ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('81',plain,(
    ! [X16: $i] :
      ( ~ ( r2_hidden @ X16 @ sk_A )
      | ( v7_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ X16 ) )
      | ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ! [X16: $i] :
        ( ~ ( r2_hidden @ X16 @ sk_A )
        | ( v7_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ X16 ) ) )
    | ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['81'])).

thf('83',plain,(
    v1_partfun1 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v4_relat_1 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v4_relat_1 @ X9 @ X10 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_partfun1 @ X9 @ X10 )
      | ( r2_hidden @ ( sk_D_2 @ X9 @ X11 ) @ ( k2_relat_1 @ X9 ) )
      | ( m3_yellow_6 @ X9 @ X10 @ X11 )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d15_yellow_6])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( m3_yellow_6 @ sk_C_1 @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ X0 ) @ ( k2_relat_1 @ sk_C_1 ) )
      | ~ ( v1_partfun1 @ sk_C_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_partfun1 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( m3_yellow_6 @ sk_C_1 @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ X0 ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['86','87','88','89'])).

thf('91',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( X3
       != ( k2_relat_1 @ X1 ) )
      | ( X4
        = ( k1_funct_1 @ X1 @ ( sk_D_1 @ X4 @ X1 ) ) )
      | ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('92',plain,(
    ! [X1: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k2_relat_1 @ X1 ) )
      | ( X4
        = ( k1_funct_1 @ X1 @ ( sk_D_1 @ X4 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( m3_yellow_6 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( sk_D_2 @ sk_C_1 @ X0 )
        = ( k1_funct_1 @ sk_C_1 @ ( sk_D_1 @ ( sk_D_2 @ sk_C_1 @ X0 ) @ sk_C_1 ) ) )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['90','92'])).

thf('94',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( m3_yellow_6 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( sk_D_2 @ sk_C_1 @ X0 )
        = ( k1_funct_1 @ sk_C_1 @ ( sk_D_1 @ ( sk_D_2 @ sk_C_1 @ X0 ) @ sk_C_1 ) ) ) ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( m3_yellow_6 @ sk_C_1 @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ X0 ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['86','87','88','89'])).

thf('98',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( X3
       != ( k2_relat_1 @ X1 ) )
      | ( r2_hidden @ ( sk_D_1 @ X4 @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('99',plain,(
    ! [X1: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k2_relat_1 @ X1 ) )
      | ( r2_hidden @ ( sk_D_1 @ X4 @ X1 ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( m3_yellow_6 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_D_2 @ sk_C_1 @ X0 ) @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['97','99'])).

thf('101',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('102',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( m3_yellow_6 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_D_2 @ sk_C_1 @ X0 ) @ sk_C_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['100','101','102','103'])).

thf('105',plain,
    ( ! [X16: $i] :
        ( ~ ( r2_hidden @ X16 @ sk_A )
        | ( v7_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ X16 ) ) )
   <= ! [X16: $i] :
        ( ~ ( r2_hidden @ X16 @ sk_A )
        | ( v7_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ X16 ) ) ) ),
    inference(split,[status(esa)],['81'])).

thf('106',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_struct_0 @ X0 )
        | ( m3_yellow_6 @ sk_C_1 @ sk_A @ X0 )
        | ( v7_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ ( sk_D_1 @ ( sk_D_2 @ sk_C_1 @ X0 ) @ sk_C_1 ) ) ) )
   <= ! [X16: $i] :
        ( ~ ( r2_hidden @ X16 @ sk_A )
        | ( v7_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ X16 ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,
    ( ! [X0: $i] :
        ( ( v7_waybel_0 @ ( sk_D_2 @ sk_C_1 @ X0 ) )
        | ~ ( l1_struct_0 @ X0 )
        | ( m3_yellow_6 @ sk_C_1 @ sk_A @ X0 )
        | ( m3_yellow_6 @ sk_C_1 @ sk_A @ X0 )
        | ~ ( l1_struct_0 @ X0 ) )
   <= ! [X16: $i] :
        ( ~ ( r2_hidden @ X16 @ sk_A )
        | ( v7_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ X16 ) ) ) ),
    inference('sup+',[status(thm)],['96','106'])).

thf('108',plain,
    ( ! [X0: $i] :
        ( ( m3_yellow_6 @ sk_C_1 @ sk_A @ X0 )
        | ~ ( l1_struct_0 @ X0 )
        | ( v7_waybel_0 @ ( sk_D_2 @ sk_C_1 @ X0 ) ) )
   <= ! [X16: $i] :
        ( ~ ( r2_hidden @ X16 @ sk_A )
        | ( v7_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,
    ( ~ ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B )
   <= ~ ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('110',plain,
    ( ( ( v7_waybel_0 @ ( sk_D_2 @ sk_C_1 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ~ ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B )
      & ! [X16: $i] :
          ( ~ ( r2_hidden @ X16 @ sk_A )
          | ( v7_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ X16 ) ) ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( v7_waybel_0 @ ( sk_D_2 @ sk_C_1 @ sk_B ) )
   <= ( ~ ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B )
      & ! [X16: $i] :
          ( ~ ( r2_hidden @ X16 @ sk_A )
          | ( v7_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ X16 ) ) ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( m3_yellow_6 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( sk_D_2 @ sk_C_1 @ X0 )
        = ( k1_funct_1 @ sk_C_1 @ ( sk_D_1 @ ( sk_D_2 @ sk_C_1 @ X0 ) @ sk_C_1 ) ) ) ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( m3_yellow_6 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_D_2 @ sk_C_1 @ X0 ) @ sk_C_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['100','101','102','103'])).

thf('115',plain,
    ( ! [X16: $i] :
        ( ~ ( r2_hidden @ X16 @ sk_A )
        | ( v4_orders_2 @ ( k1_funct_1 @ sk_C_1 @ X16 ) ) )
   <= ! [X16: $i] :
        ( ~ ( r2_hidden @ X16 @ sk_A )
        | ( v4_orders_2 @ ( k1_funct_1 @ sk_C_1 @ X16 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('116',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_struct_0 @ X0 )
        | ( m3_yellow_6 @ sk_C_1 @ sk_A @ X0 )
        | ( v4_orders_2 @ ( k1_funct_1 @ sk_C_1 @ ( sk_D_1 @ ( sk_D_2 @ sk_C_1 @ X0 ) @ sk_C_1 ) ) ) )
   <= ! [X16: $i] :
        ( ~ ( r2_hidden @ X16 @ sk_A )
        | ( v4_orders_2 @ ( k1_funct_1 @ sk_C_1 @ X16 ) ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ! [X0: $i] :
        ( ( v4_orders_2 @ ( sk_D_2 @ sk_C_1 @ X0 ) )
        | ~ ( l1_struct_0 @ X0 )
        | ( m3_yellow_6 @ sk_C_1 @ sk_A @ X0 )
        | ( m3_yellow_6 @ sk_C_1 @ sk_A @ X0 )
        | ~ ( l1_struct_0 @ X0 ) )
   <= ! [X16: $i] :
        ( ~ ( r2_hidden @ X16 @ sk_A )
        | ( v4_orders_2 @ ( k1_funct_1 @ sk_C_1 @ X16 ) ) ) ),
    inference('sup+',[status(thm)],['113','116'])).

thf('118',plain,
    ( ! [X0: $i] :
        ( ( m3_yellow_6 @ sk_C_1 @ sk_A @ X0 )
        | ~ ( l1_struct_0 @ X0 )
        | ( v4_orders_2 @ ( sk_D_2 @ sk_C_1 @ X0 ) ) )
   <= ! [X16: $i] :
        ( ~ ( r2_hidden @ X16 @ sk_A )
        | ( v4_orders_2 @ ( k1_funct_1 @ sk_C_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,
    ( ~ ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B )
   <= ~ ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('120',plain,
    ( ( ( v4_orders_2 @ ( sk_D_2 @ sk_C_1 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ~ ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B )
      & ! [X16: $i] :
          ( ~ ( r2_hidden @ X16 @ sk_A )
          | ( v4_orders_2 @ ( k1_funct_1 @ sk_C_1 @ X16 ) ) ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( v4_orders_2 @ ( sk_D_2 @ sk_C_1 @ sk_B ) )
   <= ( ~ ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B )
      & ! [X16: $i] :
          ( ~ ( r2_hidden @ X16 @ sk_A )
          | ( v4_orders_2 @ ( k1_funct_1 @ sk_C_1 @ X16 ) ) ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( m3_yellow_6 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( sk_D_2 @ sk_C_1 @ X0 )
        = ( k1_funct_1 @ sk_C_1 @ ( sk_D_1 @ ( sk_D_2 @ sk_C_1 @ X0 ) @ sk_C_1 ) ) ) ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( m3_yellow_6 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_D_2 @ sk_C_1 @ X0 ) @ sk_C_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['100','101','102','103'])).

thf('125',plain,
    ( ! [X16: $i] :
        ( ~ ( r2_hidden @ X16 @ sk_A )
        | ( l1_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ X16 ) @ sk_B ) )
   <= ! [X16: $i] :
        ( ~ ( r2_hidden @ X16 @ sk_A )
        | ( l1_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ X16 ) @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('126',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_struct_0 @ X0 )
        | ( m3_yellow_6 @ sk_C_1 @ sk_A @ X0 )
        | ( l1_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ ( sk_D_1 @ ( sk_D_2 @ sk_C_1 @ X0 ) @ sk_C_1 ) ) @ sk_B ) )
   <= ! [X16: $i] :
        ( ~ ( r2_hidden @ X16 @ sk_A )
        | ( l1_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ X16 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,
    ( ! [X0: $i] :
        ( ( l1_waybel_0 @ ( sk_D_2 @ sk_C_1 @ X0 ) @ sk_B )
        | ~ ( l1_struct_0 @ X0 )
        | ( m3_yellow_6 @ sk_C_1 @ sk_A @ X0 )
        | ( m3_yellow_6 @ sk_C_1 @ sk_A @ X0 )
        | ~ ( l1_struct_0 @ X0 ) )
   <= ! [X16: $i] :
        ( ~ ( r2_hidden @ X16 @ sk_A )
        | ( l1_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ X16 ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['123','126'])).

thf('128',plain,
    ( ! [X0: $i] :
        ( ( m3_yellow_6 @ sk_C_1 @ sk_A @ X0 )
        | ~ ( l1_struct_0 @ X0 )
        | ( l1_waybel_0 @ ( sk_D_2 @ sk_C_1 @ X0 ) @ sk_B ) )
   <= ! [X16: $i] :
        ( ~ ( r2_hidden @ X16 @ sk_A )
        | ( l1_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ X16 ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v4_relat_1 @ X9 @ X10 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_partfun1 @ X9 @ X10 )
      | ~ ( l1_waybel_0 @ ( sk_D_2 @ X9 @ X11 ) @ X11 )
      | ~ ( v7_waybel_0 @ ( sk_D_2 @ X9 @ X11 ) )
      | ~ ( v4_orders_2 @ ( sk_D_2 @ X9 @ X11 ) )
      | ( v2_struct_0 @ ( sk_D_2 @ X9 @ X11 ) )
      | ( m3_yellow_6 @ X9 @ X10 @ X11 )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d15_yellow_6])).

thf('130',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_struct_0 @ sk_B )
        | ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B )
        | ~ ( l1_struct_0 @ sk_B )
        | ( m3_yellow_6 @ sk_C_1 @ X0 @ sk_B )
        | ( v2_struct_0 @ ( sk_D_2 @ sk_C_1 @ sk_B ) )
        | ~ ( v4_orders_2 @ ( sk_D_2 @ sk_C_1 @ sk_B ) )
        | ~ ( v7_waybel_0 @ ( sk_D_2 @ sk_C_1 @ sk_B ) )
        | ~ ( v1_partfun1 @ sk_C_1 @ X0 )
        | ~ ( v1_funct_1 @ sk_C_1 )
        | ~ ( v4_relat_1 @ sk_C_1 @ X0 )
        | ~ ( v1_relat_1 @ sk_C_1 ) )
   <= ! [X16: $i] :
        ( ~ ( r2_hidden @ X16 @ sk_A )
        | ( l1_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ X16 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ! [X0: $i] :
        ( ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B )
        | ( m3_yellow_6 @ sk_C_1 @ X0 @ sk_B )
        | ( v2_struct_0 @ ( sk_D_2 @ sk_C_1 @ sk_B ) )
        | ~ ( v4_orders_2 @ ( sk_D_2 @ sk_C_1 @ sk_B ) )
        | ~ ( v7_waybel_0 @ ( sk_D_2 @ sk_C_1 @ sk_B ) )
        | ~ ( v1_partfun1 @ sk_C_1 @ X0 )
        | ~ ( v4_relat_1 @ sk_C_1 @ X0 ) )
   <= ! [X16: $i] :
        ( ~ ( r2_hidden @ X16 @ sk_A )
        | ( l1_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ X16 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['130','131','132','133','134'])).

thf('136',plain,
    ( ! [X0: $i] :
        ( ~ ( v4_relat_1 @ sk_C_1 @ X0 )
        | ~ ( v1_partfun1 @ sk_C_1 @ X0 )
        | ~ ( v7_waybel_0 @ ( sk_D_2 @ sk_C_1 @ sk_B ) )
        | ( v2_struct_0 @ ( sk_D_2 @ sk_C_1 @ sk_B ) )
        | ( m3_yellow_6 @ sk_C_1 @ X0 @ sk_B )
        | ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B ) )
   <= ( ~ ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B )
      & ! [X16: $i] :
          ( ~ ( r2_hidden @ X16 @ sk_A )
          | ( l1_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ X16 ) @ sk_B ) )
      & ! [X16: $i] :
          ( ~ ( r2_hidden @ X16 @ sk_A )
          | ( v4_orders_2 @ ( k1_funct_1 @ sk_C_1 @ X16 ) ) ) ) ),
    inference('sup-',[status(thm)],['122','135'])).

thf('137',plain,
    ( ! [X0: $i] :
        ( ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B )
        | ( m3_yellow_6 @ sk_C_1 @ X0 @ sk_B )
        | ( v2_struct_0 @ ( sk_D_2 @ sk_C_1 @ sk_B ) )
        | ~ ( v1_partfun1 @ sk_C_1 @ X0 )
        | ~ ( v4_relat_1 @ sk_C_1 @ X0 ) )
   <= ( ~ ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B )
      & ! [X16: $i] :
          ( ~ ( r2_hidden @ X16 @ sk_A )
          | ( l1_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ X16 ) @ sk_B ) )
      & ! [X16: $i] :
          ( ~ ( r2_hidden @ X16 @ sk_A )
          | ( v7_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ X16 ) ) )
      & ! [X16: $i] :
          ( ~ ( r2_hidden @ X16 @ sk_A )
          | ( v4_orders_2 @ ( k1_funct_1 @ sk_C_1 @ X16 ) ) ) ) ),
    inference('sup-',[status(thm)],['112','136'])).

thf('138',plain,
    ( ( ~ ( v4_relat_1 @ sk_C_1 @ sk_A )
      | ( v2_struct_0 @ ( sk_D_2 @ sk_C_1 @ sk_B ) )
      | ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B )
      | ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B ) )
   <= ( ~ ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B )
      & ! [X16: $i] :
          ( ~ ( r2_hidden @ X16 @ sk_A )
          | ( l1_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ X16 ) @ sk_B ) )
      & ! [X16: $i] :
          ( ~ ( r2_hidden @ X16 @ sk_A )
          | ( v7_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ X16 ) ) )
      & ! [X16: $i] :
          ( ~ ( r2_hidden @ X16 @ sk_A )
          | ( v4_orders_2 @ ( k1_funct_1 @ sk_C_1 @ X16 ) ) ) ) ),
    inference('sup-',[status(thm)],['83','137'])).

thf('139',plain,(
    v4_relat_1 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( ( v2_struct_0 @ ( sk_D_2 @ sk_C_1 @ sk_B ) )
      | ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B )
      | ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B ) )
   <= ( ~ ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B )
      & ! [X16: $i] :
          ( ~ ( r2_hidden @ X16 @ sk_A )
          | ( l1_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ X16 ) @ sk_B ) )
      & ! [X16: $i] :
          ( ~ ( r2_hidden @ X16 @ sk_A )
          | ( v7_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ X16 ) ) )
      & ! [X16: $i] :
          ( ~ ( r2_hidden @ X16 @ sk_A )
          | ( v4_orders_2 @ ( k1_funct_1 @ sk_C_1 @ X16 ) ) ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,
    ( ( ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B )
      | ( v2_struct_0 @ ( sk_D_2 @ sk_C_1 @ sk_B ) ) )
   <= ( ~ ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B )
      & ! [X16: $i] :
          ( ~ ( r2_hidden @ X16 @ sk_A )
          | ( l1_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ X16 ) @ sk_B ) )
      & ! [X16: $i] :
          ( ~ ( r2_hidden @ X16 @ sk_A )
          | ( v7_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ X16 ) ) )
      & ! [X16: $i] :
          ( ~ ( r2_hidden @ X16 @ sk_A )
          | ( v4_orders_2 @ ( k1_funct_1 @ sk_C_1 @ X16 ) ) ) ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,
    ( ~ ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B )
   <= ~ ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('143',plain,
    ( ( v2_struct_0 @ ( sk_D_2 @ sk_C_1 @ sk_B ) )
   <= ( ~ ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B )
      & ! [X16: $i] :
          ( ~ ( r2_hidden @ X16 @ sk_A )
          | ( l1_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ X16 ) @ sk_B ) )
      & ! [X16: $i] :
          ( ~ ( r2_hidden @ X16 @ sk_A )
          | ( v7_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ X16 ) ) )
      & ! [X16: $i] :
          ( ~ ( r2_hidden @ X16 @ sk_A )
          | ( v4_orders_2 @ ( k1_funct_1 @ sk_C_1 @ X16 ) ) ) ) ),
    inference(clc,[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( m3_yellow_6 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_D_2 @ sk_C_1 @ X0 ) @ sk_C_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['100','101','102','103'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( m3_yellow_6 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( sk_D_2 @ sk_C_1 @ X0 )
        = ( k1_funct_1 @ sk_C_1 @ ( sk_D_1 @ ( sk_D_2 @ sk_C_1 @ X0 ) @ sk_C_1 ) ) ) ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('146',plain,
    ( ! [X16: $i] :
        ( ~ ( r2_hidden @ X16 @ sk_A )
        | ~ ( v2_struct_0 @ ( k1_funct_1 @ sk_C_1 @ X16 ) ) )
   <= ! [X16: $i] :
        ( ~ ( r2_hidden @ X16 @ sk_A )
        | ~ ( v2_struct_0 @ ( k1_funct_1 @ sk_C_1 @ X16 ) ) ) ),
    inference(split,[status(esa)],['78'])).

thf('147',plain,
    ( ! [X0: $i] :
        ( ~ ( v2_struct_0 @ ( sk_D_2 @ sk_C_1 @ X0 ) )
        | ~ ( l1_struct_0 @ X0 )
        | ( m3_yellow_6 @ sk_C_1 @ sk_A @ X0 )
        | ~ ( r2_hidden @ ( sk_D_1 @ ( sk_D_2 @ sk_C_1 @ X0 ) @ sk_C_1 ) @ sk_A ) )
   <= ! [X16: $i] :
        ( ~ ( r2_hidden @ X16 @ sk_A )
        | ~ ( v2_struct_0 @ ( k1_funct_1 @ sk_C_1 @ X16 ) ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_struct_0 @ X0 )
        | ( m3_yellow_6 @ sk_C_1 @ sk_A @ X0 )
        | ( m3_yellow_6 @ sk_C_1 @ sk_A @ X0 )
        | ~ ( l1_struct_0 @ X0 )
        | ~ ( v2_struct_0 @ ( sk_D_2 @ sk_C_1 @ X0 ) ) )
   <= ! [X16: $i] :
        ( ~ ( r2_hidden @ X16 @ sk_A )
        | ~ ( v2_struct_0 @ ( k1_funct_1 @ sk_C_1 @ X16 ) ) ) ),
    inference('sup-',[status(thm)],['144','147'])).

thf('149',plain,
    ( ! [X0: $i] :
        ( ~ ( v2_struct_0 @ ( sk_D_2 @ sk_C_1 @ X0 ) )
        | ( m3_yellow_6 @ sk_C_1 @ sk_A @ X0 )
        | ~ ( l1_struct_0 @ X0 ) )
   <= ! [X16: $i] :
        ( ~ ( r2_hidden @ X16 @ sk_A )
        | ~ ( v2_struct_0 @ ( k1_funct_1 @ sk_C_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B ) )
   <= ( ~ ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B )
      & ! [X16: $i] :
          ( ~ ( r2_hidden @ X16 @ sk_A )
          | ( l1_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ X16 ) @ sk_B ) )
      & ! [X16: $i] :
          ( ~ ( r2_hidden @ X16 @ sk_A )
          | ( v7_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ X16 ) ) )
      & ! [X16: $i] :
          ( ~ ( r2_hidden @ X16 @ sk_A )
          | ( v4_orders_2 @ ( k1_funct_1 @ sk_C_1 @ X16 ) ) )
      & ! [X16: $i] :
          ( ~ ( r2_hidden @ X16 @ sk_A )
          | ~ ( v2_struct_0 @ ( k1_funct_1 @ sk_C_1 @ X16 ) ) ) ) ),
    inference('sup-',[status(thm)],['143','149'])).

thf('151',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B )
   <= ( ~ ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B )
      & ! [X16: $i] :
          ( ~ ( r2_hidden @ X16 @ sk_A )
          | ( l1_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ X16 ) @ sk_B ) )
      & ! [X16: $i] :
          ( ~ ( r2_hidden @ X16 @ sk_A )
          | ( v7_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ X16 ) ) )
      & ! [X16: $i] :
          ( ~ ( r2_hidden @ X16 @ sk_A )
          | ( v4_orders_2 @ ( k1_funct_1 @ sk_C_1 @ X16 ) ) )
      & ! [X16: $i] :
          ( ~ ( r2_hidden @ X16 @ sk_A )
          | ~ ( v2_struct_0 @ ( k1_funct_1 @ sk_C_1 @ X16 ) ) ) ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,
    ( ~ ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B )
   <= ~ ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('154',plain,
    ( ~ ! [X16: $i] :
          ( ~ ( r2_hidden @ X16 @ sk_A )
          | ( l1_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ X16 ) @ sk_B ) )
    | ~ ! [X16: $i] :
          ( ~ ( r2_hidden @ X16 @ sk_A )
          | ( v7_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ X16 ) ) )
    | ~ ! [X16: $i] :
          ( ~ ( r2_hidden @ X16 @ sk_A )
          | ( v4_orders_2 @ ( k1_funct_1 @ sk_C_1 @ X16 ) ) )
    | ~ ! [X16: $i] :
          ( ~ ( r2_hidden @ X16 @ sk_A )
          | ~ ( v2_struct_0 @ ( k1_funct_1 @ sk_C_1 @ X16 ) ) )
    | ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','33','47','61','75','76','77','79','80','82','154'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yuyD8dDPjK
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:40:24 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.99/1.18  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.99/1.18  % Solved by: fo/fo7.sh
% 0.99/1.18  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.99/1.18  % done 764 iterations in 0.740s
% 0.99/1.18  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.99/1.18  % SZS output start Refutation
% 0.99/1.18  thf(sk_B_type, type, sk_B: $i).
% 0.99/1.18  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.99/1.18  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.99/1.18  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.99/1.18  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.99/1.18  thf(sk_D_3_type, type, sk_D_3: $i).
% 0.99/1.18  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.99/1.18  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.99/1.18  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.99/1.18  thf(m3_yellow_6_type, type, m3_yellow_6: $i > $i > $i > $o).
% 0.99/1.18  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.99/1.18  thf(sk_A_type, type, sk_A: $i).
% 0.99/1.18  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 0.99/1.18  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.99/1.18  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.99/1.18  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.99/1.18  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.99/1.18  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.99/1.18  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.99/1.18  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.99/1.18  thf(t33_yellow_6, conjecture,
% 0.99/1.18    (![A:$i,B:$i]:
% 0.99/1.18     ( ( l1_struct_0 @ B ) =>
% 0.99/1.18       ( ![C:$i]:
% 0.99/1.18         ( ( ( v1_relat_1 @ C ) & ( v4_relat_1 @ C @ A ) & 
% 0.99/1.18             ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 0.99/1.18           ( ( m3_yellow_6 @ C @ A @ B ) <=>
% 0.99/1.18             ( ![D:$i]:
% 0.99/1.18               ( ( r2_hidden @ D @ A ) =>
% 0.99/1.18                 ( ( ~( v2_struct_0 @ ( k1_funct_1 @ C @ D ) ) ) & 
% 0.99/1.18                   ( v4_orders_2 @ ( k1_funct_1 @ C @ D ) ) & 
% 0.99/1.18                   ( v7_waybel_0 @ ( k1_funct_1 @ C @ D ) ) & 
% 0.99/1.18                   ( l1_waybel_0 @ ( k1_funct_1 @ C @ D ) @ B ) ) ) ) ) ) ) ))).
% 0.99/1.18  thf(zf_stmt_0, negated_conjecture,
% 0.99/1.18    (~( ![A:$i,B:$i]:
% 0.99/1.18        ( ( l1_struct_0 @ B ) =>
% 0.99/1.18          ( ![C:$i]:
% 0.99/1.18            ( ( ( v1_relat_1 @ C ) & ( v4_relat_1 @ C @ A ) & 
% 0.99/1.18                ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 0.99/1.18              ( ( m3_yellow_6 @ C @ A @ B ) <=>
% 0.99/1.18                ( ![D:$i]:
% 0.99/1.18                  ( ( r2_hidden @ D @ A ) =>
% 0.99/1.18                    ( ( ~( v2_struct_0 @ ( k1_funct_1 @ C @ D ) ) ) & 
% 0.99/1.18                      ( v4_orders_2 @ ( k1_funct_1 @ C @ D ) ) & 
% 0.99/1.18                      ( v7_waybel_0 @ ( k1_funct_1 @ C @ D ) ) & 
% 0.99/1.18                      ( l1_waybel_0 @ ( k1_funct_1 @ C @ D ) @ B ) ) ) ) ) ) ) ) )),
% 0.99/1.18    inference('cnf.neg', [status(esa)], [t33_yellow_6])).
% 0.99/1.18  thf('0', plain,
% 0.99/1.18      (![X16 : $i]:
% 0.99/1.18         (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18          | (v4_orders_2 @ (k1_funct_1 @ sk_C_1 @ X16))
% 0.99/1.18          | (m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B))),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('1', plain,
% 0.99/1.18      ((![X16 : $i]:
% 0.99/1.18          (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18           | (v4_orders_2 @ (k1_funct_1 @ sk_C_1 @ X16)))) | 
% 0.99/1.18       ((m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B))),
% 0.99/1.18      inference('split', [status(esa)], ['0'])).
% 0.99/1.18  thf('2', plain,
% 0.99/1.18      (![X16 : $i]:
% 0.99/1.18         (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18          | (l1_waybel_0 @ (k1_funct_1 @ sk_C_1 @ X16) @ sk_B)
% 0.99/1.18          | (m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B))),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('3', plain,
% 0.99/1.18      (((m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B))
% 0.99/1.18         <= (((m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.99/1.18      inference('split', [status(esa)], ['2'])).
% 0.99/1.18  thf('4', plain, ((v4_relat_1 @ sk_C_1 @ sk_A)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('5', plain,
% 0.99/1.18      ((~ (l1_waybel_0 @ (k1_funct_1 @ sk_C_1 @ sk_D_3) @ sk_B)
% 0.99/1.18        | ~ (v7_waybel_0 @ (k1_funct_1 @ sk_C_1 @ sk_D_3))
% 0.99/1.18        | ~ (v4_orders_2 @ (k1_funct_1 @ sk_C_1 @ sk_D_3))
% 0.99/1.18        | (v2_struct_0 @ (k1_funct_1 @ sk_C_1 @ sk_D_3))
% 0.99/1.18        | ~ (m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B))),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('6', plain,
% 0.99/1.18      (((v2_struct_0 @ (k1_funct_1 @ sk_C_1 @ sk_D_3)))
% 0.99/1.18         <= (((v2_struct_0 @ (k1_funct_1 @ sk_C_1 @ sk_D_3))))),
% 0.99/1.18      inference('split', [status(esa)], ['5'])).
% 0.99/1.18  thf('7', plain,
% 0.99/1.18      (((r2_hidden @ sk_D_3 @ sk_A) | ~ (m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B))),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('8', plain,
% 0.99/1.18      (((r2_hidden @ sk_D_3 @ sk_A)) <= (((r2_hidden @ sk_D_3 @ sk_A)))),
% 0.99/1.18      inference('split', [status(esa)], ['7'])).
% 0.99/1.18  thf('9', plain, ((v1_partfun1 @ sk_C_1 @ sk_A)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf(d4_partfun1, axiom,
% 0.99/1.18    (![A:$i,B:$i]:
% 0.99/1.18     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.99/1.18       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.99/1.18  thf('10', plain,
% 0.99/1.18      (![X7 : $i, X8 : $i]:
% 0.99/1.18         (~ (v1_partfun1 @ X8 @ X7)
% 0.99/1.18          | ((k1_relat_1 @ X8) = (X7))
% 0.99/1.18          | ~ (v4_relat_1 @ X8 @ X7)
% 0.99/1.18          | ~ (v1_relat_1 @ X8))),
% 0.99/1.18      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.99/1.18  thf('11', plain,
% 0.99/1.18      ((~ (v1_relat_1 @ sk_C_1)
% 0.99/1.18        | ~ (v4_relat_1 @ sk_C_1 @ sk_A)
% 0.99/1.18        | ((k1_relat_1 @ sk_C_1) = (sk_A)))),
% 0.99/1.18      inference('sup-', [status(thm)], ['9', '10'])).
% 0.99/1.18  thf('12', plain, ((v1_relat_1 @ sk_C_1)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('13', plain, ((v4_relat_1 @ sk_C_1 @ sk_A)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('14', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 0.99/1.18      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.99/1.18  thf(d5_funct_1, axiom,
% 0.99/1.18    (![A:$i]:
% 0.99/1.18     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.99/1.18       ( ![B:$i]:
% 0.99/1.18         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.99/1.18           ( ![C:$i]:
% 0.99/1.18             ( ( r2_hidden @ C @ B ) <=>
% 0.99/1.18               ( ?[D:$i]:
% 0.99/1.18                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.99/1.18                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.99/1.18  thf('15', plain,
% 0.99/1.18      (![X1 : $i, X3 : $i, X5 : $i, X6 : $i]:
% 0.99/1.18         (((X3) != (k2_relat_1 @ X1))
% 0.99/1.18          | (r2_hidden @ X5 @ X3)
% 0.99/1.18          | ~ (r2_hidden @ X6 @ (k1_relat_1 @ X1))
% 0.99/1.18          | ((X5) != (k1_funct_1 @ X1 @ X6))
% 0.99/1.18          | ~ (v1_funct_1 @ X1)
% 0.99/1.18          | ~ (v1_relat_1 @ X1))),
% 0.99/1.18      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.99/1.18  thf('16', plain,
% 0.99/1.18      (![X1 : $i, X6 : $i]:
% 0.99/1.18         (~ (v1_relat_1 @ X1)
% 0.99/1.18          | ~ (v1_funct_1 @ X1)
% 0.99/1.18          | ~ (r2_hidden @ X6 @ (k1_relat_1 @ X1))
% 0.99/1.18          | (r2_hidden @ (k1_funct_1 @ X1 @ X6) @ (k2_relat_1 @ X1)))),
% 0.99/1.18      inference('simplify', [status(thm)], ['15'])).
% 0.99/1.18  thf('17', plain,
% 0.99/1.18      (![X0 : $i]:
% 0.99/1.18         (~ (r2_hidden @ X0 @ sk_A)
% 0.99/1.18          | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ (k2_relat_1 @ sk_C_1))
% 0.99/1.18          | ~ (v1_funct_1 @ sk_C_1)
% 0.99/1.18          | ~ (v1_relat_1 @ sk_C_1))),
% 0.99/1.18      inference('sup-', [status(thm)], ['14', '16'])).
% 0.99/1.18  thf('18', plain, ((v1_funct_1 @ sk_C_1)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('19', plain, ((v1_relat_1 @ sk_C_1)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('20', plain,
% 0.99/1.18      (![X0 : $i]:
% 0.99/1.18         (~ (r2_hidden @ X0 @ sk_A)
% 0.99/1.18          | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ (k2_relat_1 @ sk_C_1)))),
% 0.99/1.18      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.99/1.18  thf('21', plain,
% 0.99/1.18      (((r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_D_3) @ (k2_relat_1 @ sk_C_1)))
% 0.99/1.18         <= (((r2_hidden @ sk_D_3 @ sk_A)))),
% 0.99/1.18      inference('sup-', [status(thm)], ['8', '20'])).
% 0.99/1.18  thf(d15_yellow_6, axiom,
% 0.99/1.18    (![A:$i,B:$i]:
% 0.99/1.18     ( ( l1_struct_0 @ B ) =>
% 0.99/1.18       ( ![C:$i]:
% 0.99/1.18         ( ( ( v1_relat_1 @ C ) & ( v4_relat_1 @ C @ A ) & 
% 0.99/1.18             ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 0.99/1.18           ( ( m3_yellow_6 @ C @ A @ B ) <=>
% 0.99/1.18             ( ![D:$i]:
% 0.99/1.18               ( ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) =>
% 0.99/1.18                 ( ( ~( v2_struct_0 @ D ) ) & ( v4_orders_2 @ D ) & 
% 0.99/1.18                   ( v7_waybel_0 @ D ) & ( l1_waybel_0 @ D @ B ) ) ) ) ) ) ) ))).
% 0.99/1.18  thf('22', plain,
% 0.99/1.18      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.99/1.18         (~ (v1_relat_1 @ X9)
% 0.99/1.18          | ~ (v4_relat_1 @ X9 @ X10)
% 0.99/1.18          | ~ (v1_funct_1 @ X9)
% 0.99/1.18          | ~ (v1_partfun1 @ X9 @ X10)
% 0.99/1.18          | ~ (m3_yellow_6 @ X9 @ X10 @ X11)
% 0.99/1.18          | ~ (v2_struct_0 @ X12)
% 0.99/1.18          | ~ (r2_hidden @ X12 @ (k2_relat_1 @ X9))
% 0.99/1.18          | ~ (l1_struct_0 @ X11))),
% 0.99/1.18      inference('cnf', [status(esa)], [d15_yellow_6])).
% 0.99/1.18  thf('23', plain,
% 0.99/1.18      ((![X0 : $i, X1 : $i]:
% 0.99/1.18          (~ (l1_struct_0 @ X0)
% 0.99/1.18           | ~ (v2_struct_0 @ (k1_funct_1 @ sk_C_1 @ sk_D_3))
% 0.99/1.18           | ~ (m3_yellow_6 @ sk_C_1 @ X1 @ X0)
% 0.99/1.18           | ~ (v1_partfun1 @ sk_C_1 @ X1)
% 0.99/1.18           | ~ (v1_funct_1 @ sk_C_1)
% 0.99/1.18           | ~ (v4_relat_1 @ sk_C_1 @ X1)
% 0.99/1.18           | ~ (v1_relat_1 @ sk_C_1)))
% 0.99/1.18         <= (((r2_hidden @ sk_D_3 @ sk_A)))),
% 0.99/1.18      inference('sup-', [status(thm)], ['21', '22'])).
% 0.99/1.18  thf('24', plain, ((v1_funct_1 @ sk_C_1)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('25', plain, ((v1_relat_1 @ sk_C_1)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('26', plain,
% 0.99/1.18      ((![X0 : $i, X1 : $i]:
% 0.99/1.18          (~ (l1_struct_0 @ X0)
% 0.99/1.18           | ~ (v2_struct_0 @ (k1_funct_1 @ sk_C_1 @ sk_D_3))
% 0.99/1.18           | ~ (m3_yellow_6 @ sk_C_1 @ X1 @ X0)
% 0.99/1.18           | ~ (v1_partfun1 @ sk_C_1 @ X1)
% 0.99/1.18           | ~ (v4_relat_1 @ sk_C_1 @ X1)))
% 0.99/1.18         <= (((r2_hidden @ sk_D_3 @ sk_A)))),
% 0.99/1.18      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.99/1.18  thf('27', plain,
% 0.99/1.18      ((![X0 : $i, X1 : $i]:
% 0.99/1.18          (~ (v4_relat_1 @ sk_C_1 @ X0)
% 0.99/1.18           | ~ (v1_partfun1 @ sk_C_1 @ X0)
% 0.99/1.18           | ~ (m3_yellow_6 @ sk_C_1 @ X0 @ X1)
% 0.99/1.18           | ~ (l1_struct_0 @ X1)))
% 0.99/1.18         <= (((v2_struct_0 @ (k1_funct_1 @ sk_C_1 @ sk_D_3))) & 
% 0.99/1.18             ((r2_hidden @ sk_D_3 @ sk_A)))),
% 0.99/1.18      inference('sup-', [status(thm)], ['6', '26'])).
% 0.99/1.18  thf('28', plain,
% 0.99/1.18      ((![X0 : $i]:
% 0.99/1.18          (~ (l1_struct_0 @ X0)
% 0.99/1.18           | ~ (m3_yellow_6 @ sk_C_1 @ sk_A @ X0)
% 0.99/1.18           | ~ (v1_partfun1 @ sk_C_1 @ sk_A)))
% 0.99/1.18         <= (((v2_struct_0 @ (k1_funct_1 @ sk_C_1 @ sk_D_3))) & 
% 0.99/1.18             ((r2_hidden @ sk_D_3 @ sk_A)))),
% 0.99/1.18      inference('sup-', [status(thm)], ['4', '27'])).
% 0.99/1.18  thf('29', plain, ((v1_partfun1 @ sk_C_1 @ sk_A)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('30', plain,
% 0.99/1.18      ((![X0 : $i]:
% 0.99/1.18          (~ (l1_struct_0 @ X0) | ~ (m3_yellow_6 @ sk_C_1 @ sk_A @ X0)))
% 0.99/1.18         <= (((v2_struct_0 @ (k1_funct_1 @ sk_C_1 @ sk_D_3))) & 
% 0.99/1.18             ((r2_hidden @ sk_D_3 @ sk_A)))),
% 0.99/1.18      inference('demod', [status(thm)], ['28', '29'])).
% 0.99/1.18  thf('31', plain,
% 0.99/1.18      ((~ (l1_struct_0 @ sk_B))
% 0.99/1.18         <= (((m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B)) & 
% 0.99/1.18             ((v2_struct_0 @ (k1_funct_1 @ sk_C_1 @ sk_D_3))) & 
% 0.99/1.18             ((r2_hidden @ sk_D_3 @ sk_A)))),
% 0.99/1.18      inference('sup-', [status(thm)], ['3', '30'])).
% 0.99/1.18  thf('32', plain, ((l1_struct_0 @ sk_B)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('33', plain,
% 0.99/1.18      (~ ((v2_struct_0 @ (k1_funct_1 @ sk_C_1 @ sk_D_3))) | 
% 0.99/1.18       ~ ((r2_hidden @ sk_D_3 @ sk_A)) | 
% 0.99/1.18       ~ ((m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B))),
% 0.99/1.18      inference('demod', [status(thm)], ['31', '32'])).
% 0.99/1.18  thf('34', plain,
% 0.99/1.18      (((m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B))
% 0.99/1.18         <= (((m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.99/1.18      inference('split', [status(esa)], ['2'])).
% 0.99/1.18  thf('35', plain,
% 0.99/1.18      (((r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_D_3) @ (k2_relat_1 @ sk_C_1)))
% 0.99/1.18         <= (((r2_hidden @ sk_D_3 @ sk_A)))),
% 0.99/1.18      inference('sup-', [status(thm)], ['8', '20'])).
% 0.99/1.18  thf('36', plain,
% 0.99/1.18      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.99/1.18         (~ (v1_relat_1 @ X9)
% 0.99/1.18          | ~ (v4_relat_1 @ X9 @ X10)
% 0.99/1.18          | ~ (v1_funct_1 @ X9)
% 0.99/1.18          | ~ (v1_partfun1 @ X9 @ X10)
% 0.99/1.18          | ~ (m3_yellow_6 @ X9 @ X10 @ X11)
% 0.99/1.18          | (v7_waybel_0 @ X12)
% 0.99/1.18          | ~ (r2_hidden @ X12 @ (k2_relat_1 @ X9))
% 0.99/1.18          | ~ (l1_struct_0 @ X11))),
% 0.99/1.18      inference('cnf', [status(esa)], [d15_yellow_6])).
% 0.99/1.18  thf('37', plain,
% 0.99/1.18      ((![X0 : $i, X1 : $i]:
% 0.99/1.18          (~ (l1_struct_0 @ X0)
% 0.99/1.18           | (v7_waybel_0 @ (k1_funct_1 @ sk_C_1 @ sk_D_3))
% 0.99/1.18           | ~ (m3_yellow_6 @ sk_C_1 @ X1 @ X0)
% 0.99/1.18           | ~ (v1_partfun1 @ sk_C_1 @ X1)
% 0.99/1.18           | ~ (v1_funct_1 @ sk_C_1)
% 0.99/1.18           | ~ (v4_relat_1 @ sk_C_1 @ X1)
% 0.99/1.18           | ~ (v1_relat_1 @ sk_C_1)))
% 0.99/1.18         <= (((r2_hidden @ sk_D_3 @ sk_A)))),
% 0.99/1.18      inference('sup-', [status(thm)], ['35', '36'])).
% 0.99/1.18  thf('38', plain, ((v1_funct_1 @ sk_C_1)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('39', plain, ((v1_relat_1 @ sk_C_1)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('40', plain,
% 0.99/1.18      ((![X0 : $i, X1 : $i]:
% 0.99/1.18          (~ (l1_struct_0 @ X0)
% 0.99/1.18           | (v7_waybel_0 @ (k1_funct_1 @ sk_C_1 @ sk_D_3))
% 0.99/1.18           | ~ (m3_yellow_6 @ sk_C_1 @ X1 @ X0)
% 0.99/1.18           | ~ (v1_partfun1 @ sk_C_1 @ X1)
% 0.99/1.18           | ~ (v4_relat_1 @ sk_C_1 @ X1)))
% 0.99/1.18         <= (((r2_hidden @ sk_D_3 @ sk_A)))),
% 0.99/1.18      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.99/1.18  thf('41', plain,
% 0.99/1.18      (((~ (v4_relat_1 @ sk_C_1 @ sk_A)
% 0.99/1.18         | ~ (v1_partfun1 @ sk_C_1 @ sk_A)
% 0.99/1.18         | (v7_waybel_0 @ (k1_funct_1 @ sk_C_1 @ sk_D_3))
% 0.99/1.18         | ~ (l1_struct_0 @ sk_B)))
% 0.99/1.18         <= (((m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B)) & 
% 0.99/1.18             ((r2_hidden @ sk_D_3 @ sk_A)))),
% 0.99/1.18      inference('sup-', [status(thm)], ['34', '40'])).
% 0.99/1.18  thf('42', plain, ((v4_relat_1 @ sk_C_1 @ sk_A)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('43', plain, ((v1_partfun1 @ sk_C_1 @ sk_A)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('44', plain, ((l1_struct_0 @ sk_B)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('45', plain,
% 0.99/1.18      (((v7_waybel_0 @ (k1_funct_1 @ sk_C_1 @ sk_D_3)))
% 0.99/1.18         <= (((m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B)) & 
% 0.99/1.18             ((r2_hidden @ sk_D_3 @ sk_A)))),
% 0.99/1.18      inference('demod', [status(thm)], ['41', '42', '43', '44'])).
% 0.99/1.18  thf('46', plain,
% 0.99/1.18      ((~ (v7_waybel_0 @ (k1_funct_1 @ sk_C_1 @ sk_D_3)))
% 0.99/1.18         <= (~ ((v7_waybel_0 @ (k1_funct_1 @ sk_C_1 @ sk_D_3))))),
% 0.99/1.18      inference('split', [status(esa)], ['5'])).
% 0.99/1.18  thf('47', plain,
% 0.99/1.18      (((v7_waybel_0 @ (k1_funct_1 @ sk_C_1 @ sk_D_3))) | 
% 0.99/1.18       ~ ((r2_hidden @ sk_D_3 @ sk_A)) | 
% 0.99/1.18       ~ ((m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B))),
% 0.99/1.18      inference('sup-', [status(thm)], ['45', '46'])).
% 0.99/1.18  thf('48', plain,
% 0.99/1.18      (((m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B))
% 0.99/1.18         <= (((m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.99/1.18      inference('split', [status(esa)], ['2'])).
% 0.99/1.18  thf('49', plain,
% 0.99/1.18      (((r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_D_3) @ (k2_relat_1 @ sk_C_1)))
% 0.99/1.18         <= (((r2_hidden @ sk_D_3 @ sk_A)))),
% 0.99/1.18      inference('sup-', [status(thm)], ['8', '20'])).
% 0.99/1.18  thf('50', plain,
% 0.99/1.18      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.99/1.18         (~ (v1_relat_1 @ X9)
% 0.99/1.18          | ~ (v4_relat_1 @ X9 @ X10)
% 0.99/1.18          | ~ (v1_funct_1 @ X9)
% 0.99/1.18          | ~ (v1_partfun1 @ X9 @ X10)
% 0.99/1.18          | ~ (m3_yellow_6 @ X9 @ X10 @ X11)
% 0.99/1.18          | (v4_orders_2 @ X12)
% 0.99/1.18          | ~ (r2_hidden @ X12 @ (k2_relat_1 @ X9))
% 0.99/1.18          | ~ (l1_struct_0 @ X11))),
% 0.99/1.18      inference('cnf', [status(esa)], [d15_yellow_6])).
% 0.99/1.18  thf('51', plain,
% 0.99/1.18      ((![X0 : $i, X1 : $i]:
% 0.99/1.18          (~ (l1_struct_0 @ X0)
% 0.99/1.18           | (v4_orders_2 @ (k1_funct_1 @ sk_C_1 @ sk_D_3))
% 0.99/1.18           | ~ (m3_yellow_6 @ sk_C_1 @ X1 @ X0)
% 0.99/1.18           | ~ (v1_partfun1 @ sk_C_1 @ X1)
% 0.99/1.18           | ~ (v1_funct_1 @ sk_C_1)
% 0.99/1.18           | ~ (v4_relat_1 @ sk_C_1 @ X1)
% 0.99/1.18           | ~ (v1_relat_1 @ sk_C_1)))
% 0.99/1.18         <= (((r2_hidden @ sk_D_3 @ sk_A)))),
% 0.99/1.18      inference('sup-', [status(thm)], ['49', '50'])).
% 0.99/1.18  thf('52', plain, ((v1_funct_1 @ sk_C_1)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('53', plain, ((v1_relat_1 @ sk_C_1)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('54', plain,
% 0.99/1.18      ((![X0 : $i, X1 : $i]:
% 0.99/1.18          (~ (l1_struct_0 @ X0)
% 0.99/1.18           | (v4_orders_2 @ (k1_funct_1 @ sk_C_1 @ sk_D_3))
% 0.99/1.18           | ~ (m3_yellow_6 @ sk_C_1 @ X1 @ X0)
% 0.99/1.18           | ~ (v1_partfun1 @ sk_C_1 @ X1)
% 0.99/1.18           | ~ (v4_relat_1 @ sk_C_1 @ X1)))
% 0.99/1.18         <= (((r2_hidden @ sk_D_3 @ sk_A)))),
% 0.99/1.18      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.99/1.18  thf('55', plain,
% 0.99/1.18      (((~ (v4_relat_1 @ sk_C_1 @ sk_A)
% 0.99/1.18         | ~ (v1_partfun1 @ sk_C_1 @ sk_A)
% 0.99/1.18         | (v4_orders_2 @ (k1_funct_1 @ sk_C_1 @ sk_D_3))
% 0.99/1.18         | ~ (l1_struct_0 @ sk_B)))
% 0.99/1.18         <= (((m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B)) & 
% 0.99/1.18             ((r2_hidden @ sk_D_3 @ sk_A)))),
% 0.99/1.18      inference('sup-', [status(thm)], ['48', '54'])).
% 0.99/1.18  thf('56', plain, ((v4_relat_1 @ sk_C_1 @ sk_A)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('57', plain, ((v1_partfun1 @ sk_C_1 @ sk_A)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('58', plain, ((l1_struct_0 @ sk_B)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('59', plain,
% 0.99/1.18      (((v4_orders_2 @ (k1_funct_1 @ sk_C_1 @ sk_D_3)))
% 0.99/1.18         <= (((m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B)) & 
% 0.99/1.18             ((r2_hidden @ sk_D_3 @ sk_A)))),
% 0.99/1.18      inference('demod', [status(thm)], ['55', '56', '57', '58'])).
% 0.99/1.18  thf('60', plain,
% 0.99/1.18      ((~ (v4_orders_2 @ (k1_funct_1 @ sk_C_1 @ sk_D_3)))
% 0.99/1.18         <= (~ ((v4_orders_2 @ (k1_funct_1 @ sk_C_1 @ sk_D_3))))),
% 0.99/1.18      inference('split', [status(esa)], ['5'])).
% 0.99/1.18  thf('61', plain,
% 0.99/1.18      (((v4_orders_2 @ (k1_funct_1 @ sk_C_1 @ sk_D_3))) | 
% 0.99/1.18       ~ ((r2_hidden @ sk_D_3 @ sk_A)) | 
% 0.99/1.18       ~ ((m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B))),
% 0.99/1.18      inference('sup-', [status(thm)], ['59', '60'])).
% 0.99/1.18  thf('62', plain,
% 0.99/1.18      (((m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B))
% 0.99/1.18         <= (((m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.99/1.18      inference('split', [status(esa)], ['2'])).
% 0.99/1.18  thf('63', plain,
% 0.99/1.18      (((r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_D_3) @ (k2_relat_1 @ sk_C_1)))
% 0.99/1.18         <= (((r2_hidden @ sk_D_3 @ sk_A)))),
% 0.99/1.18      inference('sup-', [status(thm)], ['8', '20'])).
% 0.99/1.18  thf('64', plain,
% 0.99/1.18      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.99/1.18         (~ (v1_relat_1 @ X9)
% 0.99/1.18          | ~ (v4_relat_1 @ X9 @ X10)
% 0.99/1.18          | ~ (v1_funct_1 @ X9)
% 0.99/1.18          | ~ (v1_partfun1 @ X9 @ X10)
% 0.99/1.18          | ~ (m3_yellow_6 @ X9 @ X10 @ X11)
% 0.99/1.18          | (l1_waybel_0 @ X12 @ X11)
% 0.99/1.18          | ~ (r2_hidden @ X12 @ (k2_relat_1 @ X9))
% 0.99/1.18          | ~ (l1_struct_0 @ X11))),
% 0.99/1.18      inference('cnf', [status(esa)], [d15_yellow_6])).
% 0.99/1.18  thf('65', plain,
% 0.99/1.18      ((![X0 : $i, X1 : $i]:
% 0.99/1.18          (~ (l1_struct_0 @ X0)
% 0.99/1.18           | (l1_waybel_0 @ (k1_funct_1 @ sk_C_1 @ sk_D_3) @ X0)
% 0.99/1.18           | ~ (m3_yellow_6 @ sk_C_1 @ X1 @ X0)
% 0.99/1.18           | ~ (v1_partfun1 @ sk_C_1 @ X1)
% 0.99/1.18           | ~ (v1_funct_1 @ sk_C_1)
% 0.99/1.18           | ~ (v4_relat_1 @ sk_C_1 @ X1)
% 0.99/1.18           | ~ (v1_relat_1 @ sk_C_1)))
% 0.99/1.18         <= (((r2_hidden @ sk_D_3 @ sk_A)))),
% 0.99/1.18      inference('sup-', [status(thm)], ['63', '64'])).
% 0.99/1.18  thf('66', plain, ((v1_funct_1 @ sk_C_1)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('67', plain, ((v1_relat_1 @ sk_C_1)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('68', plain,
% 0.99/1.18      ((![X0 : $i, X1 : $i]:
% 0.99/1.18          (~ (l1_struct_0 @ X0)
% 0.99/1.18           | (l1_waybel_0 @ (k1_funct_1 @ sk_C_1 @ sk_D_3) @ X0)
% 0.99/1.18           | ~ (m3_yellow_6 @ sk_C_1 @ X1 @ X0)
% 0.99/1.18           | ~ (v1_partfun1 @ sk_C_1 @ X1)
% 0.99/1.18           | ~ (v4_relat_1 @ sk_C_1 @ X1)))
% 0.99/1.18         <= (((r2_hidden @ sk_D_3 @ sk_A)))),
% 0.99/1.18      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.99/1.18  thf('69', plain,
% 0.99/1.18      (((~ (v4_relat_1 @ sk_C_1 @ sk_A)
% 0.99/1.18         | ~ (v1_partfun1 @ sk_C_1 @ sk_A)
% 0.99/1.18         | (l1_waybel_0 @ (k1_funct_1 @ sk_C_1 @ sk_D_3) @ sk_B)
% 0.99/1.18         | ~ (l1_struct_0 @ sk_B)))
% 0.99/1.18         <= (((m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B)) & 
% 0.99/1.18             ((r2_hidden @ sk_D_3 @ sk_A)))),
% 0.99/1.18      inference('sup-', [status(thm)], ['62', '68'])).
% 0.99/1.18  thf('70', plain, ((v4_relat_1 @ sk_C_1 @ sk_A)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('71', plain, ((v1_partfun1 @ sk_C_1 @ sk_A)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('72', plain, ((l1_struct_0 @ sk_B)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('73', plain,
% 0.99/1.18      (((l1_waybel_0 @ (k1_funct_1 @ sk_C_1 @ sk_D_3) @ sk_B))
% 0.99/1.18         <= (((m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B)) & 
% 0.99/1.18             ((r2_hidden @ sk_D_3 @ sk_A)))),
% 0.99/1.18      inference('demod', [status(thm)], ['69', '70', '71', '72'])).
% 0.99/1.18  thf('74', plain,
% 0.99/1.18      ((~ (l1_waybel_0 @ (k1_funct_1 @ sk_C_1 @ sk_D_3) @ sk_B))
% 0.99/1.18         <= (~ ((l1_waybel_0 @ (k1_funct_1 @ sk_C_1 @ sk_D_3) @ sk_B)))),
% 0.99/1.18      inference('split', [status(esa)], ['5'])).
% 0.99/1.18  thf('75', plain,
% 0.99/1.18      (((l1_waybel_0 @ (k1_funct_1 @ sk_C_1 @ sk_D_3) @ sk_B)) | 
% 0.99/1.18       ~ ((r2_hidden @ sk_D_3 @ sk_A)) | 
% 0.99/1.18       ~ ((m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B))),
% 0.99/1.18      inference('sup-', [status(thm)], ['73', '74'])).
% 0.99/1.18  thf('76', plain,
% 0.99/1.18      (((r2_hidden @ sk_D_3 @ sk_A)) | ~ ((m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B))),
% 0.99/1.18      inference('split', [status(esa)], ['7'])).
% 0.99/1.18  thf('77', plain,
% 0.99/1.18      (((v2_struct_0 @ (k1_funct_1 @ sk_C_1 @ sk_D_3))) | 
% 0.99/1.18       ~ ((l1_waybel_0 @ (k1_funct_1 @ sk_C_1 @ sk_D_3) @ sk_B)) | 
% 0.99/1.18       ~ ((m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B)) | 
% 0.99/1.18       ~ ((v7_waybel_0 @ (k1_funct_1 @ sk_C_1 @ sk_D_3))) | 
% 0.99/1.18       ~ ((v4_orders_2 @ (k1_funct_1 @ sk_C_1 @ sk_D_3)))),
% 0.99/1.18      inference('split', [status(esa)], ['5'])).
% 0.99/1.18  thf('78', plain,
% 0.99/1.18      (![X16 : $i]:
% 0.99/1.18         (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18          | ~ (v2_struct_0 @ (k1_funct_1 @ sk_C_1 @ X16))
% 0.99/1.18          | (m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B))),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('79', plain,
% 0.99/1.18      ((![X16 : $i]:
% 0.99/1.18          (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18           | ~ (v2_struct_0 @ (k1_funct_1 @ sk_C_1 @ X16)))) | 
% 0.99/1.18       ((m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B))),
% 0.99/1.18      inference('split', [status(esa)], ['78'])).
% 0.99/1.18  thf('80', plain,
% 0.99/1.18      ((![X16 : $i]:
% 0.99/1.18          (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18           | (l1_waybel_0 @ (k1_funct_1 @ sk_C_1 @ X16) @ sk_B))) | 
% 0.99/1.18       ((m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B))),
% 0.99/1.18      inference('split', [status(esa)], ['2'])).
% 0.99/1.18  thf('81', plain,
% 0.99/1.18      (![X16 : $i]:
% 0.99/1.18         (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18          | (v7_waybel_0 @ (k1_funct_1 @ sk_C_1 @ X16))
% 0.99/1.18          | (m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B))),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('82', plain,
% 0.99/1.18      ((![X16 : $i]:
% 0.99/1.18          (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18           | (v7_waybel_0 @ (k1_funct_1 @ sk_C_1 @ X16)))) | 
% 0.99/1.18       ((m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B))),
% 0.99/1.18      inference('split', [status(esa)], ['81'])).
% 0.99/1.18  thf('83', plain, ((v1_partfun1 @ sk_C_1 @ sk_A)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('84', plain, ((v4_relat_1 @ sk_C_1 @ sk_A)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('85', plain,
% 0.99/1.18      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.99/1.18         (~ (v1_relat_1 @ X9)
% 0.99/1.18          | ~ (v4_relat_1 @ X9 @ X10)
% 0.99/1.18          | ~ (v1_funct_1 @ X9)
% 0.99/1.18          | ~ (v1_partfun1 @ X9 @ X10)
% 0.99/1.18          | (r2_hidden @ (sk_D_2 @ X9 @ X11) @ (k2_relat_1 @ X9))
% 0.99/1.18          | (m3_yellow_6 @ X9 @ X10 @ X11)
% 0.99/1.18          | ~ (l1_struct_0 @ X11))),
% 0.99/1.18      inference('cnf', [status(esa)], [d15_yellow_6])).
% 0.99/1.18  thf('86', plain,
% 0.99/1.18      (![X0 : $i]:
% 0.99/1.18         (~ (l1_struct_0 @ X0)
% 0.99/1.18          | (m3_yellow_6 @ sk_C_1 @ sk_A @ X0)
% 0.99/1.18          | (r2_hidden @ (sk_D_2 @ sk_C_1 @ X0) @ (k2_relat_1 @ sk_C_1))
% 0.99/1.18          | ~ (v1_partfun1 @ sk_C_1 @ sk_A)
% 0.99/1.18          | ~ (v1_funct_1 @ sk_C_1)
% 0.99/1.18          | ~ (v1_relat_1 @ sk_C_1))),
% 0.99/1.18      inference('sup-', [status(thm)], ['84', '85'])).
% 0.99/1.18  thf('87', plain, ((v1_partfun1 @ sk_C_1 @ sk_A)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('88', plain, ((v1_funct_1 @ sk_C_1)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('89', plain, ((v1_relat_1 @ sk_C_1)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('90', plain,
% 0.99/1.18      (![X0 : $i]:
% 0.99/1.18         (~ (l1_struct_0 @ X0)
% 0.99/1.18          | (m3_yellow_6 @ sk_C_1 @ sk_A @ X0)
% 0.99/1.18          | (r2_hidden @ (sk_D_2 @ sk_C_1 @ X0) @ (k2_relat_1 @ sk_C_1)))),
% 0.99/1.18      inference('demod', [status(thm)], ['86', '87', '88', '89'])).
% 0.99/1.18  thf('91', plain,
% 0.99/1.18      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.99/1.18         (((X3) != (k2_relat_1 @ X1))
% 0.99/1.18          | ((X4) = (k1_funct_1 @ X1 @ (sk_D_1 @ X4 @ X1)))
% 0.99/1.18          | ~ (r2_hidden @ X4 @ X3)
% 0.99/1.18          | ~ (v1_funct_1 @ X1)
% 0.99/1.18          | ~ (v1_relat_1 @ X1))),
% 0.99/1.18      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.99/1.18  thf('92', plain,
% 0.99/1.18      (![X1 : $i, X4 : $i]:
% 0.99/1.18         (~ (v1_relat_1 @ X1)
% 0.99/1.18          | ~ (v1_funct_1 @ X1)
% 0.99/1.18          | ~ (r2_hidden @ X4 @ (k2_relat_1 @ X1))
% 0.99/1.18          | ((X4) = (k1_funct_1 @ X1 @ (sk_D_1 @ X4 @ X1))))),
% 0.99/1.18      inference('simplify', [status(thm)], ['91'])).
% 0.99/1.18  thf('93', plain,
% 0.99/1.18      (![X0 : $i]:
% 0.99/1.18         ((m3_yellow_6 @ sk_C_1 @ sk_A @ X0)
% 0.99/1.18          | ~ (l1_struct_0 @ X0)
% 0.99/1.18          | ((sk_D_2 @ sk_C_1 @ X0)
% 0.99/1.18              = (k1_funct_1 @ sk_C_1 @ 
% 0.99/1.18                 (sk_D_1 @ (sk_D_2 @ sk_C_1 @ X0) @ sk_C_1)))
% 0.99/1.18          | ~ (v1_funct_1 @ sk_C_1)
% 0.99/1.18          | ~ (v1_relat_1 @ sk_C_1))),
% 0.99/1.18      inference('sup-', [status(thm)], ['90', '92'])).
% 0.99/1.18  thf('94', plain, ((v1_funct_1 @ sk_C_1)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('95', plain, ((v1_relat_1 @ sk_C_1)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('96', plain,
% 0.99/1.18      (![X0 : $i]:
% 0.99/1.18         ((m3_yellow_6 @ sk_C_1 @ sk_A @ X0)
% 0.99/1.18          | ~ (l1_struct_0 @ X0)
% 0.99/1.18          | ((sk_D_2 @ sk_C_1 @ X0)
% 0.99/1.18              = (k1_funct_1 @ sk_C_1 @ 
% 0.99/1.18                 (sk_D_1 @ (sk_D_2 @ sk_C_1 @ X0) @ sk_C_1))))),
% 0.99/1.18      inference('demod', [status(thm)], ['93', '94', '95'])).
% 0.99/1.18  thf('97', plain,
% 0.99/1.18      (![X0 : $i]:
% 0.99/1.18         (~ (l1_struct_0 @ X0)
% 0.99/1.18          | (m3_yellow_6 @ sk_C_1 @ sk_A @ X0)
% 0.99/1.18          | (r2_hidden @ (sk_D_2 @ sk_C_1 @ X0) @ (k2_relat_1 @ sk_C_1)))),
% 0.99/1.18      inference('demod', [status(thm)], ['86', '87', '88', '89'])).
% 0.99/1.18  thf('98', plain,
% 0.99/1.18      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.99/1.18         (((X3) != (k2_relat_1 @ X1))
% 0.99/1.18          | (r2_hidden @ (sk_D_1 @ X4 @ X1) @ (k1_relat_1 @ X1))
% 0.99/1.18          | ~ (r2_hidden @ X4 @ X3)
% 0.99/1.18          | ~ (v1_funct_1 @ X1)
% 0.99/1.18          | ~ (v1_relat_1 @ X1))),
% 0.99/1.18      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.99/1.18  thf('99', plain,
% 0.99/1.18      (![X1 : $i, X4 : $i]:
% 0.99/1.18         (~ (v1_relat_1 @ X1)
% 0.99/1.18          | ~ (v1_funct_1 @ X1)
% 0.99/1.18          | ~ (r2_hidden @ X4 @ (k2_relat_1 @ X1))
% 0.99/1.18          | (r2_hidden @ (sk_D_1 @ X4 @ X1) @ (k1_relat_1 @ X1)))),
% 0.99/1.18      inference('simplify', [status(thm)], ['98'])).
% 0.99/1.18  thf('100', plain,
% 0.99/1.18      (![X0 : $i]:
% 0.99/1.18         ((m3_yellow_6 @ sk_C_1 @ sk_A @ X0)
% 0.99/1.18          | ~ (l1_struct_0 @ X0)
% 0.99/1.18          | (r2_hidden @ (sk_D_1 @ (sk_D_2 @ sk_C_1 @ X0) @ sk_C_1) @ 
% 0.99/1.18             (k1_relat_1 @ sk_C_1))
% 0.99/1.18          | ~ (v1_funct_1 @ sk_C_1)
% 0.99/1.18          | ~ (v1_relat_1 @ sk_C_1))),
% 0.99/1.18      inference('sup-', [status(thm)], ['97', '99'])).
% 0.99/1.18  thf('101', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 0.99/1.18      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.99/1.18  thf('102', plain, ((v1_funct_1 @ sk_C_1)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('103', plain, ((v1_relat_1 @ sk_C_1)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('104', plain,
% 0.99/1.18      (![X0 : $i]:
% 0.99/1.18         ((m3_yellow_6 @ sk_C_1 @ sk_A @ X0)
% 0.99/1.18          | ~ (l1_struct_0 @ X0)
% 0.99/1.18          | (r2_hidden @ (sk_D_1 @ (sk_D_2 @ sk_C_1 @ X0) @ sk_C_1) @ sk_A))),
% 0.99/1.18      inference('demod', [status(thm)], ['100', '101', '102', '103'])).
% 0.99/1.18  thf('105', plain,
% 0.99/1.18      ((![X16 : $i]:
% 0.99/1.18          (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18           | (v7_waybel_0 @ (k1_funct_1 @ sk_C_1 @ X16))))
% 0.99/1.18         <= ((![X16 : $i]:
% 0.99/1.18                (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18                 | (v7_waybel_0 @ (k1_funct_1 @ sk_C_1 @ X16)))))),
% 0.99/1.18      inference('split', [status(esa)], ['81'])).
% 0.99/1.18  thf('106', plain,
% 0.99/1.18      ((![X0 : $i]:
% 0.99/1.18          (~ (l1_struct_0 @ X0)
% 0.99/1.18           | (m3_yellow_6 @ sk_C_1 @ sk_A @ X0)
% 0.99/1.18           | (v7_waybel_0 @ 
% 0.99/1.18              (k1_funct_1 @ sk_C_1 @ (sk_D_1 @ (sk_D_2 @ sk_C_1 @ X0) @ sk_C_1)))))
% 0.99/1.18         <= ((![X16 : $i]:
% 0.99/1.18                (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18                 | (v7_waybel_0 @ (k1_funct_1 @ sk_C_1 @ X16)))))),
% 0.99/1.18      inference('sup-', [status(thm)], ['104', '105'])).
% 0.99/1.18  thf('107', plain,
% 0.99/1.18      ((![X0 : $i]:
% 0.99/1.18          ((v7_waybel_0 @ (sk_D_2 @ sk_C_1 @ X0))
% 0.99/1.18           | ~ (l1_struct_0 @ X0)
% 0.99/1.18           | (m3_yellow_6 @ sk_C_1 @ sk_A @ X0)
% 0.99/1.18           | (m3_yellow_6 @ sk_C_1 @ sk_A @ X0)
% 0.99/1.18           | ~ (l1_struct_0 @ X0)))
% 0.99/1.18         <= ((![X16 : $i]:
% 0.99/1.18                (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18                 | (v7_waybel_0 @ (k1_funct_1 @ sk_C_1 @ X16)))))),
% 0.99/1.18      inference('sup+', [status(thm)], ['96', '106'])).
% 0.99/1.18  thf('108', plain,
% 0.99/1.18      ((![X0 : $i]:
% 0.99/1.18          ((m3_yellow_6 @ sk_C_1 @ sk_A @ X0)
% 0.99/1.18           | ~ (l1_struct_0 @ X0)
% 0.99/1.18           | (v7_waybel_0 @ (sk_D_2 @ sk_C_1 @ X0))))
% 0.99/1.18         <= ((![X16 : $i]:
% 0.99/1.18                (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18                 | (v7_waybel_0 @ (k1_funct_1 @ sk_C_1 @ X16)))))),
% 0.99/1.18      inference('simplify', [status(thm)], ['107'])).
% 0.99/1.18  thf('109', plain,
% 0.99/1.18      ((~ (m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B))
% 0.99/1.18         <= (~ ((m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.99/1.18      inference('split', [status(esa)], ['5'])).
% 0.99/1.18  thf('110', plain,
% 0.99/1.18      ((((v7_waybel_0 @ (sk_D_2 @ sk_C_1 @ sk_B)) | ~ (l1_struct_0 @ sk_B)))
% 0.99/1.18         <= (~ ((m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B)) & 
% 0.99/1.18             (![X16 : $i]:
% 0.99/1.18                (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18                 | (v7_waybel_0 @ (k1_funct_1 @ sk_C_1 @ X16)))))),
% 0.99/1.18      inference('sup-', [status(thm)], ['108', '109'])).
% 0.99/1.18  thf('111', plain, ((l1_struct_0 @ sk_B)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('112', plain,
% 0.99/1.18      (((v7_waybel_0 @ (sk_D_2 @ sk_C_1 @ sk_B)))
% 0.99/1.18         <= (~ ((m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B)) & 
% 0.99/1.18             (![X16 : $i]:
% 0.99/1.18                (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18                 | (v7_waybel_0 @ (k1_funct_1 @ sk_C_1 @ X16)))))),
% 0.99/1.18      inference('demod', [status(thm)], ['110', '111'])).
% 0.99/1.18  thf('113', plain,
% 0.99/1.18      (![X0 : $i]:
% 0.99/1.18         ((m3_yellow_6 @ sk_C_1 @ sk_A @ X0)
% 0.99/1.18          | ~ (l1_struct_0 @ X0)
% 0.99/1.18          | ((sk_D_2 @ sk_C_1 @ X0)
% 0.99/1.18              = (k1_funct_1 @ sk_C_1 @ 
% 0.99/1.18                 (sk_D_1 @ (sk_D_2 @ sk_C_1 @ X0) @ sk_C_1))))),
% 0.99/1.18      inference('demod', [status(thm)], ['93', '94', '95'])).
% 0.99/1.18  thf('114', plain,
% 0.99/1.18      (![X0 : $i]:
% 0.99/1.18         ((m3_yellow_6 @ sk_C_1 @ sk_A @ X0)
% 0.99/1.18          | ~ (l1_struct_0 @ X0)
% 0.99/1.18          | (r2_hidden @ (sk_D_1 @ (sk_D_2 @ sk_C_1 @ X0) @ sk_C_1) @ sk_A))),
% 0.99/1.18      inference('demod', [status(thm)], ['100', '101', '102', '103'])).
% 0.99/1.18  thf('115', plain,
% 0.99/1.18      ((![X16 : $i]:
% 0.99/1.18          (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18           | (v4_orders_2 @ (k1_funct_1 @ sk_C_1 @ X16))))
% 0.99/1.18         <= ((![X16 : $i]:
% 0.99/1.18                (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18                 | (v4_orders_2 @ (k1_funct_1 @ sk_C_1 @ X16)))))),
% 0.99/1.18      inference('split', [status(esa)], ['0'])).
% 0.99/1.18  thf('116', plain,
% 0.99/1.18      ((![X0 : $i]:
% 0.99/1.18          (~ (l1_struct_0 @ X0)
% 0.99/1.18           | (m3_yellow_6 @ sk_C_1 @ sk_A @ X0)
% 0.99/1.18           | (v4_orders_2 @ 
% 0.99/1.18              (k1_funct_1 @ sk_C_1 @ (sk_D_1 @ (sk_D_2 @ sk_C_1 @ X0) @ sk_C_1)))))
% 0.99/1.18         <= ((![X16 : $i]:
% 0.99/1.18                (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18                 | (v4_orders_2 @ (k1_funct_1 @ sk_C_1 @ X16)))))),
% 0.99/1.18      inference('sup-', [status(thm)], ['114', '115'])).
% 0.99/1.18  thf('117', plain,
% 0.99/1.18      ((![X0 : $i]:
% 0.99/1.18          ((v4_orders_2 @ (sk_D_2 @ sk_C_1 @ X0))
% 0.99/1.18           | ~ (l1_struct_0 @ X0)
% 0.99/1.18           | (m3_yellow_6 @ sk_C_1 @ sk_A @ X0)
% 0.99/1.18           | (m3_yellow_6 @ sk_C_1 @ sk_A @ X0)
% 0.99/1.18           | ~ (l1_struct_0 @ X0)))
% 0.99/1.18         <= ((![X16 : $i]:
% 0.99/1.18                (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18                 | (v4_orders_2 @ (k1_funct_1 @ sk_C_1 @ X16)))))),
% 0.99/1.18      inference('sup+', [status(thm)], ['113', '116'])).
% 0.99/1.18  thf('118', plain,
% 0.99/1.18      ((![X0 : $i]:
% 0.99/1.18          ((m3_yellow_6 @ sk_C_1 @ sk_A @ X0)
% 0.99/1.18           | ~ (l1_struct_0 @ X0)
% 0.99/1.18           | (v4_orders_2 @ (sk_D_2 @ sk_C_1 @ X0))))
% 0.99/1.18         <= ((![X16 : $i]:
% 0.99/1.18                (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18                 | (v4_orders_2 @ (k1_funct_1 @ sk_C_1 @ X16)))))),
% 0.99/1.18      inference('simplify', [status(thm)], ['117'])).
% 0.99/1.18  thf('119', plain,
% 0.99/1.18      ((~ (m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B))
% 0.99/1.18         <= (~ ((m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.99/1.18      inference('split', [status(esa)], ['5'])).
% 0.99/1.18  thf('120', plain,
% 0.99/1.18      ((((v4_orders_2 @ (sk_D_2 @ sk_C_1 @ sk_B)) | ~ (l1_struct_0 @ sk_B)))
% 0.99/1.18         <= (~ ((m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B)) & 
% 0.99/1.18             (![X16 : $i]:
% 0.99/1.18                (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18                 | (v4_orders_2 @ (k1_funct_1 @ sk_C_1 @ X16)))))),
% 0.99/1.18      inference('sup-', [status(thm)], ['118', '119'])).
% 0.99/1.18  thf('121', plain, ((l1_struct_0 @ sk_B)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('122', plain,
% 0.99/1.18      (((v4_orders_2 @ (sk_D_2 @ sk_C_1 @ sk_B)))
% 0.99/1.18         <= (~ ((m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B)) & 
% 0.99/1.18             (![X16 : $i]:
% 0.99/1.18                (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18                 | (v4_orders_2 @ (k1_funct_1 @ sk_C_1 @ X16)))))),
% 0.99/1.18      inference('demod', [status(thm)], ['120', '121'])).
% 0.99/1.18  thf('123', plain,
% 0.99/1.18      (![X0 : $i]:
% 0.99/1.18         ((m3_yellow_6 @ sk_C_1 @ sk_A @ X0)
% 0.99/1.18          | ~ (l1_struct_0 @ X0)
% 0.99/1.18          | ((sk_D_2 @ sk_C_1 @ X0)
% 0.99/1.18              = (k1_funct_1 @ sk_C_1 @ 
% 0.99/1.18                 (sk_D_1 @ (sk_D_2 @ sk_C_1 @ X0) @ sk_C_1))))),
% 0.99/1.18      inference('demod', [status(thm)], ['93', '94', '95'])).
% 0.99/1.18  thf('124', plain,
% 0.99/1.18      (![X0 : $i]:
% 0.99/1.18         ((m3_yellow_6 @ sk_C_1 @ sk_A @ X0)
% 0.99/1.18          | ~ (l1_struct_0 @ X0)
% 0.99/1.18          | (r2_hidden @ (sk_D_1 @ (sk_D_2 @ sk_C_1 @ X0) @ sk_C_1) @ sk_A))),
% 0.99/1.18      inference('demod', [status(thm)], ['100', '101', '102', '103'])).
% 0.99/1.18  thf('125', plain,
% 0.99/1.18      ((![X16 : $i]:
% 0.99/1.18          (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18           | (l1_waybel_0 @ (k1_funct_1 @ sk_C_1 @ X16) @ sk_B)))
% 0.99/1.18         <= ((![X16 : $i]:
% 0.99/1.18                (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18                 | (l1_waybel_0 @ (k1_funct_1 @ sk_C_1 @ X16) @ sk_B))))),
% 0.99/1.18      inference('split', [status(esa)], ['2'])).
% 0.99/1.18  thf('126', plain,
% 0.99/1.18      ((![X0 : $i]:
% 0.99/1.18          (~ (l1_struct_0 @ X0)
% 0.99/1.18           | (m3_yellow_6 @ sk_C_1 @ sk_A @ X0)
% 0.99/1.18           | (l1_waybel_0 @ 
% 0.99/1.18              (k1_funct_1 @ sk_C_1 @ (sk_D_1 @ (sk_D_2 @ sk_C_1 @ X0) @ sk_C_1)) @ 
% 0.99/1.18              sk_B)))
% 0.99/1.18         <= ((![X16 : $i]:
% 0.99/1.18                (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18                 | (l1_waybel_0 @ (k1_funct_1 @ sk_C_1 @ X16) @ sk_B))))),
% 0.99/1.18      inference('sup-', [status(thm)], ['124', '125'])).
% 0.99/1.18  thf('127', plain,
% 0.99/1.18      ((![X0 : $i]:
% 0.99/1.18          ((l1_waybel_0 @ (sk_D_2 @ sk_C_1 @ X0) @ sk_B)
% 0.99/1.18           | ~ (l1_struct_0 @ X0)
% 0.99/1.18           | (m3_yellow_6 @ sk_C_1 @ sk_A @ X0)
% 0.99/1.18           | (m3_yellow_6 @ sk_C_1 @ sk_A @ X0)
% 0.99/1.18           | ~ (l1_struct_0 @ X0)))
% 0.99/1.18         <= ((![X16 : $i]:
% 0.99/1.18                (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18                 | (l1_waybel_0 @ (k1_funct_1 @ sk_C_1 @ X16) @ sk_B))))),
% 0.99/1.18      inference('sup+', [status(thm)], ['123', '126'])).
% 0.99/1.18  thf('128', plain,
% 0.99/1.18      ((![X0 : $i]:
% 0.99/1.18          ((m3_yellow_6 @ sk_C_1 @ sk_A @ X0)
% 0.99/1.18           | ~ (l1_struct_0 @ X0)
% 0.99/1.18           | (l1_waybel_0 @ (sk_D_2 @ sk_C_1 @ X0) @ sk_B)))
% 0.99/1.18         <= ((![X16 : $i]:
% 0.99/1.18                (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18                 | (l1_waybel_0 @ (k1_funct_1 @ sk_C_1 @ X16) @ sk_B))))),
% 0.99/1.18      inference('simplify', [status(thm)], ['127'])).
% 0.99/1.18  thf('129', plain,
% 0.99/1.18      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.99/1.18         (~ (v1_relat_1 @ X9)
% 0.99/1.18          | ~ (v4_relat_1 @ X9 @ X10)
% 0.99/1.18          | ~ (v1_funct_1 @ X9)
% 0.99/1.18          | ~ (v1_partfun1 @ X9 @ X10)
% 0.99/1.18          | ~ (l1_waybel_0 @ (sk_D_2 @ X9 @ X11) @ X11)
% 0.99/1.18          | ~ (v7_waybel_0 @ (sk_D_2 @ X9 @ X11))
% 0.99/1.18          | ~ (v4_orders_2 @ (sk_D_2 @ X9 @ X11))
% 0.99/1.18          | (v2_struct_0 @ (sk_D_2 @ X9 @ X11))
% 0.99/1.18          | (m3_yellow_6 @ X9 @ X10 @ X11)
% 0.99/1.18          | ~ (l1_struct_0 @ X11))),
% 0.99/1.18      inference('cnf', [status(esa)], [d15_yellow_6])).
% 0.99/1.18  thf('130', plain,
% 0.99/1.18      ((![X0 : $i]:
% 0.99/1.18          (~ (l1_struct_0 @ sk_B)
% 0.99/1.18           | (m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B)
% 0.99/1.18           | ~ (l1_struct_0 @ sk_B)
% 0.99/1.18           | (m3_yellow_6 @ sk_C_1 @ X0 @ sk_B)
% 0.99/1.18           | (v2_struct_0 @ (sk_D_2 @ sk_C_1 @ sk_B))
% 0.99/1.18           | ~ (v4_orders_2 @ (sk_D_2 @ sk_C_1 @ sk_B))
% 0.99/1.18           | ~ (v7_waybel_0 @ (sk_D_2 @ sk_C_1 @ sk_B))
% 0.99/1.18           | ~ (v1_partfun1 @ sk_C_1 @ X0)
% 0.99/1.18           | ~ (v1_funct_1 @ sk_C_1)
% 0.99/1.18           | ~ (v4_relat_1 @ sk_C_1 @ X0)
% 0.99/1.18           | ~ (v1_relat_1 @ sk_C_1)))
% 0.99/1.18         <= ((![X16 : $i]:
% 0.99/1.18                (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18                 | (l1_waybel_0 @ (k1_funct_1 @ sk_C_1 @ X16) @ sk_B))))),
% 0.99/1.18      inference('sup-', [status(thm)], ['128', '129'])).
% 0.99/1.18  thf('131', plain, ((l1_struct_0 @ sk_B)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('132', plain, ((l1_struct_0 @ sk_B)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('133', plain, ((v1_funct_1 @ sk_C_1)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('134', plain, ((v1_relat_1 @ sk_C_1)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('135', plain,
% 0.99/1.18      ((![X0 : $i]:
% 0.99/1.18          ((m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B)
% 0.99/1.18           | (m3_yellow_6 @ sk_C_1 @ X0 @ sk_B)
% 0.99/1.18           | (v2_struct_0 @ (sk_D_2 @ sk_C_1 @ sk_B))
% 0.99/1.18           | ~ (v4_orders_2 @ (sk_D_2 @ sk_C_1 @ sk_B))
% 0.99/1.18           | ~ (v7_waybel_0 @ (sk_D_2 @ sk_C_1 @ sk_B))
% 0.99/1.18           | ~ (v1_partfun1 @ sk_C_1 @ X0)
% 0.99/1.18           | ~ (v4_relat_1 @ sk_C_1 @ X0)))
% 0.99/1.18         <= ((![X16 : $i]:
% 0.99/1.18                (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18                 | (l1_waybel_0 @ (k1_funct_1 @ sk_C_1 @ X16) @ sk_B))))),
% 0.99/1.18      inference('demod', [status(thm)], ['130', '131', '132', '133', '134'])).
% 0.99/1.18  thf('136', plain,
% 0.99/1.18      ((![X0 : $i]:
% 0.99/1.18          (~ (v4_relat_1 @ sk_C_1 @ X0)
% 0.99/1.18           | ~ (v1_partfun1 @ sk_C_1 @ X0)
% 0.99/1.18           | ~ (v7_waybel_0 @ (sk_D_2 @ sk_C_1 @ sk_B))
% 0.99/1.18           | (v2_struct_0 @ (sk_D_2 @ sk_C_1 @ sk_B))
% 0.99/1.18           | (m3_yellow_6 @ sk_C_1 @ X0 @ sk_B)
% 0.99/1.18           | (m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B)))
% 0.99/1.18         <= (~ ((m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B)) & 
% 0.99/1.18             (![X16 : $i]:
% 0.99/1.18                (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18                 | (l1_waybel_0 @ (k1_funct_1 @ sk_C_1 @ X16) @ sk_B))) & 
% 0.99/1.18             (![X16 : $i]:
% 0.99/1.18                (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18                 | (v4_orders_2 @ (k1_funct_1 @ sk_C_1 @ X16)))))),
% 0.99/1.18      inference('sup-', [status(thm)], ['122', '135'])).
% 0.99/1.18  thf('137', plain,
% 0.99/1.18      ((![X0 : $i]:
% 0.99/1.18          ((m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B)
% 0.99/1.18           | (m3_yellow_6 @ sk_C_1 @ X0 @ sk_B)
% 0.99/1.18           | (v2_struct_0 @ (sk_D_2 @ sk_C_1 @ sk_B))
% 0.99/1.18           | ~ (v1_partfun1 @ sk_C_1 @ X0)
% 0.99/1.18           | ~ (v4_relat_1 @ sk_C_1 @ X0)))
% 0.99/1.18         <= (~ ((m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B)) & 
% 0.99/1.18             (![X16 : $i]:
% 0.99/1.18                (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18                 | (l1_waybel_0 @ (k1_funct_1 @ sk_C_1 @ X16) @ sk_B))) & 
% 0.99/1.18             (![X16 : $i]:
% 0.99/1.18                (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18                 | (v7_waybel_0 @ (k1_funct_1 @ sk_C_1 @ X16)))) & 
% 0.99/1.18             (![X16 : $i]:
% 0.99/1.18                (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18                 | (v4_orders_2 @ (k1_funct_1 @ sk_C_1 @ X16)))))),
% 0.99/1.18      inference('sup-', [status(thm)], ['112', '136'])).
% 0.99/1.18  thf('138', plain,
% 0.99/1.18      (((~ (v4_relat_1 @ sk_C_1 @ sk_A)
% 0.99/1.18         | (v2_struct_0 @ (sk_D_2 @ sk_C_1 @ sk_B))
% 0.99/1.18         | (m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B)
% 0.99/1.18         | (m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B)))
% 0.99/1.18         <= (~ ((m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B)) & 
% 0.99/1.18             (![X16 : $i]:
% 0.99/1.18                (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18                 | (l1_waybel_0 @ (k1_funct_1 @ sk_C_1 @ X16) @ sk_B))) & 
% 0.99/1.18             (![X16 : $i]:
% 0.99/1.18                (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18                 | (v7_waybel_0 @ (k1_funct_1 @ sk_C_1 @ X16)))) & 
% 0.99/1.18             (![X16 : $i]:
% 0.99/1.18                (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18                 | (v4_orders_2 @ (k1_funct_1 @ sk_C_1 @ X16)))))),
% 0.99/1.18      inference('sup-', [status(thm)], ['83', '137'])).
% 0.99/1.18  thf('139', plain, ((v4_relat_1 @ sk_C_1 @ sk_A)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('140', plain,
% 0.99/1.18      ((((v2_struct_0 @ (sk_D_2 @ sk_C_1 @ sk_B))
% 0.99/1.18         | (m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B)
% 0.99/1.18         | (m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B)))
% 0.99/1.18         <= (~ ((m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B)) & 
% 0.99/1.18             (![X16 : $i]:
% 0.99/1.18                (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18                 | (l1_waybel_0 @ (k1_funct_1 @ sk_C_1 @ X16) @ sk_B))) & 
% 0.99/1.18             (![X16 : $i]:
% 0.99/1.18                (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18                 | (v7_waybel_0 @ (k1_funct_1 @ sk_C_1 @ X16)))) & 
% 0.99/1.18             (![X16 : $i]:
% 0.99/1.18                (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18                 | (v4_orders_2 @ (k1_funct_1 @ sk_C_1 @ X16)))))),
% 0.99/1.18      inference('demod', [status(thm)], ['138', '139'])).
% 0.99/1.18  thf('141', plain,
% 0.99/1.18      ((((m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B)
% 0.99/1.18         | (v2_struct_0 @ (sk_D_2 @ sk_C_1 @ sk_B))))
% 0.99/1.18         <= (~ ((m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B)) & 
% 0.99/1.18             (![X16 : $i]:
% 0.99/1.18                (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18                 | (l1_waybel_0 @ (k1_funct_1 @ sk_C_1 @ X16) @ sk_B))) & 
% 0.99/1.18             (![X16 : $i]:
% 0.99/1.18                (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18                 | (v7_waybel_0 @ (k1_funct_1 @ sk_C_1 @ X16)))) & 
% 0.99/1.18             (![X16 : $i]:
% 0.99/1.18                (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18                 | (v4_orders_2 @ (k1_funct_1 @ sk_C_1 @ X16)))))),
% 0.99/1.18      inference('simplify', [status(thm)], ['140'])).
% 0.99/1.18  thf('142', plain,
% 0.99/1.18      ((~ (m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B))
% 0.99/1.18         <= (~ ((m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.99/1.18      inference('split', [status(esa)], ['5'])).
% 0.99/1.18  thf('143', plain,
% 0.99/1.18      (((v2_struct_0 @ (sk_D_2 @ sk_C_1 @ sk_B)))
% 0.99/1.18         <= (~ ((m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B)) & 
% 0.99/1.18             (![X16 : $i]:
% 0.99/1.18                (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18                 | (l1_waybel_0 @ (k1_funct_1 @ sk_C_1 @ X16) @ sk_B))) & 
% 0.99/1.18             (![X16 : $i]:
% 0.99/1.18                (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18                 | (v7_waybel_0 @ (k1_funct_1 @ sk_C_1 @ X16)))) & 
% 0.99/1.18             (![X16 : $i]:
% 0.99/1.18                (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18                 | (v4_orders_2 @ (k1_funct_1 @ sk_C_1 @ X16)))))),
% 0.99/1.18      inference('clc', [status(thm)], ['141', '142'])).
% 0.99/1.18  thf('144', plain,
% 0.99/1.18      (![X0 : $i]:
% 0.99/1.18         ((m3_yellow_6 @ sk_C_1 @ sk_A @ X0)
% 0.99/1.18          | ~ (l1_struct_0 @ X0)
% 0.99/1.18          | (r2_hidden @ (sk_D_1 @ (sk_D_2 @ sk_C_1 @ X0) @ sk_C_1) @ sk_A))),
% 0.99/1.18      inference('demod', [status(thm)], ['100', '101', '102', '103'])).
% 0.99/1.18  thf('145', plain,
% 0.99/1.18      (![X0 : $i]:
% 0.99/1.18         ((m3_yellow_6 @ sk_C_1 @ sk_A @ X0)
% 0.99/1.18          | ~ (l1_struct_0 @ X0)
% 0.99/1.18          | ((sk_D_2 @ sk_C_1 @ X0)
% 0.99/1.18              = (k1_funct_1 @ sk_C_1 @ 
% 0.99/1.18                 (sk_D_1 @ (sk_D_2 @ sk_C_1 @ X0) @ sk_C_1))))),
% 0.99/1.18      inference('demod', [status(thm)], ['93', '94', '95'])).
% 0.99/1.18  thf('146', plain,
% 0.99/1.18      ((![X16 : $i]:
% 0.99/1.18          (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18           | ~ (v2_struct_0 @ (k1_funct_1 @ sk_C_1 @ X16))))
% 0.99/1.18         <= ((![X16 : $i]:
% 0.99/1.18                (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18                 | ~ (v2_struct_0 @ (k1_funct_1 @ sk_C_1 @ X16)))))),
% 0.99/1.18      inference('split', [status(esa)], ['78'])).
% 0.99/1.18  thf('147', plain,
% 0.99/1.18      ((![X0 : $i]:
% 0.99/1.18          (~ (v2_struct_0 @ (sk_D_2 @ sk_C_1 @ X0))
% 0.99/1.18           | ~ (l1_struct_0 @ X0)
% 0.99/1.18           | (m3_yellow_6 @ sk_C_1 @ sk_A @ X0)
% 0.99/1.18           | ~ (r2_hidden @ (sk_D_1 @ (sk_D_2 @ sk_C_1 @ X0) @ sk_C_1) @ sk_A)))
% 0.99/1.18         <= ((![X16 : $i]:
% 0.99/1.18                (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18                 | ~ (v2_struct_0 @ (k1_funct_1 @ sk_C_1 @ X16)))))),
% 0.99/1.18      inference('sup-', [status(thm)], ['145', '146'])).
% 0.99/1.18  thf('148', plain,
% 0.99/1.18      ((![X0 : $i]:
% 0.99/1.18          (~ (l1_struct_0 @ X0)
% 0.99/1.18           | (m3_yellow_6 @ sk_C_1 @ sk_A @ X0)
% 0.99/1.18           | (m3_yellow_6 @ sk_C_1 @ sk_A @ X0)
% 0.99/1.18           | ~ (l1_struct_0 @ X0)
% 0.99/1.18           | ~ (v2_struct_0 @ (sk_D_2 @ sk_C_1 @ X0))))
% 0.99/1.18         <= ((![X16 : $i]:
% 0.99/1.18                (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18                 | ~ (v2_struct_0 @ (k1_funct_1 @ sk_C_1 @ X16)))))),
% 0.99/1.18      inference('sup-', [status(thm)], ['144', '147'])).
% 0.99/1.18  thf('149', plain,
% 0.99/1.18      ((![X0 : $i]:
% 0.99/1.18          (~ (v2_struct_0 @ (sk_D_2 @ sk_C_1 @ X0))
% 0.99/1.18           | (m3_yellow_6 @ sk_C_1 @ sk_A @ X0)
% 0.99/1.18           | ~ (l1_struct_0 @ X0)))
% 0.99/1.18         <= ((![X16 : $i]:
% 0.99/1.18                (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18                 | ~ (v2_struct_0 @ (k1_funct_1 @ sk_C_1 @ X16)))))),
% 0.99/1.18      inference('simplify', [status(thm)], ['148'])).
% 0.99/1.18  thf('150', plain,
% 0.99/1.18      (((~ (l1_struct_0 @ sk_B) | (m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B)))
% 0.99/1.18         <= (~ ((m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B)) & 
% 0.99/1.18             (![X16 : $i]:
% 0.99/1.18                (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18                 | (l1_waybel_0 @ (k1_funct_1 @ sk_C_1 @ X16) @ sk_B))) & 
% 0.99/1.18             (![X16 : $i]:
% 0.99/1.18                (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18                 | (v7_waybel_0 @ (k1_funct_1 @ sk_C_1 @ X16)))) & 
% 0.99/1.18             (![X16 : $i]:
% 0.99/1.18                (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18                 | (v4_orders_2 @ (k1_funct_1 @ sk_C_1 @ X16)))) & 
% 0.99/1.18             (![X16 : $i]:
% 0.99/1.18                (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18                 | ~ (v2_struct_0 @ (k1_funct_1 @ sk_C_1 @ X16)))))),
% 0.99/1.18      inference('sup-', [status(thm)], ['143', '149'])).
% 0.99/1.18  thf('151', plain, ((l1_struct_0 @ sk_B)),
% 0.99/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.18  thf('152', plain,
% 0.99/1.18      (((m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B))
% 0.99/1.18         <= (~ ((m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B)) & 
% 0.99/1.18             (![X16 : $i]:
% 0.99/1.18                (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18                 | (l1_waybel_0 @ (k1_funct_1 @ sk_C_1 @ X16) @ sk_B))) & 
% 0.99/1.18             (![X16 : $i]:
% 0.99/1.18                (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18                 | (v7_waybel_0 @ (k1_funct_1 @ sk_C_1 @ X16)))) & 
% 0.99/1.18             (![X16 : $i]:
% 0.99/1.18                (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18                 | (v4_orders_2 @ (k1_funct_1 @ sk_C_1 @ X16)))) & 
% 0.99/1.18             (![X16 : $i]:
% 0.99/1.18                (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18                 | ~ (v2_struct_0 @ (k1_funct_1 @ sk_C_1 @ X16)))))),
% 0.99/1.18      inference('demod', [status(thm)], ['150', '151'])).
% 0.99/1.18  thf('153', plain,
% 0.99/1.18      ((~ (m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B))
% 0.99/1.18         <= (~ ((m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.99/1.18      inference('split', [status(esa)], ['5'])).
% 0.99/1.18  thf('154', plain,
% 0.99/1.18      (~
% 0.99/1.18       (![X16 : $i]:
% 0.99/1.18          (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18           | (l1_waybel_0 @ (k1_funct_1 @ sk_C_1 @ X16) @ sk_B))) | 
% 0.99/1.18       ~
% 0.99/1.18       (![X16 : $i]:
% 0.99/1.18          (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18           | (v7_waybel_0 @ (k1_funct_1 @ sk_C_1 @ X16)))) | 
% 0.99/1.18       ~
% 0.99/1.18       (![X16 : $i]:
% 0.99/1.18          (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18           | (v4_orders_2 @ (k1_funct_1 @ sk_C_1 @ X16)))) | 
% 0.99/1.18       ~
% 0.99/1.18       (![X16 : $i]:
% 0.99/1.18          (~ (r2_hidden @ X16 @ sk_A)
% 0.99/1.18           | ~ (v2_struct_0 @ (k1_funct_1 @ sk_C_1 @ X16)))) | 
% 0.99/1.18       ((m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B))),
% 0.99/1.18      inference('sup-', [status(thm)], ['152', '153'])).
% 0.99/1.18  thf('155', plain, ($false),
% 0.99/1.18      inference('sat_resolution*', [status(thm)],
% 0.99/1.18                ['1', '33', '47', '61', '75', '76', '77', '79', '80', '82', 
% 0.99/1.18                 '154'])).
% 0.99/1.18  
% 0.99/1.18  % SZS output end Refutation
% 0.99/1.18  
% 1.02/1.19  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
