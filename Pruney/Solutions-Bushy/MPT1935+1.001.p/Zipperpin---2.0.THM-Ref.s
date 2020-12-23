%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1935+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Dh2C4asQXB

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:34 EST 2020

% Result     : Theorem 1.24s
% Output     : Refutation 1.24s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 639 expanded)
%              Number of leaves         :   24 ( 188 expanded)
%              Depth                    :   21
%              Number of atoms          : 2169 (13945 expanded)
%              Number of equality atoms :   18 (  88 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(m3_yellow_6_type,type,(
    m3_yellow_6: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_partfun1 @ X5 @ X4 )
      | ( ( k1_relat_1 @ X5 )
        = X4 )
      | ~ ( v4_relat_1 @ X5 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
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
    ! [X7: $i,X9: $i,X11: $i,X12: $i] :
      ( ( X9
       != ( k2_relat_1 @ X7 ) )
      | ( r2_hidden @ X11 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X7 ) )
      | ( X11
       != ( k1_funct_1 @ X7 @ X12 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('16',plain,(
    ! [X7: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X7 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X7 @ X12 ) @ ( k2_relat_1 @ X7 ) ) ) ),
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
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v4_relat_1 @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_partfun1 @ X0 @ X1 )
      | ~ ( m3_yellow_6 @ X0 @ X1 @ X2 )
      | ~ ( v2_struct_0 @ X3 )
      | ~ ( r2_hidden @ X3 @ ( k2_relat_1 @ X0 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
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
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v4_relat_1 @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_partfun1 @ X0 @ X1 )
      | ~ ( m3_yellow_6 @ X0 @ X1 @ X2 )
      | ( v7_waybel_0 @ X3 )
      | ~ ( r2_hidden @ X3 @ ( k2_relat_1 @ X0 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
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
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v4_relat_1 @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_partfun1 @ X0 @ X1 )
      | ~ ( m3_yellow_6 @ X0 @ X1 @ X2 )
      | ( v4_orders_2 @ X3 )
      | ~ ( r2_hidden @ X3 @ ( k2_relat_1 @ X0 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
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
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v4_relat_1 @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_partfun1 @ X0 @ X1 )
      | ~ ( m3_yellow_6 @ X0 @ X1 @ X2 )
      | ( l1_waybel_0 @ X3 @ X2 )
      | ~ ( r2_hidden @ X3 @ ( k2_relat_1 @ X0 ) )
      | ~ ( l1_struct_0 @ X2 ) ) ),
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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v4_relat_1 @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_partfun1 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_D @ X0 @ X2 ) @ ( k2_relat_1 @ X0 ) )
      | ( m3_yellow_6 @ X0 @ X1 @ X2 )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d15_yellow_6])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( m3_yellow_6 @ sk_C_1 @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_D @ sk_C_1 @ X0 ) @ ( k2_relat_1 @ sk_C_1 ) )
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
      | ( r2_hidden @ ( sk_D @ sk_C_1 @ X0 ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['86','87','88','89'])).

thf('91',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ( X9
       != ( k2_relat_1 @ X7 ) )
      | ( X10
        = ( k1_funct_1 @ X7 @ ( sk_D_2 @ X10 @ X7 ) ) )
      | ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('92',plain,(
    ! [X7: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k2_relat_1 @ X7 ) )
      | ( X10
        = ( k1_funct_1 @ X7 @ ( sk_D_2 @ X10 @ X7 ) ) ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( m3_yellow_6 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( sk_D @ sk_C_1 @ X0 )
        = ( k1_funct_1 @ sk_C_1 @ ( sk_D_2 @ ( sk_D @ sk_C_1 @ X0 ) @ sk_C_1 ) ) )
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
      | ( ( sk_D @ sk_C_1 @ X0 )
        = ( k1_funct_1 @ sk_C_1 @ ( sk_D_2 @ ( sk_D @ sk_C_1 @ X0 ) @ sk_C_1 ) ) ) ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( m3_yellow_6 @ sk_C_1 @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_D @ sk_C_1 @ X0 ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['86','87','88','89'])).

thf('98',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ( X9
       != ( k2_relat_1 @ X7 ) )
      | ( r2_hidden @ ( sk_D_2 @ X10 @ X7 ) @ ( k1_relat_1 @ X7 ) )
      | ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('99',plain,(
    ! [X7: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k2_relat_1 @ X7 ) )
      | ( r2_hidden @ ( sk_D_2 @ X10 @ X7 ) @ ( k1_relat_1 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( m3_yellow_6 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( r2_hidden @ ( sk_D_2 @ ( sk_D @ sk_C_1 @ X0 ) @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
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
      | ( r2_hidden @ ( sk_D_2 @ ( sk_D @ sk_C_1 @ X0 ) @ sk_C_1 ) @ sk_A ) ) ),
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
        | ( v7_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ ( sk_D_2 @ ( sk_D @ sk_C_1 @ X0 ) @ sk_C_1 ) ) ) )
   <= ! [X16: $i] :
        ( ~ ( r2_hidden @ X16 @ sk_A )
        | ( v7_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ X16 ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,
    ( ! [X0: $i] :
        ( ( v7_waybel_0 @ ( sk_D @ sk_C_1 @ X0 ) )
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
        | ( v7_waybel_0 @ ( sk_D @ sk_C_1 @ X0 ) ) )
   <= ! [X16: $i] :
        ( ~ ( r2_hidden @ X16 @ sk_A )
        | ( v7_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,
    ( ~ ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B )
   <= ~ ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('110',plain,
    ( ( ( v7_waybel_0 @ ( sk_D @ sk_C_1 @ sk_B ) )
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
    ( ( v7_waybel_0 @ ( sk_D @ sk_C_1 @ sk_B ) )
   <= ( ~ ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B )
      & ! [X16: $i] :
          ( ~ ( r2_hidden @ X16 @ sk_A )
          | ( v7_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ X16 ) ) ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( m3_yellow_6 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( sk_D @ sk_C_1 @ X0 )
        = ( k1_funct_1 @ sk_C_1 @ ( sk_D_2 @ ( sk_D @ sk_C_1 @ X0 ) @ sk_C_1 ) ) ) ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( m3_yellow_6 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( r2_hidden @ ( sk_D_2 @ ( sk_D @ sk_C_1 @ X0 ) @ sk_C_1 ) @ sk_A ) ) ),
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
        | ( v4_orders_2 @ ( k1_funct_1 @ sk_C_1 @ ( sk_D_2 @ ( sk_D @ sk_C_1 @ X0 ) @ sk_C_1 ) ) ) )
   <= ! [X16: $i] :
        ( ~ ( r2_hidden @ X16 @ sk_A )
        | ( v4_orders_2 @ ( k1_funct_1 @ sk_C_1 @ X16 ) ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ! [X0: $i] :
        ( ( v4_orders_2 @ ( sk_D @ sk_C_1 @ X0 ) )
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
        | ( v4_orders_2 @ ( sk_D @ sk_C_1 @ X0 ) ) )
   <= ! [X16: $i] :
        ( ~ ( r2_hidden @ X16 @ sk_A )
        | ( v4_orders_2 @ ( k1_funct_1 @ sk_C_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,
    ( ~ ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B )
   <= ~ ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('120',plain,
    ( ( ( v4_orders_2 @ ( sk_D @ sk_C_1 @ sk_B ) )
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
    ( ( v4_orders_2 @ ( sk_D @ sk_C_1 @ sk_B ) )
   <= ( ~ ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B )
      & ! [X16: $i] :
          ( ~ ( r2_hidden @ X16 @ sk_A )
          | ( v4_orders_2 @ ( k1_funct_1 @ sk_C_1 @ X16 ) ) ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( m3_yellow_6 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( sk_D @ sk_C_1 @ X0 )
        = ( k1_funct_1 @ sk_C_1 @ ( sk_D_2 @ ( sk_D @ sk_C_1 @ X0 ) @ sk_C_1 ) ) ) ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( m3_yellow_6 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( r2_hidden @ ( sk_D_2 @ ( sk_D @ sk_C_1 @ X0 ) @ sk_C_1 ) @ sk_A ) ) ),
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
        | ( l1_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ ( sk_D_2 @ ( sk_D @ sk_C_1 @ X0 ) @ sk_C_1 ) ) @ sk_B ) )
   <= ! [X16: $i] :
        ( ~ ( r2_hidden @ X16 @ sk_A )
        | ( l1_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ X16 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,
    ( ! [X0: $i] :
        ( ( l1_waybel_0 @ ( sk_D @ sk_C_1 @ X0 ) @ sk_B )
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
        | ( l1_waybel_0 @ ( sk_D @ sk_C_1 @ X0 ) @ sk_B ) )
   <= ! [X16: $i] :
        ( ~ ( r2_hidden @ X16 @ sk_A )
        | ( l1_waybel_0 @ ( k1_funct_1 @ sk_C_1 @ X16 ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v4_relat_1 @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_partfun1 @ X0 @ X1 )
      | ~ ( l1_waybel_0 @ ( sk_D @ X0 @ X2 ) @ X2 )
      | ~ ( v7_waybel_0 @ ( sk_D @ X0 @ X2 ) )
      | ~ ( v4_orders_2 @ ( sk_D @ X0 @ X2 ) )
      | ( v2_struct_0 @ ( sk_D @ X0 @ X2 ) )
      | ( m3_yellow_6 @ X0 @ X1 @ X2 )
      | ~ ( l1_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d15_yellow_6])).

thf('130',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_struct_0 @ sk_B )
        | ( m3_yellow_6 @ sk_C_1 @ sk_A @ sk_B )
        | ~ ( l1_struct_0 @ sk_B )
        | ( m3_yellow_6 @ sk_C_1 @ X0 @ sk_B )
        | ( v2_struct_0 @ ( sk_D @ sk_C_1 @ sk_B ) )
        | ~ ( v4_orders_2 @ ( sk_D @ sk_C_1 @ sk_B ) )
        | ~ ( v7_waybel_0 @ ( sk_D @ sk_C_1 @ sk_B ) )
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
        | ( v2_struct_0 @ ( sk_D @ sk_C_1 @ sk_B ) )
        | ~ ( v4_orders_2 @ ( sk_D @ sk_C_1 @ sk_B ) )
        | ~ ( v7_waybel_0 @ ( sk_D @ sk_C_1 @ sk_B ) )
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
        | ~ ( v7_waybel_0 @ ( sk_D @ sk_C_1 @ sk_B ) )
        | ( v2_struct_0 @ ( sk_D @ sk_C_1 @ sk_B ) )
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
        | ( v2_struct_0 @ ( sk_D @ sk_C_1 @ sk_B ) )
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
      | ( v2_struct_0 @ ( sk_D @ sk_C_1 @ sk_B ) )
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
    ( ( ( v2_struct_0 @ ( sk_D @ sk_C_1 @ sk_B ) )
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
      | ( v2_struct_0 @ ( sk_D @ sk_C_1 @ sk_B ) ) )
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
    ( ( v2_struct_0 @ ( sk_D @ sk_C_1 @ sk_B ) )
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
      | ( r2_hidden @ ( sk_D_2 @ ( sk_D @ sk_C_1 @ X0 ) @ sk_C_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['100','101','102','103'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( m3_yellow_6 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( sk_D @ sk_C_1 @ X0 )
        = ( k1_funct_1 @ sk_C_1 @ ( sk_D_2 @ ( sk_D @ sk_C_1 @ X0 ) @ sk_C_1 ) ) ) ) ),
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
        ( ~ ( v2_struct_0 @ ( sk_D @ sk_C_1 @ X0 ) )
        | ~ ( l1_struct_0 @ X0 )
        | ( m3_yellow_6 @ sk_C_1 @ sk_A @ X0 )
        | ~ ( r2_hidden @ ( sk_D_2 @ ( sk_D @ sk_C_1 @ X0 ) @ sk_C_1 ) @ sk_A ) )
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
        | ~ ( v2_struct_0 @ ( sk_D @ sk_C_1 @ X0 ) ) )
   <= ! [X16: $i] :
        ( ~ ( r2_hidden @ X16 @ sk_A )
        | ~ ( v2_struct_0 @ ( k1_funct_1 @ sk_C_1 @ X16 ) ) ) ),
    inference('sup-',[status(thm)],['144','147'])).

thf('149',plain,
    ( ! [X0: $i] :
        ( ~ ( v2_struct_0 @ ( sk_D @ sk_C_1 @ X0 ) )
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
