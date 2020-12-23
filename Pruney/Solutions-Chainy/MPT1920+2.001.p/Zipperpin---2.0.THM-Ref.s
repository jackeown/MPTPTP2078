%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.b9R0z6C7w0

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:54 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 446 expanded)
%              Number of leaves         :   31 ( 145 expanded)
%              Depth                    :   15
%              Number of atoms          : 1055 (5075 expanded)
%              Number of equality atoms :   27 (  36 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(m1_yellow_6_type,type,(
    m1_yellow_6: $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(u1_waybel_0_type,type,(
    u1_waybel_0: $i > $i > $i )).

thf(m1_yellow_0_type,type,(
    m1_yellow_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t18_yellow_6,conjecture,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_waybel_0 @ B @ A )
         => ! [C: $i] :
              ( ( m1_yellow_6 @ C @ A @ B )
             => ! [D: $i] :
                  ( ( m1_yellow_6 @ D @ A @ C )
                 => ( m1_yellow_6 @ D @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_struct_0 @ A )
       => ! [B: $i] :
            ( ( l1_waybel_0 @ B @ A )
           => ! [C: $i] :
                ( ( m1_yellow_6 @ C @ A @ B )
               => ! [D: $i] :
                    ( ( m1_yellow_6 @ D @ A @ C )
                   => ( m1_yellow_6 @ D @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t18_yellow_6])).

thf('0',plain,(
    ~ ( m1_yellow_6 @ sk_D @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_yellow_6 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_yellow_6,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_waybel_0 @ B @ A )
         => ! [C: $i] :
              ( ( l1_waybel_0 @ C @ A )
             => ( ( m1_yellow_6 @ C @ A @ B )
              <=> ( ( m1_yellow_0 @ C @ B )
                  & ( ( u1_waybel_0 @ A @ C )
                    = ( k2_partfun1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( l1_waybel_0 @ X16 @ X17 )
      | ~ ( m1_yellow_6 @ X18 @ X17 @ X16 )
      | ( ( u1_waybel_0 @ X17 @ X18 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X17 ) @ ( u1_waybel_0 @ X17 @ X16 ) @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_waybel_0 @ X18 @ X17 )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d8_yellow_6])).

thf('3',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( l1_waybel_0 @ sk_C @ sk_A )
    | ( ( u1_waybel_0 @ sk_A @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_yellow_6 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_yellow_6,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_waybel_0 @ B @ A ) )
     => ! [C: $i] :
          ( ( m1_yellow_6 @ C @ A @ B )
         => ( l1_waybel_0 @ C @ A ) ) ) )).

thf('6',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( l1_struct_0 @ X19 )
      | ~ ( l1_waybel_0 @ X20 @ X19 )
      | ( l1_waybel_0 @ X21 @ X19 )
      | ~ ( m1_yellow_6 @ X21 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_yellow_6])).

thf('7',plain,
    ( ( l1_waybel_0 @ sk_C @ sk_A )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_waybel_0 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_u1_waybel_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_waybel_0 @ B @ A ) )
     => ( ( v1_funct_1 @ ( u1_waybel_0 @ A @ B ) )
        & ( v1_funct_2 @ ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ ( u1_waybel_0 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_struct_0 @ X14 )
      | ~ ( l1_waybel_0 @ X15 @ X14 )
      | ( m1_subset_1 @ ( u1_waybel_0 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X14 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_u1_waybel_0])).

thf('13',plain,
    ( ( m1_subset_1 @ ( u1_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ ( u1_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('16',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ( ( k2_partfun1 @ X7 @ X8 @ X6 @ X9 )
        = ( k7_relat_1 @ X6 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) @ X0 )
        = ( k7_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( v1_funct_1 @ ( u1_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_struct_0 @ X14 )
      | ~ ( l1_waybel_0 @ X15 @ X14 )
      | ( v1_funct_1 @ ( u1_waybel_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_u1_waybel_0])).

thf('20',plain,
    ( ( v1_funct_1 @ ( u1_waybel_0 @ sk_A @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_1 @ ( u1_waybel_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) @ X0 )
      = ( k7_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['17','22'])).

thf('24',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( u1_waybel_0 @ sk_A @ sk_C )
    = ( k7_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['3','4','10','23','24'])).

thf('26',plain,(
    m1_yellow_6 @ sk_D @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( l1_waybel_0 @ X16 @ X17 )
      | ~ ( m1_yellow_6 @ X18 @ X17 @ X16 )
      | ( m1_yellow_0 @ X18 @ X16 )
      | ~ ( l1_waybel_0 @ X18 @ X17 )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d8_yellow_6])).

thf('28',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( l1_waybel_0 @ sk_D @ sk_A )
    | ( m1_yellow_0 @ sk_D @ sk_C )
    | ~ ( l1_waybel_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_yellow_6 @ sk_D @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( l1_struct_0 @ X19 )
      | ~ ( l1_waybel_0 @ X20 @ X19 )
      | ( l1_waybel_0 @ X21 @ X19 )
      | ~ ( m1_yellow_6 @ X21 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_yellow_6])).

thf('32',plain,
    ( ( l1_waybel_0 @ sk_D @ sk_A )
    | ~ ( l1_waybel_0 @ sk_C @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( l1_waybel_0 @ sk_D @ sk_A )
    | ~ ( l1_waybel_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    l1_waybel_0 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('36',plain,(
    l1_waybel_0 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    l1_waybel_0 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('38',plain,(
    m1_yellow_0 @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['28','29','36','37'])).

thf(d13_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( l1_orders_2 @ B )
         => ( ( m1_yellow_0 @ B @ A )
          <=> ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
              & ( r1_tarski @ ( u1_orders_2 @ B ) @ ( u1_orders_2 @ A ) ) ) ) ) ) )).

thf('39',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_orders_2 @ X10 )
      | ~ ( m1_yellow_0 @ X10 @ X11 )
      | ( r1_tarski @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d13_yellow_0])).

thf('40',plain,
    ( ~ ( l1_orders_2 @ sk_C )
    | ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) )
    | ~ ( l1_orders_2 @ sk_D ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_waybel_0 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['7','8','9'])).

thf(dt_l1_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_waybel_0 @ B @ A )
         => ( l1_orders_2 @ B ) ) ) )).

thf('42',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_waybel_0 @ X12 @ X13 )
      | ( l1_orders_2 @ X12 )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_0])).

thf('43',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( l1_orders_2 @ sk_C ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_orders_2 @ sk_C ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    l1_waybel_0 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['34','35'])).

thf('47',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_waybel_0 @ X12 @ X13 )
      | ( l1_orders_2 @ X12 )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_0])).

thf('48',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( l1_orders_2 @ sk_D ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    l1_orders_2 @ sk_D ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['40','45','50'])).

thf(t82_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r1_tarski @ A @ B )
       => ( ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
            = ( k7_relat_1 @ C @ A ) )
          & ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A )
            = ( k7_relat_1 @ C @ A ) ) ) ) ) )).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k7_relat_1 @ X2 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[t82_funct_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ ( u1_struct_0 @ sk_C ) ) @ ( u1_struct_0 @ sk_D ) )
        = ( k7_relat_1 @ X0 @ ( u1_struct_0 @ sk_D ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( k7_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_D ) )
      = ( k7_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_1 @ ( u1_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['25','53'])).

thf('55',plain,(
    m1_yellow_6 @ sk_D @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( l1_waybel_0 @ X16 @ X17 )
      | ~ ( m1_yellow_6 @ X18 @ X17 @ X16 )
      | ( ( u1_waybel_0 @ X17 @ X18 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X17 ) @ ( u1_waybel_0 @ X17 @ X16 ) @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_waybel_0 @ X18 @ X17 )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d8_yellow_6])).

thf('57',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( l1_waybel_0 @ sk_D @ sk_A )
    | ( ( u1_waybel_0 @ sk_A @ sk_D )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_D ) ) )
    | ~ ( l1_waybel_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    l1_waybel_0 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['34','35'])).

thf('60',plain,(
    l1_waybel_0 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('61',plain,
    ( ( u1_waybel_0 @ sk_A @ sk_D )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['57','58','59','60'])).

thf('62',plain,(
    l1_waybel_0 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('63',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_struct_0 @ X14 )
      | ~ ( l1_waybel_0 @ X15 @ X14 )
      | ( m1_subset_1 @ ( u1_waybel_0 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X14 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_u1_waybel_0])).

thf('64',plain,
    ( ( m1_subset_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    m1_subset_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ( ( k2_partfun1 @ X7 @ X8 @ X6 @ X9 )
        = ( k7_relat_1 @ X6 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_C ) @ X0 )
        = ( k7_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) @ X0 ) )
      | ~ ( v1_funct_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    l1_waybel_0 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('70',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_struct_0 @ X14 )
      | ~ ( l1_waybel_0 @ X15 @ X14 )
      | ( v1_funct_1 @ ( u1_waybel_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_u1_waybel_0])).

thf('71',plain,
    ( ( v1_funct_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_C ) @ X0 )
      = ( k7_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['68','73'])).

thf('75',plain,
    ( ( u1_waybel_0 @ sk_A @ sk_D )
    = ( k7_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['61','74'])).

thf('76',plain,(
    m1_subset_1 @ ( u1_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('77',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('78',plain,(
    v1_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_funct_1 @ ( u1_waybel_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('80',plain,
    ( ( u1_waybel_0 @ sk_A @ sk_D )
    = ( k7_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['54','75','78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B ) @ X0 )
      = ( k7_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['17','22'])).

thf('82',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( l1_waybel_0 @ X16 @ X17 )
      | ~ ( m1_yellow_0 @ X18 @ X16 )
      | ( ( u1_waybel_0 @ X17 @ X18 )
       != ( k2_partfun1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X17 ) @ ( u1_waybel_0 @ X17 @ X16 ) @ ( u1_struct_0 @ X18 ) ) )
      | ( m1_yellow_6 @ X18 @ X17 @ X16 )
      | ~ ( l1_waybel_0 @ X18 @ X17 )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d8_yellow_6])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( ( u1_waybel_0 @ sk_A @ X0 )
       != ( k7_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_B ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( m1_yellow_6 @ X0 @ sk_A @ sk_B )
      | ~ ( m1_yellow_0 @ X0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( ( u1_waybel_0 @ sk_A @ X0 )
       != ( k7_relat_1 @ ( u1_waybel_0 @ sk_A @ sk_B ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_waybel_0 @ X0 @ sk_A )
      | ( m1_yellow_6 @ X0 @ sk_A @ sk_B )
      | ~ ( m1_yellow_0 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,
    ( ( ( u1_waybel_0 @ sk_A @ sk_D )
     != ( u1_waybel_0 @ sk_A @ sk_D ) )
    | ~ ( m1_yellow_0 @ sk_D @ sk_B )
    | ( m1_yellow_6 @ sk_D @ sk_A @ sk_B )
    | ~ ( l1_waybel_0 @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['80','86'])).

thf('88',plain,(
    m1_yellow_0 @ sk_D @ sk_C ),
    inference(demod,[status(thm)],['28','29','36','37'])).

thf('89',plain,(
    m1_yellow_6 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( l1_waybel_0 @ X16 @ X17 )
      | ~ ( m1_yellow_6 @ X18 @ X17 @ X16 )
      | ( m1_yellow_0 @ X18 @ X16 )
      | ~ ( l1_waybel_0 @ X18 @ X17 )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d8_yellow_6])).

thf('91',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( l1_waybel_0 @ sk_C @ sk_A )
    | ( m1_yellow_0 @ sk_C @ sk_B )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    l1_waybel_0 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('94',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    m1_yellow_0 @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['91','92','93','94'])).

thf(t16_yellow_6,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_yellow_0 @ B @ A )
         => ! [C: $i] :
              ( ( m1_yellow_0 @ C @ B )
             => ( m1_yellow_0 @ C @ A ) ) ) ) )).

thf('96',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_yellow_0 @ X22 @ X23 )
      | ( m1_yellow_0 @ X24 @ X23 )
      | ~ ( m1_yellow_0 @ X24 @ X22 )
      | ~ ( l1_orders_2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t16_yellow_6])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_B )
      | ~ ( m1_yellow_0 @ X0 @ sk_C )
      | ( m1_yellow_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_waybel_0 @ X12 @ X13 )
      | ( l1_orders_2 @ X12 )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_0])).

thf('100',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( l1_orders_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    l1_orders_2 @ sk_B ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( m1_yellow_0 @ X0 @ sk_C )
      | ( m1_yellow_0 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['97','102'])).

thf('104',plain,(
    m1_yellow_0 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['88','103'])).

thf('105',plain,(
    l1_waybel_0 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['34','35'])).

thf('106',plain,
    ( ( ( u1_waybel_0 @ sk_A @ sk_D )
     != ( u1_waybel_0 @ sk_A @ sk_D ) )
    | ( m1_yellow_6 @ sk_D @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['87','104','105'])).

thf('107',plain,(
    m1_yellow_6 @ sk_D @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    $false ),
    inference(demod,[status(thm)],['0','107'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.b9R0z6C7w0
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:03:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 70 iterations in 0.029s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.47  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.20/0.47  thf(m1_yellow_6_type, type, m1_yellow_6: $i > $i > $i > $o).
% 0.20/0.47  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.47  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.20/0.47  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.47  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.47  thf(u1_waybel_0_type, type, u1_waybel_0: $i > $i > $i).
% 0.20/0.47  thf(m1_yellow_0_type, type, m1_yellow_0: $i > $i > $o).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.48  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.48  thf(t18_yellow_6, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_struct_0 @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( l1_waybel_0 @ B @ A ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( m1_yellow_6 @ C @ A @ B ) =>
% 0.20/0.48               ( ![D:$i]:
% 0.20/0.48                 ( ( m1_yellow_6 @ D @ A @ C ) => ( m1_yellow_6 @ D @ A @ B ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( l1_struct_0 @ A ) =>
% 0.20/0.48          ( ![B:$i]:
% 0.20/0.48            ( ( l1_waybel_0 @ B @ A ) =>
% 0.20/0.48              ( ![C:$i]:
% 0.20/0.48                ( ( m1_yellow_6 @ C @ A @ B ) =>
% 0.20/0.48                  ( ![D:$i]:
% 0.20/0.48                    ( ( m1_yellow_6 @ D @ A @ C ) =>
% 0.20/0.48                      ( m1_yellow_6 @ D @ A @ B ) ) ) ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t18_yellow_6])).
% 0.20/0.48  thf('0', plain, (~ (m1_yellow_6 @ sk_D @ sk_A @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain, ((m1_yellow_6 @ sk_C @ sk_A @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(d8_yellow_6, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_struct_0 @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( l1_waybel_0 @ B @ A ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( l1_waybel_0 @ C @ A ) =>
% 0.20/0.48               ( ( m1_yellow_6 @ C @ A @ B ) <=>
% 0.20/0.48                 ( ( m1_yellow_0 @ C @ B ) & 
% 0.20/0.48                   ( ( u1_waybel_0 @ A @ C ) =
% 0.20/0.48                     ( k2_partfun1 @
% 0.20/0.48                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.20/0.48                       ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.48         (~ (l1_waybel_0 @ X16 @ X17)
% 0.20/0.48          | ~ (m1_yellow_6 @ X18 @ X17 @ X16)
% 0.20/0.48          | ((u1_waybel_0 @ X17 @ X18)
% 0.20/0.48              = (k2_partfun1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X17) @ 
% 0.20/0.48                 (u1_waybel_0 @ X17 @ X16) @ (u1_struct_0 @ X18)))
% 0.20/0.48          | ~ (l1_waybel_0 @ X18 @ X17)
% 0.20/0.48          | ~ (l1_struct_0 @ X17))),
% 0.20/0.48      inference('cnf', [status(esa)], [d8_yellow_6])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      ((~ (l1_struct_0 @ sk_A)
% 0.20/0.48        | ~ (l1_waybel_0 @ sk_C @ sk_A)
% 0.20/0.48        | ((u1_waybel_0 @ sk_A @ sk_C)
% 0.20/0.48            = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.48               (u1_waybel_0 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_C)))
% 0.20/0.48        | ~ (l1_waybel_0 @ sk_B @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.48  thf('4', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('5', plain, ((m1_yellow_6 @ sk_C @ sk_A @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(dt_m1_yellow_6, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( l1_struct_0 @ A ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.48       ( ![C:$i]: ( ( m1_yellow_6 @ C @ A @ B ) => ( l1_waybel_0 @ C @ A ) ) ) ))).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.48         (~ (l1_struct_0 @ X19)
% 0.20/0.48          | ~ (l1_waybel_0 @ X20 @ X19)
% 0.20/0.48          | (l1_waybel_0 @ X21 @ X19)
% 0.20/0.48          | ~ (m1_yellow_6 @ X21 @ X19 @ X20))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_m1_yellow_6])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (((l1_waybel_0 @ sk_C @ sk_A)
% 0.20/0.48        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.20/0.48        | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.48  thf('8', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('9', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('10', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.20/0.48  thf('11', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(dt_u1_waybel_0, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( l1_struct_0 @ A ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.48       ( ( v1_funct_1 @ ( u1_waybel_0 @ A @ B ) ) & 
% 0.20/0.48         ( v1_funct_2 @
% 0.20/0.48           ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.48         ( m1_subset_1 @
% 0.20/0.48           ( u1_waybel_0 @ A @ B ) @ 
% 0.20/0.48           ( k1_zfmisc_1 @
% 0.20/0.48             ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (![X14 : $i, X15 : $i]:
% 0.20/0.48         (~ (l1_struct_0 @ X14)
% 0.20/0.48          | ~ (l1_waybel_0 @ X15 @ X14)
% 0.20/0.48          | (m1_subset_1 @ (u1_waybel_0 @ X14 @ X15) @ 
% 0.20/0.48             (k1_zfmisc_1 @ 
% 0.20/0.48              (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X14)))))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_u1_waybel_0])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (((m1_subset_1 @ (u1_waybel_0 @ sk_A @ sk_B) @ 
% 0.20/0.48         (k1_zfmisc_1 @ 
% 0.20/0.48          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 0.20/0.48        | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.48  thf('14', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      ((m1_subset_1 @ (u1_waybel_0 @ sk_A @ sk_B) @ 
% 0.20/0.48        (k1_zfmisc_1 @ 
% 0.20/0.48         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.48      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.48  thf(redefinition_k2_partfun1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.48       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8)))
% 0.20/0.48          | ~ (v1_funct_1 @ X6)
% 0.20/0.48          | ((k2_partfun1 @ X7 @ X8 @ X6 @ X9) = (k7_relat_1 @ X6 @ X9)))),
% 0.20/0.48      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.48            (u1_waybel_0 @ sk_A @ sk_B) @ X0)
% 0.20/0.48            = (k7_relat_1 @ (u1_waybel_0 @ sk_A @ sk_B) @ X0))
% 0.20/0.48          | ~ (v1_funct_1 @ (u1_waybel_0 @ sk_A @ sk_B)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.48  thf('18', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (![X14 : $i, X15 : $i]:
% 0.20/0.48         (~ (l1_struct_0 @ X14)
% 0.20/0.48          | ~ (l1_waybel_0 @ X15 @ X14)
% 0.20/0.48          | (v1_funct_1 @ (u1_waybel_0 @ X14 @ X15)))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_u1_waybel_0])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (((v1_funct_1 @ (u1_waybel_0 @ sk_A @ sk_B)) | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.48  thf('21', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('22', plain, ((v1_funct_1 @ (u1_waybel_0 @ sk_A @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.48           (u1_waybel_0 @ sk_A @ sk_B) @ X0)
% 0.20/0.48           = (k7_relat_1 @ (u1_waybel_0 @ sk_A @ sk_B) @ X0))),
% 0.20/0.48      inference('demod', [status(thm)], ['17', '22'])).
% 0.20/0.48  thf('24', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      (((u1_waybel_0 @ sk_A @ sk_C)
% 0.20/0.48         = (k7_relat_1 @ (u1_waybel_0 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_C)))),
% 0.20/0.48      inference('demod', [status(thm)], ['3', '4', '10', '23', '24'])).
% 0.20/0.48  thf('26', plain, ((m1_yellow_6 @ sk_D @ sk_A @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.48         (~ (l1_waybel_0 @ X16 @ X17)
% 0.20/0.48          | ~ (m1_yellow_6 @ X18 @ X17 @ X16)
% 0.20/0.48          | (m1_yellow_0 @ X18 @ X16)
% 0.20/0.48          | ~ (l1_waybel_0 @ X18 @ X17)
% 0.20/0.48          | ~ (l1_struct_0 @ X17))),
% 0.20/0.48      inference('cnf', [status(esa)], [d8_yellow_6])).
% 0.20/0.48  thf('28', plain,
% 0.20/0.48      ((~ (l1_struct_0 @ sk_A)
% 0.20/0.48        | ~ (l1_waybel_0 @ sk_D @ sk_A)
% 0.20/0.48        | (m1_yellow_0 @ sk_D @ sk_C)
% 0.20/0.48        | ~ (l1_waybel_0 @ sk_C @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.48  thf('29', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('30', plain, ((m1_yellow_6 @ sk_D @ sk_A @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('31', plain,
% 0.20/0.48      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.48         (~ (l1_struct_0 @ X19)
% 0.20/0.48          | ~ (l1_waybel_0 @ X20 @ X19)
% 0.20/0.48          | (l1_waybel_0 @ X21 @ X19)
% 0.20/0.48          | ~ (m1_yellow_6 @ X21 @ X19 @ X20))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_m1_yellow_6])).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      (((l1_waybel_0 @ sk_D @ sk_A)
% 0.20/0.48        | ~ (l1_waybel_0 @ sk_C @ sk_A)
% 0.20/0.48        | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.48  thf('33', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('34', plain,
% 0.20/0.48      (((l1_waybel_0 @ sk_D @ sk_A) | ~ (l1_waybel_0 @ sk_C @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.48  thf('35', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.20/0.48  thf('36', plain, ((l1_waybel_0 @ sk_D @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.48  thf('37', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.20/0.48  thf('38', plain, ((m1_yellow_0 @ sk_D @ sk_C)),
% 0.20/0.48      inference('demod', [status(thm)], ['28', '29', '36', '37'])).
% 0.20/0.48  thf(d13_yellow_0, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_orders_2 @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( l1_orders_2 @ B ) =>
% 0.20/0.48           ( ( m1_yellow_0 @ B @ A ) <=>
% 0.20/0.48             ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.48               ( r1_tarski @ ( u1_orders_2 @ B ) @ ( u1_orders_2 @ A ) ) ) ) ) ) ))).
% 0.20/0.48  thf('39', plain,
% 0.20/0.48      (![X10 : $i, X11 : $i]:
% 0.20/0.48         (~ (l1_orders_2 @ X10)
% 0.20/0.48          | ~ (m1_yellow_0 @ X10 @ X11)
% 0.20/0.48          | (r1_tarski @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X11))
% 0.20/0.48          | ~ (l1_orders_2 @ X11))),
% 0.20/0.48      inference('cnf', [status(esa)], [d13_yellow_0])).
% 0.20/0.48  thf('40', plain,
% 0.20/0.48      ((~ (l1_orders_2 @ sk_C)
% 0.20/0.48        | (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))
% 0.20/0.48        | ~ (l1_orders_2 @ sk_D))),
% 0.20/0.48      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.48  thf('41', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.20/0.48  thf(dt_l1_waybel_0, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_struct_0 @ A ) =>
% 0.20/0.48       ( ![B:$i]: ( ( l1_waybel_0 @ B @ A ) => ( l1_orders_2 @ B ) ) ) ))).
% 0.20/0.48  thf('42', plain,
% 0.20/0.48      (![X12 : $i, X13 : $i]:
% 0.20/0.48         (~ (l1_waybel_0 @ X12 @ X13)
% 0.20/0.48          | (l1_orders_2 @ X12)
% 0.20/0.48          | ~ (l1_struct_0 @ X13))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_l1_waybel_0])).
% 0.20/0.48  thf('43', plain, ((~ (l1_struct_0 @ sk_A) | (l1_orders_2 @ sk_C))),
% 0.20/0.48      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.48  thf('44', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('45', plain, ((l1_orders_2 @ sk_C)),
% 0.20/0.48      inference('demod', [status(thm)], ['43', '44'])).
% 0.20/0.48  thf('46', plain, ((l1_waybel_0 @ sk_D @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.48  thf('47', plain,
% 0.20/0.48      (![X12 : $i, X13 : $i]:
% 0.20/0.48         (~ (l1_waybel_0 @ X12 @ X13)
% 0.20/0.48          | (l1_orders_2 @ X12)
% 0.20/0.48          | ~ (l1_struct_0 @ X13))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_l1_waybel_0])).
% 0.20/0.48  thf('48', plain, ((~ (l1_struct_0 @ sk_A) | (l1_orders_2 @ sk_D))),
% 0.20/0.48      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.48  thf('49', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('50', plain, ((l1_orders_2 @ sk_D)),
% 0.20/0.48      inference('demod', [status(thm)], ['48', '49'])).
% 0.20/0.48  thf('51', plain, ((r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['40', '45', '50'])).
% 0.20/0.48  thf(t82_funct_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.48       ( ( r1_tarski @ A @ B ) =>
% 0.20/0.48         ( ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.20/0.48             ( k7_relat_1 @ C @ A ) ) & 
% 0.20/0.48           ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A ) =
% 0.20/0.48             ( k7_relat_1 @ C @ A ) ) ) ) ))).
% 0.20/0.48  thf('52', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (~ (r1_tarski @ X0 @ X1)
% 0.20/0.48          | ~ (v1_relat_1 @ X2)
% 0.20/0.48          | ~ (v1_funct_1 @ X2)
% 0.20/0.48          | ((k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)
% 0.20/0.48              = (k7_relat_1 @ X2 @ X0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t82_funct_1])).
% 0.20/0.48  thf('53', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k7_relat_1 @ (k7_relat_1 @ X0 @ (u1_struct_0 @ sk_C)) @ 
% 0.20/0.48            (u1_struct_0 @ sk_D)) = (k7_relat_1 @ X0 @ (u1_struct_0 @ sk_D)))
% 0.20/0.48          | ~ (v1_funct_1 @ X0)
% 0.20/0.48          | ~ (v1_relat_1 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.48  thf('54', plain,
% 0.20/0.48      ((((k7_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_D))
% 0.20/0.48          = (k7_relat_1 @ (u1_waybel_0 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_D)))
% 0.20/0.48        | ~ (v1_relat_1 @ (u1_waybel_0 @ sk_A @ sk_B))
% 0.20/0.48        | ~ (v1_funct_1 @ (u1_waybel_0 @ sk_A @ sk_B)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['25', '53'])).
% 0.20/0.48  thf('55', plain, ((m1_yellow_6 @ sk_D @ sk_A @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('56', plain,
% 0.20/0.48      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.48         (~ (l1_waybel_0 @ X16 @ X17)
% 0.20/0.48          | ~ (m1_yellow_6 @ X18 @ X17 @ X16)
% 0.20/0.48          | ((u1_waybel_0 @ X17 @ X18)
% 0.20/0.48              = (k2_partfun1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X17) @ 
% 0.20/0.48                 (u1_waybel_0 @ X17 @ X16) @ (u1_struct_0 @ X18)))
% 0.20/0.48          | ~ (l1_waybel_0 @ X18 @ X17)
% 0.20/0.48          | ~ (l1_struct_0 @ X17))),
% 0.20/0.48      inference('cnf', [status(esa)], [d8_yellow_6])).
% 0.20/0.48  thf('57', plain,
% 0.20/0.48      ((~ (l1_struct_0 @ sk_A)
% 0.20/0.48        | ~ (l1_waybel_0 @ sk_D @ sk_A)
% 0.20/0.48        | ((u1_waybel_0 @ sk_A @ sk_D)
% 0.20/0.48            = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.48               (u1_waybel_0 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_D)))
% 0.20/0.48        | ~ (l1_waybel_0 @ sk_C @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['55', '56'])).
% 0.20/0.48  thf('58', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('59', plain, ((l1_waybel_0 @ sk_D @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.48  thf('60', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.20/0.48  thf('61', plain,
% 0.20/0.48      (((u1_waybel_0 @ sk_A @ sk_D)
% 0.20/0.48         = (k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.48            (u1_waybel_0 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_D)))),
% 0.20/0.48      inference('demod', [status(thm)], ['57', '58', '59', '60'])).
% 0.20/0.48  thf('62', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.20/0.48  thf('63', plain,
% 0.20/0.48      (![X14 : $i, X15 : $i]:
% 0.20/0.48         (~ (l1_struct_0 @ X14)
% 0.20/0.48          | ~ (l1_waybel_0 @ X15 @ X14)
% 0.20/0.48          | (m1_subset_1 @ (u1_waybel_0 @ X14 @ X15) @ 
% 0.20/0.48             (k1_zfmisc_1 @ 
% 0.20/0.48              (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X14)))))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_u1_waybel_0])).
% 0.20/0.48  thf('64', plain,
% 0.20/0.48      (((m1_subset_1 @ (u1_waybel_0 @ sk_A @ sk_C) @ 
% 0.20/0.48         (k1_zfmisc_1 @ 
% 0.20/0.48          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 0.20/0.48        | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['62', '63'])).
% 0.20/0.48  thf('65', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('66', plain,
% 0.20/0.48      ((m1_subset_1 @ (u1_waybel_0 @ sk_A @ sk_C) @ 
% 0.20/0.48        (k1_zfmisc_1 @ 
% 0.20/0.48         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.48      inference('demod', [status(thm)], ['64', '65'])).
% 0.20/0.48  thf('67', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8)))
% 0.20/0.48          | ~ (v1_funct_1 @ X6)
% 0.20/0.48          | ((k2_partfun1 @ X7 @ X8 @ X6 @ X9) = (k7_relat_1 @ X6 @ X9)))),
% 0.20/0.48      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.20/0.48  thf('68', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.48            (u1_waybel_0 @ sk_A @ sk_C) @ X0)
% 0.20/0.48            = (k7_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C) @ X0))
% 0.20/0.48          | ~ (v1_funct_1 @ (u1_waybel_0 @ sk_A @ sk_C)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['66', '67'])).
% 0.20/0.48  thf('69', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.20/0.48  thf('70', plain,
% 0.20/0.48      (![X14 : $i, X15 : $i]:
% 0.20/0.48         (~ (l1_struct_0 @ X14)
% 0.20/0.48          | ~ (l1_waybel_0 @ X15 @ X14)
% 0.20/0.48          | (v1_funct_1 @ (u1_waybel_0 @ X14 @ X15)))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_u1_waybel_0])).
% 0.20/0.48  thf('71', plain,
% 0.20/0.48      (((v1_funct_1 @ (u1_waybel_0 @ sk_A @ sk_C)) | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['69', '70'])).
% 0.20/0.48  thf('72', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('73', plain, ((v1_funct_1 @ (u1_waybel_0 @ sk_A @ sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['71', '72'])).
% 0.20/0.48  thf('74', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((k2_partfun1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.48           (u1_waybel_0 @ sk_A @ sk_C) @ X0)
% 0.20/0.48           = (k7_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C) @ X0))),
% 0.20/0.48      inference('demod', [status(thm)], ['68', '73'])).
% 0.20/0.48  thf('75', plain,
% 0.20/0.48      (((u1_waybel_0 @ sk_A @ sk_D)
% 0.20/0.48         = (k7_relat_1 @ (u1_waybel_0 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_D)))),
% 0.20/0.48      inference('demod', [status(thm)], ['61', '74'])).
% 0.20/0.48  thf('76', plain,
% 0.20/0.48      ((m1_subset_1 @ (u1_waybel_0 @ sk_A @ sk_B) @ 
% 0.20/0.48        (k1_zfmisc_1 @ 
% 0.20/0.48         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.48      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.48  thf(cc1_relset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.48       ( v1_relat_1 @ C ) ))).
% 0.20/0.48  thf('77', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.48         ((v1_relat_1 @ X3)
% 0.20/0.48          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 0.20/0.48      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.48  thf('78', plain, ((v1_relat_1 @ (u1_waybel_0 @ sk_A @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['76', '77'])).
% 0.20/0.48  thf('79', plain, ((v1_funct_1 @ (u1_waybel_0 @ sk_A @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.48  thf('80', plain,
% 0.20/0.48      (((u1_waybel_0 @ sk_A @ sk_D)
% 0.20/0.48         = (k7_relat_1 @ (u1_waybel_0 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_D)))),
% 0.20/0.48      inference('demod', [status(thm)], ['54', '75', '78', '79'])).
% 0.20/0.48  thf('81', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.48           (u1_waybel_0 @ sk_A @ sk_B) @ X0)
% 0.20/0.48           = (k7_relat_1 @ (u1_waybel_0 @ sk_A @ sk_B) @ X0))),
% 0.20/0.48      inference('demod', [status(thm)], ['17', '22'])).
% 0.20/0.48  thf('82', plain,
% 0.20/0.48      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.48         (~ (l1_waybel_0 @ X16 @ X17)
% 0.20/0.48          | ~ (m1_yellow_0 @ X18 @ X16)
% 0.20/0.48          | ((u1_waybel_0 @ X17 @ X18)
% 0.20/0.48              != (k2_partfun1 @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X17) @ 
% 0.20/0.48                  (u1_waybel_0 @ X17 @ X16) @ (u1_struct_0 @ X18)))
% 0.20/0.48          | (m1_yellow_6 @ X18 @ X17 @ X16)
% 0.20/0.48          | ~ (l1_waybel_0 @ X18 @ X17)
% 0.20/0.48          | ~ (l1_struct_0 @ X17))),
% 0.20/0.48      inference('cnf', [status(esa)], [d8_yellow_6])).
% 0.20/0.48  thf('83', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((u1_waybel_0 @ sk_A @ X0)
% 0.20/0.48            != (k7_relat_1 @ (u1_waybel_0 @ sk_A @ sk_B) @ (u1_struct_0 @ X0)))
% 0.20/0.48          | ~ (l1_struct_0 @ sk_A)
% 0.20/0.48          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.20/0.48          | (m1_yellow_6 @ X0 @ sk_A @ sk_B)
% 0.20/0.48          | ~ (m1_yellow_0 @ X0 @ sk_B)
% 0.20/0.48          | ~ (l1_waybel_0 @ sk_B @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['81', '82'])).
% 0.20/0.48  thf('84', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('85', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('86', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((u1_waybel_0 @ sk_A @ X0)
% 0.20/0.48            != (k7_relat_1 @ (u1_waybel_0 @ sk_A @ sk_B) @ (u1_struct_0 @ X0)))
% 0.20/0.48          | ~ (l1_waybel_0 @ X0 @ sk_A)
% 0.20/0.48          | (m1_yellow_6 @ X0 @ sk_A @ sk_B)
% 0.20/0.48          | ~ (m1_yellow_0 @ X0 @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.20/0.48  thf('87', plain,
% 0.20/0.48      ((((u1_waybel_0 @ sk_A @ sk_D) != (u1_waybel_0 @ sk_A @ sk_D))
% 0.20/0.48        | ~ (m1_yellow_0 @ sk_D @ sk_B)
% 0.20/0.48        | (m1_yellow_6 @ sk_D @ sk_A @ sk_B)
% 0.20/0.48        | ~ (l1_waybel_0 @ sk_D @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['80', '86'])).
% 0.20/0.48  thf('88', plain, ((m1_yellow_0 @ sk_D @ sk_C)),
% 0.20/0.48      inference('demod', [status(thm)], ['28', '29', '36', '37'])).
% 0.20/0.48  thf('89', plain, ((m1_yellow_6 @ sk_C @ sk_A @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('90', plain,
% 0.20/0.48      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.48         (~ (l1_waybel_0 @ X16 @ X17)
% 0.20/0.48          | ~ (m1_yellow_6 @ X18 @ X17 @ X16)
% 0.20/0.48          | (m1_yellow_0 @ X18 @ X16)
% 0.20/0.48          | ~ (l1_waybel_0 @ X18 @ X17)
% 0.20/0.48          | ~ (l1_struct_0 @ X17))),
% 0.20/0.48      inference('cnf', [status(esa)], [d8_yellow_6])).
% 0.20/0.48  thf('91', plain,
% 0.20/0.48      ((~ (l1_struct_0 @ sk_A)
% 0.20/0.48        | ~ (l1_waybel_0 @ sk_C @ sk_A)
% 0.20/0.48        | (m1_yellow_0 @ sk_C @ sk_B)
% 0.20/0.48        | ~ (l1_waybel_0 @ sk_B @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['89', '90'])).
% 0.20/0.48  thf('92', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('93', plain, ((l1_waybel_0 @ sk_C @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.20/0.48  thf('94', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('95', plain, ((m1_yellow_0 @ sk_C @ sk_B)),
% 0.20/0.48      inference('demod', [status(thm)], ['91', '92', '93', '94'])).
% 0.20/0.48  thf(t16_yellow_6, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_orders_2 @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_yellow_0 @ B @ A ) =>
% 0.20/0.48           ( ![C:$i]: ( ( m1_yellow_0 @ C @ B ) => ( m1_yellow_0 @ C @ A ) ) ) ) ) ))).
% 0.20/0.48  thf('96', plain,
% 0.20/0.48      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.48         (~ (m1_yellow_0 @ X22 @ X23)
% 0.20/0.48          | (m1_yellow_0 @ X24 @ X23)
% 0.20/0.48          | ~ (m1_yellow_0 @ X24 @ X22)
% 0.20/0.48          | ~ (l1_orders_2 @ X23))),
% 0.20/0.48      inference('cnf', [status(esa)], [t16_yellow_6])).
% 0.20/0.48  thf('97', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (l1_orders_2 @ sk_B)
% 0.20/0.48          | ~ (m1_yellow_0 @ X0 @ sk_C)
% 0.20/0.48          | (m1_yellow_0 @ X0 @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['95', '96'])).
% 0.20/0.48  thf('98', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('99', plain,
% 0.20/0.48      (![X12 : $i, X13 : $i]:
% 0.20/0.48         (~ (l1_waybel_0 @ X12 @ X13)
% 0.20/0.48          | (l1_orders_2 @ X12)
% 0.20/0.48          | ~ (l1_struct_0 @ X13))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_l1_waybel_0])).
% 0.20/0.48  thf('100', plain, ((~ (l1_struct_0 @ sk_A) | (l1_orders_2 @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['98', '99'])).
% 0.20/0.48  thf('101', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('102', plain, ((l1_orders_2 @ sk_B)),
% 0.20/0.48      inference('demod', [status(thm)], ['100', '101'])).
% 0.20/0.48  thf('103', plain,
% 0.20/0.48      (![X0 : $i]: (~ (m1_yellow_0 @ X0 @ sk_C) | (m1_yellow_0 @ X0 @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['97', '102'])).
% 0.20/0.48  thf('104', plain, ((m1_yellow_0 @ sk_D @ sk_B)),
% 0.20/0.48      inference('sup-', [status(thm)], ['88', '103'])).
% 0.20/0.48  thf('105', plain, ((l1_waybel_0 @ sk_D @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.48  thf('106', plain,
% 0.20/0.48      ((((u1_waybel_0 @ sk_A @ sk_D) != (u1_waybel_0 @ sk_A @ sk_D))
% 0.20/0.48        | (m1_yellow_6 @ sk_D @ sk_A @ sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['87', '104', '105'])).
% 0.20/0.48  thf('107', plain, ((m1_yellow_6 @ sk_D @ sk_A @ sk_B)),
% 0.20/0.48      inference('simplify', [status(thm)], ['106'])).
% 0.20/0.48  thf('108', plain, ($false), inference('demod', [status(thm)], ['0', '107'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
