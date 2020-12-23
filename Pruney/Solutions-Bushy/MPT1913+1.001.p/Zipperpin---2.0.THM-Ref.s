%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1913+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jwtzJpn2hh

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 264 expanded)
%              Number of leaves         :   22 (  92 expanded)
%              Depth                    :    9
%              Number of atoms          :  839 (4702 expanded)
%              Number of equality atoms :   26 ( 151 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k12_pralg_1_type,type,(
    k12_pralg_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v2_pralg_1_type,type,(
    v2_pralg_1: $i > $o )).

thf(k10_pralg_1_type,type,(
    k10_pralg_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(t9_yellow_6,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v4_relat_1 @ B @ A )
            & ( v1_funct_1 @ B )
            & ( v1_partfun1 @ B @ A )
            & ( v2_pralg_1 @ B ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ( ( k1_funct_1 @ ( k12_pralg_1 @ A @ B ) @ C )
                = ( u1_struct_0 @ ( k10_pralg_1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v4_relat_1 @ B @ A )
              & ( v1_funct_1 @ B )
              & ( v1_partfun1 @ B @ A )
              & ( v2_pralg_1 @ B ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ A )
               => ( ( k1_funct_1 @ ( k12_pralg_1 @ A @ B ) @ C )
                  = ( u1_struct_0 @ ( k10_pralg_1 @ A @ B @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t9_yellow_6])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('2',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    r2_hidden @ sk_C @ sk_A ),
    inference(clc,[status(thm)],['2','3'])).

thf('5',plain,(
    v4_relat_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k12_pralg_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A )
        & ( v1_funct_1 @ B )
        & ( v1_partfun1 @ B @ A )
        & ( v2_pralg_1 @ B ) )
     => ( ( v1_relat_1 @ ( k12_pralg_1 @ A @ B ) )
        & ( v4_relat_1 @ ( k12_pralg_1 @ A @ B ) @ A )
        & ( v1_funct_1 @ ( k12_pralg_1 @ A @ B ) )
        & ( v1_partfun1 @ ( k12_pralg_1 @ A @ B ) @ A ) ) ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v1_partfun1 @ ( k12_pralg_1 @ X5 @ X6 ) @ X5 )
      | ~ ( v2_pralg_1 @ X6 )
      | ~ ( v1_partfun1 @ X6 @ X5 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v4_relat_1 @ X6 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k12_pralg_1])).

thf('7',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_partfun1 @ sk_B @ sk_A )
    | ~ ( v2_pralg_1 @ sk_B )
    | ( v1_partfun1 @ ( k12_pralg_1 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v2_pralg_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_partfun1 @ ( k12_pralg_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['7','8','9','10','11'])).

thf(d13_pralg_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A )
        & ( v1_funct_1 @ B )
        & ( v1_partfun1 @ B @ A )
        & ( v2_pralg_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v4_relat_1 @ C @ A )
            & ( v1_funct_1 @ C )
            & ( v1_partfun1 @ C @ A ) )
         => ( ( C
              = ( k12_pralg_1 @ A @ B ) )
          <=> ! [D: $i] :
                ~ ( ( r2_hidden @ D @ A )
                  & ! [E: $i] :
                      ( ( l1_struct_0 @ E )
                     => ~ ( ( E
                            = ( k1_funct_1 @ B @ D ) )
                          & ( ( k1_funct_1 @ C @ D )
                            = ( u1_struct_0 @ E ) ) ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v4_relat_1 @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_partfun1 @ X0 @ X1 )
      | ( X0
       != ( k12_pralg_1 @ X1 @ X3 ) )
      | ~ ( r2_hidden @ X4 @ X1 )
      | ( ( k1_funct_1 @ X0 @ X4 )
        = ( u1_struct_0 @ ( sk_E @ X4 @ X0 @ X3 ) ) )
      | ~ ( v2_pralg_1 @ X3 )
      | ~ ( v1_partfun1 @ X3 @ X1 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v4_relat_1 @ X3 @ X1 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d13_pralg_1])).

thf('14',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v4_relat_1 @ X3 @ X1 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_partfun1 @ X3 @ X1 )
      | ~ ( v2_pralg_1 @ X3 )
      | ( ( k1_funct_1 @ ( k12_pralg_1 @ X1 @ X3 ) @ X4 )
        = ( u1_struct_0 @ ( sk_E @ X4 @ ( k12_pralg_1 @ X1 @ X3 ) @ X3 ) ) )
      | ~ ( r2_hidden @ X4 @ X1 )
      | ~ ( v1_partfun1 @ ( k12_pralg_1 @ X1 @ X3 ) @ X1 )
      | ~ ( v1_funct_1 @ ( k12_pralg_1 @ X1 @ X3 ) )
      | ~ ( v4_relat_1 @ ( k12_pralg_1 @ X1 @ X3 ) @ X1 )
      | ~ ( v1_relat_1 @ ( k12_pralg_1 @ X1 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k12_pralg_1 @ sk_A @ sk_B ) )
      | ~ ( v4_relat_1 @ ( k12_pralg_1 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( v1_funct_1 @ ( k12_pralg_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( ( k1_funct_1 @ ( k12_pralg_1 @ sk_A @ sk_B ) @ X0 )
        = ( u1_struct_0 @ ( sk_E @ X0 @ ( k12_pralg_1 @ sk_A @ sk_B ) @ sk_B ) ) )
      | ~ ( v2_pralg_1 @ sk_B )
      | ~ ( v1_partfun1 @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v4_relat_1 @ sk_B @ sk_A )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v1_relat_1 @ ( k12_pralg_1 @ X5 @ X6 ) )
      | ~ ( v2_pralg_1 @ X6 )
      | ~ ( v1_partfun1 @ X6 @ X5 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v4_relat_1 @ X6 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k12_pralg_1])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v4_relat_1 @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_pralg_1 @ sk_B )
    | ( v1_relat_1 @ ( k12_pralg_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v4_relat_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v2_pralg_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_relat_1 @ ( k12_pralg_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['18','19','20','21','22'])).

thf('24',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v4_relat_1 @ ( k12_pralg_1 @ X5 @ X6 ) @ X5 )
      | ~ ( v2_pralg_1 @ X6 )
      | ~ ( v1_partfun1 @ X6 @ X5 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v4_relat_1 @ X6 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k12_pralg_1])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v4_relat_1 @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_pralg_1 @ sk_B )
    | ( v4_relat_1 @ ( k12_pralg_1 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v4_relat_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v2_pralg_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v4_relat_1 @ ( k12_pralg_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['26','27','28','29','30'])).

thf('32',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v1_funct_1 @ ( k12_pralg_1 @ X5 @ X6 ) )
      | ~ ( v2_pralg_1 @ X6 )
      | ~ ( v1_partfun1 @ X6 @ X5 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v4_relat_1 @ X6 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k12_pralg_1])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v4_relat_1 @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_pralg_1 @ sk_B )
    | ( v1_funct_1 @ ( k12_pralg_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v4_relat_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v2_pralg_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_1 @ ( k12_pralg_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['34','35','36','37','38'])).

thf('40',plain,(
    v2_pralg_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v4_relat_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( ( k1_funct_1 @ ( k12_pralg_1 @ sk_A @ sk_B ) @ X0 )
        = ( u1_struct_0 @ ( sk_E @ X0 @ ( k12_pralg_1 @ sk_A @ sk_B ) @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['15','23','31','39','40','41','42','43','44'])).

thf('46',plain,
    ( ( k1_funct_1 @ ( k12_pralg_1 @ sk_A @ sk_B ) @ sk_C )
    = ( u1_struct_0 @ ( sk_E @ sk_C @ ( k12_pralg_1 @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','45'])).

thf('47',plain,(
    r2_hidden @ sk_C @ sk_A ),
    inference(clc,[status(thm)],['2','3'])).

thf('48',plain,(
    v1_partfun1 @ ( k12_pralg_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['7','8','9','10','11'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v4_relat_1 @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_partfun1 @ X0 @ X1 )
      | ( X0
       != ( k12_pralg_1 @ X1 @ X3 ) )
      | ~ ( r2_hidden @ X4 @ X1 )
      | ( ( sk_E @ X4 @ X0 @ X3 )
        = ( k1_funct_1 @ X3 @ X4 ) )
      | ~ ( v2_pralg_1 @ X3 )
      | ~ ( v1_partfun1 @ X3 @ X1 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v4_relat_1 @ X3 @ X1 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d13_pralg_1])).

thf('50',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v4_relat_1 @ X3 @ X1 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_partfun1 @ X3 @ X1 )
      | ~ ( v2_pralg_1 @ X3 )
      | ( ( sk_E @ X4 @ ( k12_pralg_1 @ X1 @ X3 ) @ X3 )
        = ( k1_funct_1 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ X4 @ X1 )
      | ~ ( v1_partfun1 @ ( k12_pralg_1 @ X1 @ X3 ) @ X1 )
      | ~ ( v1_funct_1 @ ( k12_pralg_1 @ X1 @ X3 ) )
      | ~ ( v4_relat_1 @ ( k12_pralg_1 @ X1 @ X3 ) @ X1 )
      | ~ ( v1_relat_1 @ ( k12_pralg_1 @ X1 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k12_pralg_1 @ sk_A @ sk_B ) )
      | ~ ( v4_relat_1 @ ( k12_pralg_1 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( v1_funct_1 @ ( k12_pralg_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( ( sk_E @ X0 @ ( k12_pralg_1 @ sk_A @ sk_B ) @ sk_B )
        = ( k1_funct_1 @ sk_B @ X0 ) )
      | ~ ( v2_pralg_1 @ sk_B )
      | ~ ( v1_partfun1 @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v4_relat_1 @ sk_B @ sk_A )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,(
    v1_relat_1 @ ( k12_pralg_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['18','19','20','21','22'])).

thf('53',plain,(
    v4_relat_1 @ ( k12_pralg_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['26','27','28','29','30'])).

thf('54',plain,(
    v1_funct_1 @ ( k12_pralg_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['34','35','36','37','38'])).

thf('55',plain,(
    v2_pralg_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v4_relat_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( ( sk_E @ X0 @ ( k12_pralg_1 @ sk_A @ sk_B ) @ sk_B )
        = ( k1_funct_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['51','52','53','54','55','56','57','58','59'])).

thf('61',plain,
    ( ( sk_E @ sk_C @ ( k12_pralg_1 @ sk_A @ sk_B ) @ sk_B )
    = ( k1_funct_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['47','60'])).

thf('62',plain,
    ( ( k1_funct_1 @ ( k12_pralg_1 @ sk_A @ sk_B ) @ sk_C )
    = ( u1_struct_0 @ ( k1_funct_1 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['46','61'])).

thf('63',plain,(
    ( k1_funct_1 @ ( k12_pralg_1 @ sk_A @ sk_B ) @ sk_C )
 != ( u1_struct_0 @ ( k10_pralg_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k10_pralg_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A )
        & ( v1_funct_1 @ B )
        & ( v1_partfun1 @ B @ A )
        & ( v2_pralg_1 @ B )
        & ( m1_subset_1 @ C @ A ) )
     => ( ( k10_pralg_1 @ A @ B @ C )
        = ( k1_funct_1 @ B @ C ) ) ) )).

thf('66',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v2_pralg_1 @ X7 )
      | ~ ( v1_partfun1 @ X7 @ X8 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v4_relat_1 @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X7 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ X8 )
      | ( ( k10_pralg_1 @ X8 @ X7 @ X9 )
        = ( k1_funct_1 @ X7 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k10_pralg_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( ( k10_pralg_1 @ sk_A @ sk_B @ X0 )
        = ( k1_funct_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v4_relat_1 @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_pralg_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v4_relat_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v2_pralg_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( ( k10_pralg_1 @ sk_A @ sk_B @ X0 )
        = ( k1_funct_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['67','68','69','70','71'])).

thf('73',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k10_pralg_1 @ sk_A @ sk_B @ X0 )
        = ( k1_funct_1 @ sk_B @ X0 ) ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k10_pralg_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_funct_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['64','74'])).

thf('76',plain,(
    ( k1_funct_1 @ ( k12_pralg_1 @ sk_A @ sk_B ) @ sk_C )
 != ( u1_struct_0 @ ( k1_funct_1 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['63','75'])).

thf('77',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['62','76'])).


%------------------------------------------------------------------------------
