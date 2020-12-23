%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ktYE0cOehY

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 264 expanded)
%              Number of leaves         :   22 (  92 expanded)
%              Depth                    :    9
%              Number of atoms          :  846 (4716 expanded)
%              Number of equality atoms :   26 ( 151 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_pralg_1_type,type,(
    v2_pralg_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k10_pralg_1_type,type,(
    k10_pralg_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k12_pralg_1_type,type,(
    k12_pralg_1: $i > $i > $i )).

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

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

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
    ! [X8: $i,X9: $i] :
      ( ( v1_partfun1 @ ( k12_pralg_1 @ X8 @ X9 ) @ X8 )
      | ~ ( v2_pralg_1 @ X9 )
      | ~ ( v1_partfun1 @ X9 @ X8 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v4_relat_1 @ X9 @ X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
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
    ! [X3: $i,X4: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v4_relat_1 @ X3 @ X4 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_partfun1 @ X3 @ X4 )
      | ( X3
       != ( k12_pralg_1 @ X4 @ X6 ) )
      | ~ ( r2_hidden @ X7 @ X4 )
      | ( ( k1_funct_1 @ X3 @ X7 )
        = ( u1_struct_0 @ ( sk_E @ X7 @ X3 @ X6 ) ) )
      | ~ ( v2_pralg_1 @ X6 )
      | ~ ( v1_partfun1 @ X6 @ X4 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v4_relat_1 @ X6 @ X4 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d13_pralg_1])).

thf('14',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v4_relat_1 @ X6 @ X4 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_partfun1 @ X6 @ X4 )
      | ~ ( v2_pralg_1 @ X6 )
      | ( ( k1_funct_1 @ ( k12_pralg_1 @ X4 @ X6 ) @ X7 )
        = ( u1_struct_0 @ ( sk_E @ X7 @ ( k12_pralg_1 @ X4 @ X6 ) @ X6 ) ) )
      | ~ ( r2_hidden @ X7 @ X4 )
      | ~ ( v1_partfun1 @ ( k12_pralg_1 @ X4 @ X6 ) @ X4 )
      | ~ ( v1_funct_1 @ ( k12_pralg_1 @ X4 @ X6 ) )
      | ~ ( v4_relat_1 @ ( k12_pralg_1 @ X4 @ X6 ) @ X4 )
      | ~ ( v1_relat_1 @ ( k12_pralg_1 @ X4 @ X6 ) ) ) ),
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
    ! [X8: $i,X9: $i] :
      ( ( v1_relat_1 @ ( k12_pralg_1 @ X8 @ X9 ) )
      | ~ ( v2_pralg_1 @ X9 )
      | ~ ( v1_partfun1 @ X9 @ X8 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v4_relat_1 @ X9 @ X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
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
    ! [X8: $i,X9: $i] :
      ( ( v4_relat_1 @ ( k12_pralg_1 @ X8 @ X9 ) @ X8 )
      | ~ ( v2_pralg_1 @ X9 )
      | ~ ( v1_partfun1 @ X9 @ X8 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v4_relat_1 @ X9 @ X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
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
    ! [X8: $i,X9: $i] :
      ( ( v1_funct_1 @ ( k12_pralg_1 @ X8 @ X9 ) )
      | ~ ( v2_pralg_1 @ X9 )
      | ~ ( v1_partfun1 @ X9 @ X8 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v4_relat_1 @ X9 @ X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
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
    ! [X3: $i,X4: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v4_relat_1 @ X3 @ X4 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_partfun1 @ X3 @ X4 )
      | ( X3
       != ( k12_pralg_1 @ X4 @ X6 ) )
      | ~ ( r2_hidden @ X7 @ X4 )
      | ( ( sk_E @ X7 @ X3 @ X6 )
        = ( k1_funct_1 @ X6 @ X7 ) )
      | ~ ( v2_pralg_1 @ X6 )
      | ~ ( v1_partfun1 @ X6 @ X4 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v4_relat_1 @ X6 @ X4 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d13_pralg_1])).

thf('50',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v4_relat_1 @ X6 @ X4 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_partfun1 @ X6 @ X4 )
      | ~ ( v2_pralg_1 @ X6 )
      | ( ( sk_E @ X7 @ ( k12_pralg_1 @ X4 @ X6 ) @ X6 )
        = ( k1_funct_1 @ X6 @ X7 ) )
      | ~ ( r2_hidden @ X7 @ X4 )
      | ~ ( v1_partfun1 @ ( k12_pralg_1 @ X4 @ X6 ) @ X4 )
      | ~ ( v1_funct_1 @ ( k12_pralg_1 @ X4 @ X6 ) )
      | ~ ( v4_relat_1 @ ( k12_pralg_1 @ X4 @ X6 ) @ X4 )
      | ~ ( v1_relat_1 @ ( k12_pralg_1 @ X4 @ X6 ) ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v2_pralg_1 @ X10 )
      | ~ ( v1_partfun1 @ X10 @ X11 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v4_relat_1 @ X10 @ X11 )
      | ~ ( v1_relat_1 @ X10 )
      | ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ X11 )
      | ( ( k10_pralg_1 @ X11 @ X10 @ X12 )
        = ( k1_funct_1 @ X10 @ X12 ) ) ) ),
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
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ktYE0cOehY
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:07:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 53 iterations in 0.033s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.50  thf(v2_pralg_1_type, type, v2_pralg_1: $i > $o).
% 0.21/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.50  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.21/0.50  thf(k10_pralg_1_type, type, k10_pralg_1: $i > $i > $i > $i).
% 0.21/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.50  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.21/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(k12_pralg_1_type, type, k12_pralg_1: $i > $i > $i).
% 0.21/0.50  thf(t9_yellow_6, conjecture,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) & 
% 0.21/0.50             ( v1_funct_1 @ B ) & ( v1_partfun1 @ B @ A ) & ( v2_pralg_1 @ B ) ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( m1_subset_1 @ C @ A ) =>
% 0.21/0.50               ( ( k1_funct_1 @ ( k12_pralg_1 @ A @ B ) @ C ) =
% 0.21/0.50                 ( u1_struct_0 @ ( k10_pralg_1 @ A @ B @ C ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i]:
% 0.21/0.50        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.50          ( ![B:$i]:
% 0.21/0.50            ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) & 
% 0.21/0.50                ( v1_funct_1 @ B ) & ( v1_partfun1 @ B @ A ) & 
% 0.21/0.50                ( v2_pralg_1 @ B ) ) =>
% 0.21/0.50              ( ![C:$i]:
% 0.21/0.50                ( ( m1_subset_1 @ C @ A ) =>
% 0.21/0.50                  ( ( k1_funct_1 @ ( k12_pralg_1 @ A @ B ) @ C ) =
% 0.21/0.50                    ( u1_struct_0 @ ( k10_pralg_1 @ A @ B @ C ) ) ) ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t9_yellow_6])).
% 0.21/0.50  thf('0', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(d2_subset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( v1_xboole_0 @ A ) =>
% 0.21/0.50         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.21/0.50       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.50         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X0 @ X1)
% 0.21/0.50          | (r2_hidden @ X0 @ X1)
% 0.21/0.50          | (v1_xboole_0 @ X1))),
% 0.21/0.50      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.50  thf('2', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_C @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.50  thf('3', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('4', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.21/0.50      inference('clc', [status(thm)], ['2', '3'])).
% 0.21/0.50  thf('5', plain, ((v4_relat_1 @ sk_B @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(dt_k12_pralg_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) & 
% 0.21/0.50         ( v1_partfun1 @ B @ A ) & ( v2_pralg_1 @ B ) ) =>
% 0.21/0.50       ( ( v1_relat_1 @ ( k12_pralg_1 @ A @ B ) ) & 
% 0.21/0.50         ( v4_relat_1 @ ( k12_pralg_1 @ A @ B ) @ A ) & 
% 0.21/0.50         ( v1_funct_1 @ ( k12_pralg_1 @ A @ B ) ) & 
% 0.21/0.50         ( v1_partfun1 @ ( k12_pralg_1 @ A @ B ) @ A ) ) ))).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (![X8 : $i, X9 : $i]:
% 0.21/0.50         ((v1_partfun1 @ (k12_pralg_1 @ X8 @ X9) @ X8)
% 0.21/0.50          | ~ (v2_pralg_1 @ X9)
% 0.21/0.50          | ~ (v1_partfun1 @ X9 @ X8)
% 0.21/0.50          | ~ (v1_funct_1 @ X9)
% 0.21/0.50          | ~ (v4_relat_1 @ X9 @ X8)
% 0.21/0.50          | ~ (v1_relat_1 @ X9))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k12_pralg_1])).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.50        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.50        | ~ (v1_partfun1 @ sk_B @ sk_A)
% 0.21/0.50        | ~ (v2_pralg_1 @ sk_B)
% 0.21/0.50        | (v1_partfun1 @ (k12_pralg_1 @ sk_A @ sk_B) @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.50  thf('8', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('9', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('10', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('11', plain, ((v2_pralg_1 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('12', plain, ((v1_partfun1 @ (k12_pralg_1 @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.50      inference('demod', [status(thm)], ['7', '8', '9', '10', '11'])).
% 0.21/0.50  thf(d13_pralg_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) & 
% 0.21/0.50         ( v1_partfun1 @ B @ A ) & ( v2_pralg_1 @ B ) ) =>
% 0.21/0.50       ( ![C:$i]:
% 0.21/0.50         ( ( ( v1_relat_1 @ C ) & ( v4_relat_1 @ C @ A ) & 
% 0.21/0.50             ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 0.21/0.50           ( ( ( C ) = ( k12_pralg_1 @ A @ B ) ) <=>
% 0.21/0.50             ( ![D:$i]:
% 0.21/0.50               ( ~( ( r2_hidden @ D @ A ) & 
% 0.21/0.50                    ( ![E:$i]:
% 0.21/0.50                      ( ( l1_struct_0 @ E ) =>
% 0.21/0.50                        ( ~( ( ( E ) = ( k1_funct_1 @ B @ D ) ) & 
% 0.21/0.50                             ( ( k1_funct_1 @ C @ D ) = ( u1_struct_0 @ E ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      (![X3 : $i, X4 : $i, X6 : $i, X7 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ X3)
% 0.21/0.50          | ~ (v4_relat_1 @ X3 @ X4)
% 0.21/0.50          | ~ (v1_funct_1 @ X3)
% 0.21/0.50          | ~ (v1_partfun1 @ X3 @ X4)
% 0.21/0.50          | ((X3) != (k12_pralg_1 @ X4 @ X6))
% 0.21/0.50          | ~ (r2_hidden @ X7 @ X4)
% 0.21/0.50          | ((k1_funct_1 @ X3 @ X7) = (u1_struct_0 @ (sk_E @ X7 @ X3 @ X6)))
% 0.21/0.50          | ~ (v2_pralg_1 @ X6)
% 0.21/0.50          | ~ (v1_partfun1 @ X6 @ X4)
% 0.21/0.50          | ~ (v1_funct_1 @ X6)
% 0.21/0.50          | ~ (v4_relat_1 @ X6 @ X4)
% 0.21/0.50          | ~ (v1_relat_1 @ X6))),
% 0.21/0.50      inference('cnf', [status(esa)], [d13_pralg_1])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ X6)
% 0.21/0.50          | ~ (v4_relat_1 @ X6 @ X4)
% 0.21/0.50          | ~ (v1_funct_1 @ X6)
% 0.21/0.50          | ~ (v1_partfun1 @ X6 @ X4)
% 0.21/0.50          | ~ (v2_pralg_1 @ X6)
% 0.21/0.50          | ((k1_funct_1 @ (k12_pralg_1 @ X4 @ X6) @ X7)
% 0.21/0.50              = (u1_struct_0 @ (sk_E @ X7 @ (k12_pralg_1 @ X4 @ X6) @ X6)))
% 0.21/0.50          | ~ (r2_hidden @ X7 @ X4)
% 0.21/0.50          | ~ (v1_partfun1 @ (k12_pralg_1 @ X4 @ X6) @ X4)
% 0.21/0.50          | ~ (v1_funct_1 @ (k12_pralg_1 @ X4 @ X6))
% 0.21/0.50          | ~ (v4_relat_1 @ (k12_pralg_1 @ X4 @ X6) @ X4)
% 0.21/0.50          | ~ (v1_relat_1 @ (k12_pralg_1 @ X4 @ X6)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ (k12_pralg_1 @ sk_A @ sk_B))
% 0.21/0.50          | ~ (v4_relat_1 @ (k12_pralg_1 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.50          | ~ (v1_funct_1 @ (k12_pralg_1 @ sk_A @ sk_B))
% 0.21/0.50          | ~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.50          | ((k1_funct_1 @ (k12_pralg_1 @ sk_A @ sk_B) @ X0)
% 0.21/0.50              = (u1_struct_0 @ (sk_E @ X0 @ (k12_pralg_1 @ sk_A @ sk_B) @ sk_B)))
% 0.21/0.50          | ~ (v2_pralg_1 @ sk_B)
% 0.21/0.50          | ~ (v1_partfun1 @ sk_B @ sk_A)
% 0.21/0.50          | ~ (v1_funct_1 @ sk_B)
% 0.21/0.50          | ~ (v4_relat_1 @ sk_B @ sk_A)
% 0.21/0.50          | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['12', '14'])).
% 0.21/0.50  thf('16', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      (![X8 : $i, X9 : $i]:
% 0.21/0.50         ((v1_relat_1 @ (k12_pralg_1 @ X8 @ X9))
% 0.21/0.50          | ~ (v2_pralg_1 @ X9)
% 0.21/0.50          | ~ (v1_partfun1 @ X9 @ X8)
% 0.21/0.50          | ~ (v1_funct_1 @ X9)
% 0.21/0.50          | ~ (v4_relat_1 @ X9 @ X8)
% 0.21/0.50          | ~ (v1_relat_1 @ X9))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k12_pralg_1])).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.50        | ~ (v4_relat_1 @ sk_B @ sk_A)
% 0.21/0.50        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.50        | ~ (v2_pralg_1 @ sk_B)
% 0.21/0.50        | (v1_relat_1 @ (k12_pralg_1 @ sk_A @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.50  thf('19', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('20', plain, ((v4_relat_1 @ sk_B @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('21', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('22', plain, ((v2_pralg_1 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('23', plain, ((v1_relat_1 @ (k12_pralg_1 @ sk_A @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['18', '19', '20', '21', '22'])).
% 0.21/0.50  thf('24', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('25', plain,
% 0.21/0.50      (![X8 : $i, X9 : $i]:
% 0.21/0.50         ((v4_relat_1 @ (k12_pralg_1 @ X8 @ X9) @ X8)
% 0.21/0.50          | ~ (v2_pralg_1 @ X9)
% 0.21/0.50          | ~ (v1_partfun1 @ X9 @ X8)
% 0.21/0.50          | ~ (v1_funct_1 @ X9)
% 0.21/0.50          | ~ (v4_relat_1 @ X9 @ X8)
% 0.21/0.50          | ~ (v1_relat_1 @ X9))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k12_pralg_1])).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.50        | ~ (v4_relat_1 @ sk_B @ sk_A)
% 0.21/0.50        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.50        | ~ (v2_pralg_1 @ sk_B)
% 0.21/0.50        | (v4_relat_1 @ (k12_pralg_1 @ sk_A @ sk_B) @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.50  thf('27', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('28', plain, ((v4_relat_1 @ sk_B @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('29', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('30', plain, ((v2_pralg_1 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('31', plain, ((v4_relat_1 @ (k12_pralg_1 @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.50      inference('demod', [status(thm)], ['26', '27', '28', '29', '30'])).
% 0.21/0.50  thf('32', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('33', plain,
% 0.21/0.50      (![X8 : $i, X9 : $i]:
% 0.21/0.50         ((v1_funct_1 @ (k12_pralg_1 @ X8 @ X9))
% 0.21/0.50          | ~ (v2_pralg_1 @ X9)
% 0.21/0.50          | ~ (v1_partfun1 @ X9 @ X8)
% 0.21/0.50          | ~ (v1_funct_1 @ X9)
% 0.21/0.50          | ~ (v4_relat_1 @ X9 @ X8)
% 0.21/0.50          | ~ (v1_relat_1 @ X9))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k12_pralg_1])).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.50        | ~ (v4_relat_1 @ sk_B @ sk_A)
% 0.21/0.50        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.50        | ~ (v2_pralg_1 @ sk_B)
% 0.21/0.50        | (v1_funct_1 @ (k12_pralg_1 @ sk_A @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.50  thf('35', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('36', plain, ((v4_relat_1 @ sk_B @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('37', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('38', plain, ((v2_pralg_1 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('39', plain, ((v1_funct_1 @ (k12_pralg_1 @ sk_A @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['34', '35', '36', '37', '38'])).
% 0.21/0.50  thf('40', plain, ((v2_pralg_1 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('41', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('42', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('43', plain, ((v4_relat_1 @ sk_B @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('44', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('45', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.50          | ((k1_funct_1 @ (k12_pralg_1 @ sk_A @ sk_B) @ X0)
% 0.21/0.50              = (u1_struct_0 @ (sk_E @ X0 @ (k12_pralg_1 @ sk_A @ sk_B) @ sk_B))))),
% 0.21/0.50      inference('demod', [status(thm)],
% 0.21/0.50                ['15', '23', '31', '39', '40', '41', '42', '43', '44'])).
% 0.21/0.50  thf('46', plain,
% 0.21/0.50      (((k1_funct_1 @ (k12_pralg_1 @ sk_A @ sk_B) @ sk_C)
% 0.21/0.50         = (u1_struct_0 @ (sk_E @ sk_C @ (k12_pralg_1 @ sk_A @ sk_B) @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['4', '45'])).
% 0.21/0.50  thf('47', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.21/0.50      inference('clc', [status(thm)], ['2', '3'])).
% 0.21/0.50  thf('48', plain, ((v1_partfun1 @ (k12_pralg_1 @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.50      inference('demod', [status(thm)], ['7', '8', '9', '10', '11'])).
% 0.21/0.50  thf('49', plain,
% 0.21/0.50      (![X3 : $i, X4 : $i, X6 : $i, X7 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ X3)
% 0.21/0.50          | ~ (v4_relat_1 @ X3 @ X4)
% 0.21/0.50          | ~ (v1_funct_1 @ X3)
% 0.21/0.50          | ~ (v1_partfun1 @ X3 @ X4)
% 0.21/0.50          | ((X3) != (k12_pralg_1 @ X4 @ X6))
% 0.21/0.50          | ~ (r2_hidden @ X7 @ X4)
% 0.21/0.50          | ((sk_E @ X7 @ X3 @ X6) = (k1_funct_1 @ X6 @ X7))
% 0.21/0.50          | ~ (v2_pralg_1 @ X6)
% 0.21/0.50          | ~ (v1_partfun1 @ X6 @ X4)
% 0.21/0.50          | ~ (v1_funct_1 @ X6)
% 0.21/0.50          | ~ (v4_relat_1 @ X6 @ X4)
% 0.21/0.50          | ~ (v1_relat_1 @ X6))),
% 0.21/0.50      inference('cnf', [status(esa)], [d13_pralg_1])).
% 0.21/0.50  thf('50', plain,
% 0.21/0.50      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ X6)
% 0.21/0.50          | ~ (v4_relat_1 @ X6 @ X4)
% 0.21/0.50          | ~ (v1_funct_1 @ X6)
% 0.21/0.50          | ~ (v1_partfun1 @ X6 @ X4)
% 0.21/0.50          | ~ (v2_pralg_1 @ X6)
% 0.21/0.50          | ((sk_E @ X7 @ (k12_pralg_1 @ X4 @ X6) @ X6)
% 0.21/0.50              = (k1_funct_1 @ X6 @ X7))
% 0.21/0.50          | ~ (r2_hidden @ X7 @ X4)
% 0.21/0.50          | ~ (v1_partfun1 @ (k12_pralg_1 @ X4 @ X6) @ X4)
% 0.21/0.50          | ~ (v1_funct_1 @ (k12_pralg_1 @ X4 @ X6))
% 0.21/0.50          | ~ (v4_relat_1 @ (k12_pralg_1 @ X4 @ X6) @ X4)
% 0.21/0.50          | ~ (v1_relat_1 @ (k12_pralg_1 @ X4 @ X6)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['49'])).
% 0.21/0.50  thf('51', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ (k12_pralg_1 @ sk_A @ sk_B))
% 0.21/0.50          | ~ (v4_relat_1 @ (k12_pralg_1 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.50          | ~ (v1_funct_1 @ (k12_pralg_1 @ sk_A @ sk_B))
% 0.21/0.50          | ~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.50          | ((sk_E @ X0 @ (k12_pralg_1 @ sk_A @ sk_B) @ sk_B)
% 0.21/0.50              = (k1_funct_1 @ sk_B @ X0))
% 0.21/0.50          | ~ (v2_pralg_1 @ sk_B)
% 0.21/0.50          | ~ (v1_partfun1 @ sk_B @ sk_A)
% 0.21/0.50          | ~ (v1_funct_1 @ sk_B)
% 0.21/0.50          | ~ (v4_relat_1 @ sk_B @ sk_A)
% 0.21/0.50          | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['48', '50'])).
% 0.21/0.50  thf('52', plain, ((v1_relat_1 @ (k12_pralg_1 @ sk_A @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['18', '19', '20', '21', '22'])).
% 0.21/0.50  thf('53', plain, ((v4_relat_1 @ (k12_pralg_1 @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.50      inference('demod', [status(thm)], ['26', '27', '28', '29', '30'])).
% 0.21/0.50  thf('54', plain, ((v1_funct_1 @ (k12_pralg_1 @ sk_A @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['34', '35', '36', '37', '38'])).
% 0.21/0.50  thf('55', plain, ((v2_pralg_1 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('56', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('57', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('58', plain, ((v4_relat_1 @ sk_B @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('59', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('60', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.50          | ((sk_E @ X0 @ (k12_pralg_1 @ sk_A @ sk_B) @ sk_B)
% 0.21/0.50              = (k1_funct_1 @ sk_B @ X0)))),
% 0.21/0.50      inference('demod', [status(thm)],
% 0.21/0.50                ['51', '52', '53', '54', '55', '56', '57', '58', '59'])).
% 0.21/0.50  thf('61', plain,
% 0.21/0.50      (((sk_E @ sk_C @ (k12_pralg_1 @ sk_A @ sk_B) @ sk_B)
% 0.21/0.50         = (k1_funct_1 @ sk_B @ sk_C))),
% 0.21/0.50      inference('sup-', [status(thm)], ['47', '60'])).
% 0.21/0.50  thf('62', plain,
% 0.21/0.50      (((k1_funct_1 @ (k12_pralg_1 @ sk_A @ sk_B) @ sk_C)
% 0.21/0.50         = (u1_struct_0 @ (k1_funct_1 @ sk_B @ sk_C)))),
% 0.21/0.50      inference('demod', [status(thm)], ['46', '61'])).
% 0.21/0.50  thf('63', plain,
% 0.21/0.50      (((k1_funct_1 @ (k12_pralg_1 @ sk_A @ sk_B) @ sk_C)
% 0.21/0.50         != (u1_struct_0 @ (k10_pralg_1 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('64', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('65', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(redefinition_k10_pralg_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ B ) & 
% 0.21/0.50         ( v4_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) & 
% 0.21/0.50         ( v1_partfun1 @ B @ A ) & ( v2_pralg_1 @ B ) & ( m1_subset_1 @ C @ A ) ) =>
% 0.21/0.50       ( ( k10_pralg_1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ))).
% 0.21/0.50  thf('66', plain,
% 0.21/0.50      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.50         (~ (v2_pralg_1 @ X10)
% 0.21/0.50          | ~ (v1_partfun1 @ X10 @ X11)
% 0.21/0.50          | ~ (v1_funct_1 @ X10)
% 0.21/0.50          | ~ (v4_relat_1 @ X10 @ X11)
% 0.21/0.50          | ~ (v1_relat_1 @ X10)
% 0.21/0.50          | (v1_xboole_0 @ X11)
% 0.21/0.50          | ~ (m1_subset_1 @ X12 @ X11)
% 0.21/0.50          | ((k10_pralg_1 @ X11 @ X10 @ X12) = (k1_funct_1 @ X10 @ X12)))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_k10_pralg_1])).
% 0.21/0.50  thf('67', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((k10_pralg_1 @ sk_A @ sk_B @ X0) = (k1_funct_1 @ sk_B @ X0))
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.50          | (v1_xboole_0 @ sk_A)
% 0.21/0.50          | ~ (v1_relat_1 @ sk_B)
% 0.21/0.50          | ~ (v4_relat_1 @ sk_B @ sk_A)
% 0.21/0.50          | ~ (v1_funct_1 @ sk_B)
% 0.21/0.50          | ~ (v2_pralg_1 @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['65', '66'])).
% 0.21/0.50  thf('68', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('69', plain, ((v4_relat_1 @ sk_B @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('70', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('71', plain, ((v2_pralg_1 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('72', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((k10_pralg_1 @ sk_A @ sk_B @ X0) = (k1_funct_1 @ sk_B @ X0))
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.50          | (v1_xboole_0 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['67', '68', '69', '70', '71'])).
% 0.21/0.50  thf('73', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('74', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.50          | ((k10_pralg_1 @ sk_A @ sk_B @ X0) = (k1_funct_1 @ sk_B @ X0)))),
% 0.21/0.50      inference('clc', [status(thm)], ['72', '73'])).
% 0.21/0.50  thf('75', plain,
% 0.21/0.50      (((k10_pralg_1 @ sk_A @ sk_B @ sk_C) = (k1_funct_1 @ sk_B @ sk_C))),
% 0.21/0.50      inference('sup-', [status(thm)], ['64', '74'])).
% 0.21/0.50  thf('76', plain,
% 0.21/0.50      (((k1_funct_1 @ (k12_pralg_1 @ sk_A @ sk_B) @ sk_C)
% 0.21/0.50         != (u1_struct_0 @ (k1_funct_1 @ sk_B @ sk_C)))),
% 0.21/0.50      inference('demod', [status(thm)], ['63', '75'])).
% 0.21/0.50  thf('77', plain, ($false),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['62', '76'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
