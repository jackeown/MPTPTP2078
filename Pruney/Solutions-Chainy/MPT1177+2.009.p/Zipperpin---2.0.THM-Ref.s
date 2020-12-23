%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QEtBXlp7ND

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:13 EST 2020

% Result     : Theorem 1.20s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 769 expanded)
%              Number of leaves         :   36 ( 232 expanded)
%              Depth                    :   23
%              Number of atoms          : 1245 (12937 expanded)
%              Number of equality atoms :   35 (  92 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_orders_1_type,type,(
    m1_orders_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m2_orders_2_type,type,(
    m2_orders_2: $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(m1_orders_2_type,type,(
    m1_orders_2: $i > $i > $i > $o )).

thf(k1_orders_1_type,type,(
    k1_orders_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(t84_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m2_orders_2 @ C @ A @ B )
             => ! [D: $i] :
                  ( ( m2_orders_2 @ D @ A @ B )
                 => ( ( r2_xboole_0 @ C @ D )
                  <=> ( m1_orders_2 @ C @ A @ D ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m2_orders_2 @ C @ A @ B )
               => ! [D: $i] :
                    ( ( m2_orders_2 @ D @ A @ B )
                   => ( ( r2_xboole_0 @ C @ D )
                    <=> ( m1_orders_2 @ C @ A @ D ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t84_orders_2])).

thf('0',plain,
    ( ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D_1 )
    | ( r2_xboole_0 @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_xboole_0 @ sk_C_1 @ sk_D_1 )
   <= ( r2_xboole_0 @ sk_C_1 @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D_1 )
    | ~ ( r2_xboole_0 @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D_1 )
    | ~ ( r2_xboole_0 @ sk_C_1 @ sk_D_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D_1 )
   <= ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('5',plain,(
    m2_orders_2 @ sk_D_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_orders_1 @ sk_B @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m2_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) )
     => ! [C: $i] :
          ( ( m2_orders_2 @ C @ A @ B )
         => ( ( v6_orders_2 @ C @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( l1_orders_2 @ X25 )
      | ~ ( v5_orders_2 @ X25 )
      | ~ ( v4_orders_2 @ X25 )
      | ~ ( v3_orders_2 @ X25 )
      | ( v2_struct_0 @ X25 )
      | ~ ( m1_orders_1 @ X26 @ ( k1_orders_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( m2_orders_2 @ X27 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_orders_2])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9','10','11','12'])).

thf('14',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','15'])).

thf(t67_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_orders_2 @ C @ A @ B )
             => ( r1_tarski @ C @ B ) ) ) ) )).

thf('17',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( r1_tarski @ X30 @ X28 )
      | ~ ( m1_orders_2 @ X30 @ X29 @ X28 )
      | ~ ( l1_orders_2 @ X29 )
      | ~ ( v5_orders_2 @ X29 )
      | ~ ( v4_orders_2 @ X29 )
      | ~ ( v3_orders_2 @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t67_orders_2])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_D_1 )
      | ( r1_tarski @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_D_1 )
      | ( r1_tarski @ X0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['18','19','20','21','22'])).

thf('24',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_D_1 )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_D_1 )
   <= ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['4','25'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('27',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r2_xboole_0 @ X10 @ X12 )
      | ( X10 = X12 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('28',plain,
    ( ( ( sk_C_1 = sk_D_1 )
      | ( r2_xboole_0 @ sk_C_1 @ sk_D_1 ) )
   <= ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( r2_xboole_0 @ sk_C_1 @ sk_D_1 )
   <= ~ ( r2_xboole_0 @ sk_C_1 @ sk_D_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('30',plain,
    ( ( sk_C_1 = sk_D_1 )
   <= ( ~ ( r2_xboole_0 @ sk_C_1 @ sk_D_1 )
      & ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D_1 )
   <= ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,
    ( ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_C_1 )
   <= ( ~ ( r2_xboole_0 @ sk_C_1 @ sk_D_1 )
      & ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    m2_orders_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('35',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t69_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ~ ( ( B != k1_xboole_0 )
                  & ( m1_orders_2 @ B @ A @ C )
                  & ( m1_orders_2 @ C @ A @ B ) ) ) ) ) )).

thf('37',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( X31 = k1_xboole_0 )
      | ~ ( m1_orders_2 @ X33 @ X32 @ X31 )
      | ~ ( m1_orders_2 @ X31 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_orders_2 @ X32 )
      | ~ ( v5_orders_2 @ X32 )
      | ~ ( v4_orders_2 @ X32 )
      | ~ ( v3_orders_2 @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t69_orders_2])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C_1 )
      | ( sk_C_1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_orders_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C_1 )
      | ( sk_C_1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['38','39','40','41','42'])).

thf('44',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ~ ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_C_1 )
    | ~ ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','43'])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ~ ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_C_1 ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( ~ ( r2_xboole_0 @ sk_C_1 @ sk_D_1 )
      & ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['32','47'])).

thf('49',plain,(
    m2_orders_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_orders_1 @ sk_B @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t79_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m2_orders_2 @ C @ A @ B )
             => ( r2_hidden @ ( k1_funct_1 @ B @ ( u1_struct_0 @ A ) ) @ C ) ) ) ) )).

thf('51',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_orders_1 @ X34 @ ( k1_orders_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X34 @ ( u1_struct_0 @ X35 ) ) @ X36 )
      | ~ ( m2_orders_2 @ X36 @ X35 @ X34 )
      | ~ ( l1_orders_2 @ X35 )
      | ~ ( v5_orders_2 @ X35 )
      | ~ ( v4_orders_2 @ X35 )
      | ~ ( v3_orders_2 @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t79_orders_2])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53','54','55','56'])).

thf('58',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ X0 )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['49','59'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('61',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('62',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X17 @ X18 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('67',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('68',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['65','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference(simplify,[status(thm)],['70'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('72',plain,(
    ! [X19: $i] :
      ( ( X19 = k1_xboole_0 )
      | ~ ( r1_tarski @ X19 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X17 @ X18 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('75',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r2_xboole_0 @ X10 @ X12 )
      | ( X10 = X12 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X1 )
        = X0 )
      | ( r2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( r2_xboole_0 @ k1_xboole_0 @ X0 )
      | ( ( k4_xboole_0 @ X0 @ X0 )
        = X0 ) ) ),
    inference('sup+',[status(thm)],['73','76'])).

thf('78',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    r2_xboole_0 @ k1_xboole_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['60','80'])).

thf('82',plain,
    ( ( r2_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
   <= ( ~ ( r2_xboole_0 @ sk_C_1 @ sk_D_1 )
      & ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['48','81'])).

thf('83',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10 != X11 )
      | ~ ( r2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('84',plain,(
    ! [X11: $i] :
      ~ ( r2_xboole_0 @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,
    ( ( r2_xboole_0 @ sk_C_1 @ sk_D_1 )
    | ~ ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['82','84'])).

thf('86',plain,
    ( ( r2_xboole_0 @ sk_C_1 @ sk_D_1 )
    | ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('87',plain,(
    r2_xboole_0 @ sk_C_1 @ sk_D_1 ),
    inference('sat_resolution*',[status(thm)],['3','85','86'])).

thf('88',plain,(
    r2_xboole_0 @ sk_C_1 @ sk_D_1 ),
    inference(simpl_trail,[status(thm)],['1','87'])).

thf('89',plain,(
    m2_orders_2 @ sk_D_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    m2_orders_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    m1_orders_1 @ sk_B @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t83_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m2_orders_2 @ C @ A @ B )
             => ! [D: $i] :
                  ( ( m2_orders_2 @ D @ A @ B )
                 => ( ( C != D )
                   => ( ( m1_orders_2 @ C @ A @ D )
                    <=> ~ ( m1_orders_2 @ D @ A @ C ) ) ) ) ) ) ) )).

thf('92',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_orders_1 @ X37 @ ( k1_orders_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( m2_orders_2 @ X39 @ X38 @ X37 )
      | ( m1_orders_2 @ X39 @ X38 @ X40 )
      | ( m1_orders_2 @ X40 @ X38 @ X39 )
      | ( X40 = X39 )
      | ~ ( m2_orders_2 @ X40 @ X38 @ X37 )
      | ~ ( l1_orders_2 @ X38 )
      | ~ ( v5_orders_2 @ X38 )
      | ~ ( v4_orders_2 @ X38 )
      | ~ ( v3_orders_2 @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t83_orders_2])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( X0 = X1 )
      | ( m1_orders_2 @ X0 @ sk_A @ X1 )
      | ( m1_orders_2 @ X1 @ sk_A @ X0 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( X0 = X1 )
      | ( m1_orders_2 @ X0 @ sk_A @ X1 )
      | ( m1_orders_2 @ X1 @ sk_A @ X0 )
      | ~ ( m2_orders_2 @ X1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['93','94','95','96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B )
      | ( m1_orders_2 @ X0 @ sk_A @ sk_C_1 )
      | ( m1_orders_2 @ sk_C_1 @ sk_A @ X0 )
      | ( sk_C_1 = X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['90','98'])).

thf('100',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_C_1 = sk_D_1 )
    | ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D_1 )
    | ( m1_orders_2 @ sk_D_1 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['89','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('102',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( r1_tarski @ X30 @ X28 )
      | ~ ( m1_orders_2 @ X30 @ X29 @ X28 )
      | ~ ( l1_orders_2 @ X29 )
      | ~ ( v5_orders_2 @ X29 )
      | ~ ( v4_orders_2 @ X29 )
      | ~ ( v3_orders_2 @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t67_orders_2])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C_1 )
      | ( r1_tarski @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C_1 )
      | ( r1_tarski @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['103','104','105','106','107'])).

thf('109',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ sk_C_1 )
      | ~ ( m1_orders_2 @ X0 @ sk_A @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D_1 )
    | ( sk_C_1 = sk_D_1 )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tarski @ sk_D_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['100','110'])).

thf('112',plain,
    ( ~ ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D_1 )
   <= ~ ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('113',plain,(
    ~ ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D_1 ) ),
    inference('sat_resolution*',[status(thm)],['3','85'])).

thf('114',plain,(
    ~ ( m1_orders_2 @ sk_C_1 @ sk_A @ sk_D_1 ) ),
    inference(simpl_trail,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( r1_tarski @ sk_D_1 @ sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( sk_C_1 = sk_D_1 ) ),
    inference('sup-',[status(thm)],['111','114'])).

thf('116',plain,
    ( ( r2_xboole_0 @ sk_C_1 @ sk_D_1 )
   <= ( r2_xboole_0 @ sk_C_1 @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('117',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( r2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('118',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_D_1 )
   <= ( r2_xboole_0 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('119',plain,(
    ! [X13: $i,X15: $i] :
      ( ( X13 = X15 )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('120',plain,
    ( ( ~ ( r1_tarski @ sk_D_1 @ sk_C_1 )
      | ( sk_D_1 = sk_C_1 ) )
   <= ( r2_xboole_0 @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    r2_xboole_0 @ sk_C_1 @ sk_D_1 ),
    inference('sat_resolution*',[status(thm)],['3','85','86'])).

thf('122',plain,
    ( ~ ( r1_tarski @ sk_D_1 @ sk_C_1 )
    | ( sk_D_1 = sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['120','121'])).

thf('123',plain,
    ( ( sk_C_1 = sk_D_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['115','122'])).

thf('124',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    sk_C_1 = sk_D_1 ),
    inference(clc,[status(thm)],['123','124'])).

thf('126',plain,(
    r2_xboole_0 @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['88','125'])).

thf('127',plain,(
    ! [X11: $i] :
      ~ ( r2_xboole_0 @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['83'])).

thf('128',plain,(
    $false ),
    inference('sup-',[status(thm)],['126','127'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QEtBXlp7ND
% 0.13/0.32  % Computer   : n012.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 18:48:37 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.32  % Running portfolio for 600 s
% 0.13/0.32  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.33  % Python version: Python 3.6.8
% 0.13/0.33  % Running in FO mode
% 1.20/1.40  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.20/1.40  % Solved by: fo/fo7.sh
% 1.20/1.40  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.20/1.40  % done 1750 iterations in 0.972s
% 1.20/1.40  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.20/1.40  % SZS output start Refutation
% 1.20/1.40  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 1.20/1.40  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.20/1.40  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.20/1.40  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.20/1.40  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.20/1.40  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.20/1.40  thf(m1_orders_1_type, type, m1_orders_1: $i > $i > $o).
% 1.20/1.40  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.20/1.40  thf(m2_orders_2_type, type, m2_orders_2: $i > $i > $i > $o).
% 1.20/1.40  thf(sk_D_1_type, type, sk_D_1: $i).
% 1.20/1.40  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.20/1.40  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 1.20/1.40  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 1.20/1.40  thf(m1_orders_2_type, type, m1_orders_2: $i > $i > $i > $o).
% 1.20/1.40  thf(k1_orders_1_type, type, k1_orders_1: $i > $i).
% 1.20/1.40  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.20/1.40  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 1.20/1.40  thf(sk_A_type, type, sk_A: $i).
% 1.20/1.40  thf(sk_B_type, type, sk_B: $i).
% 1.20/1.40  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 1.20/1.40  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.20/1.40  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.20/1.40  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.20/1.40  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 1.20/1.40  thf(t84_orders_2, conjecture,
% 1.20/1.40    (![A:$i]:
% 1.20/1.40     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.20/1.40         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.20/1.40       ( ![B:$i]:
% 1.20/1.40         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.20/1.40           ( ![C:$i]:
% 1.20/1.40             ( ( m2_orders_2 @ C @ A @ B ) =>
% 1.20/1.40               ( ![D:$i]:
% 1.20/1.40                 ( ( m2_orders_2 @ D @ A @ B ) =>
% 1.20/1.40                   ( ( r2_xboole_0 @ C @ D ) <=> ( m1_orders_2 @ C @ A @ D ) ) ) ) ) ) ) ) ))).
% 1.20/1.40  thf(zf_stmt_0, negated_conjecture,
% 1.20/1.40    (~( ![A:$i]:
% 1.20/1.40        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.20/1.40            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.20/1.40          ( ![B:$i]:
% 1.20/1.40            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.20/1.40              ( ![C:$i]:
% 1.20/1.40                ( ( m2_orders_2 @ C @ A @ B ) =>
% 1.20/1.40                  ( ![D:$i]:
% 1.20/1.40                    ( ( m2_orders_2 @ D @ A @ B ) =>
% 1.20/1.40                      ( ( r2_xboole_0 @ C @ D ) <=> ( m1_orders_2 @ C @ A @ D ) ) ) ) ) ) ) ) ) )),
% 1.20/1.40    inference('cnf.neg', [status(esa)], [t84_orders_2])).
% 1.20/1.40  thf('0', plain,
% 1.20/1.40      (((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D_1)
% 1.20/1.40        | (r2_xboole_0 @ sk_C_1 @ sk_D_1))),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('1', plain,
% 1.20/1.40      (((r2_xboole_0 @ sk_C_1 @ sk_D_1)) <= (((r2_xboole_0 @ sk_C_1 @ sk_D_1)))),
% 1.20/1.40      inference('split', [status(esa)], ['0'])).
% 1.20/1.40  thf('2', plain,
% 1.20/1.40      ((~ (m1_orders_2 @ sk_C_1 @ sk_A @ sk_D_1)
% 1.20/1.40        | ~ (r2_xboole_0 @ sk_C_1 @ sk_D_1))),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('3', plain,
% 1.20/1.40      (~ ((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D_1)) | 
% 1.20/1.40       ~ ((r2_xboole_0 @ sk_C_1 @ sk_D_1))),
% 1.20/1.40      inference('split', [status(esa)], ['2'])).
% 1.20/1.40  thf('4', plain,
% 1.20/1.40      (((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D_1))
% 1.20/1.40         <= (((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D_1)))),
% 1.20/1.40      inference('split', [status(esa)], ['0'])).
% 1.20/1.40  thf('5', plain, ((m2_orders_2 @ sk_D_1 @ sk_A @ sk_B)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('6', plain,
% 1.20/1.40      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf(dt_m2_orders_2, axiom,
% 1.20/1.40    (![A:$i,B:$i]:
% 1.20/1.40     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.20/1.40         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 1.20/1.40         ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.20/1.40       ( ![C:$i]:
% 1.20/1.40         ( ( m2_orders_2 @ C @ A @ B ) =>
% 1.20/1.40           ( ( v6_orders_2 @ C @ A ) & 
% 1.20/1.40             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 1.20/1.40  thf('7', plain,
% 1.20/1.40      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.20/1.40         (~ (l1_orders_2 @ X25)
% 1.20/1.40          | ~ (v5_orders_2 @ X25)
% 1.20/1.40          | ~ (v4_orders_2 @ X25)
% 1.20/1.40          | ~ (v3_orders_2 @ X25)
% 1.20/1.40          | (v2_struct_0 @ X25)
% 1.20/1.40          | ~ (m1_orders_1 @ X26 @ (k1_orders_1 @ (u1_struct_0 @ X25)))
% 1.20/1.40          | (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 1.20/1.40          | ~ (m2_orders_2 @ X27 @ X25 @ X26))),
% 1.20/1.40      inference('cnf', [status(esa)], [dt_m2_orders_2])).
% 1.20/1.40  thf('8', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 1.20/1.40          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.20/1.40          | (v2_struct_0 @ sk_A)
% 1.20/1.40          | ~ (v3_orders_2 @ sk_A)
% 1.20/1.40          | ~ (v4_orders_2 @ sk_A)
% 1.20/1.40          | ~ (v5_orders_2 @ sk_A)
% 1.20/1.40          | ~ (l1_orders_2 @ sk_A))),
% 1.20/1.40      inference('sup-', [status(thm)], ['6', '7'])).
% 1.20/1.40  thf('9', plain, ((v3_orders_2 @ sk_A)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('10', plain, ((v4_orders_2 @ sk_A)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('11', plain, ((v5_orders_2 @ sk_A)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('12', plain, ((l1_orders_2 @ sk_A)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('13', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 1.20/1.40          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.20/1.40          | (v2_struct_0 @ sk_A))),
% 1.20/1.40      inference('demod', [status(thm)], ['8', '9', '10', '11', '12'])).
% 1.20/1.40  thf('14', plain, (~ (v2_struct_0 @ sk_A)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('15', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.20/1.40          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))),
% 1.20/1.40      inference('clc', [status(thm)], ['13', '14'])).
% 1.20/1.40  thf('16', plain,
% 1.20/1.40      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.20/1.40      inference('sup-', [status(thm)], ['5', '15'])).
% 1.20/1.40  thf(t67_orders_2, axiom,
% 1.20/1.40    (![A:$i]:
% 1.20/1.40     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.20/1.40         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.20/1.40       ( ![B:$i]:
% 1.20/1.40         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.20/1.40           ( ![C:$i]: ( ( m1_orders_2 @ C @ A @ B ) => ( r1_tarski @ C @ B ) ) ) ) ) ))).
% 1.20/1.40  thf('17', plain,
% 1.20/1.40      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.20/1.40         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 1.20/1.40          | (r1_tarski @ X30 @ X28)
% 1.20/1.40          | ~ (m1_orders_2 @ X30 @ X29 @ X28)
% 1.20/1.40          | ~ (l1_orders_2 @ X29)
% 1.20/1.40          | ~ (v5_orders_2 @ X29)
% 1.20/1.40          | ~ (v4_orders_2 @ X29)
% 1.20/1.40          | ~ (v3_orders_2 @ X29)
% 1.20/1.40          | (v2_struct_0 @ X29))),
% 1.20/1.40      inference('cnf', [status(esa)], [t67_orders_2])).
% 1.20/1.40  thf('18', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         ((v2_struct_0 @ sk_A)
% 1.20/1.40          | ~ (v3_orders_2 @ sk_A)
% 1.20/1.40          | ~ (v4_orders_2 @ sk_A)
% 1.20/1.40          | ~ (v5_orders_2 @ sk_A)
% 1.20/1.40          | ~ (l1_orders_2 @ sk_A)
% 1.20/1.40          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D_1)
% 1.20/1.40          | (r1_tarski @ X0 @ sk_D_1))),
% 1.20/1.40      inference('sup-', [status(thm)], ['16', '17'])).
% 1.20/1.40  thf('19', plain, ((v3_orders_2 @ sk_A)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('20', plain, ((v4_orders_2 @ sk_A)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('21', plain, ((v5_orders_2 @ sk_A)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('22', plain, ((l1_orders_2 @ sk_A)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('23', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         ((v2_struct_0 @ sk_A)
% 1.20/1.40          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D_1)
% 1.20/1.40          | (r1_tarski @ X0 @ sk_D_1))),
% 1.20/1.40      inference('demod', [status(thm)], ['18', '19', '20', '21', '22'])).
% 1.20/1.40  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('25', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         ((r1_tarski @ X0 @ sk_D_1) | ~ (m1_orders_2 @ X0 @ sk_A @ sk_D_1))),
% 1.20/1.40      inference('clc', [status(thm)], ['23', '24'])).
% 1.20/1.40  thf('26', plain,
% 1.20/1.40      (((r1_tarski @ sk_C_1 @ sk_D_1))
% 1.20/1.40         <= (((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D_1)))),
% 1.20/1.40      inference('sup-', [status(thm)], ['4', '25'])).
% 1.20/1.40  thf(d8_xboole_0, axiom,
% 1.20/1.40    (![A:$i,B:$i]:
% 1.20/1.40     ( ( r2_xboole_0 @ A @ B ) <=>
% 1.20/1.40       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 1.20/1.40  thf('27', plain,
% 1.20/1.40      (![X10 : $i, X12 : $i]:
% 1.20/1.40         ((r2_xboole_0 @ X10 @ X12)
% 1.20/1.40          | ((X10) = (X12))
% 1.20/1.40          | ~ (r1_tarski @ X10 @ X12))),
% 1.20/1.40      inference('cnf', [status(esa)], [d8_xboole_0])).
% 1.20/1.40  thf('28', plain,
% 1.20/1.40      (((((sk_C_1) = (sk_D_1)) | (r2_xboole_0 @ sk_C_1 @ sk_D_1)))
% 1.20/1.40         <= (((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D_1)))),
% 1.20/1.40      inference('sup-', [status(thm)], ['26', '27'])).
% 1.20/1.40  thf('29', plain,
% 1.20/1.40      ((~ (r2_xboole_0 @ sk_C_1 @ sk_D_1))
% 1.20/1.40         <= (~ ((r2_xboole_0 @ sk_C_1 @ sk_D_1)))),
% 1.20/1.40      inference('split', [status(esa)], ['2'])).
% 1.20/1.40  thf('30', plain,
% 1.20/1.40      ((((sk_C_1) = (sk_D_1)))
% 1.20/1.40         <= (~ ((r2_xboole_0 @ sk_C_1 @ sk_D_1)) & 
% 1.20/1.40             ((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D_1)))),
% 1.20/1.40      inference('sup-', [status(thm)], ['28', '29'])).
% 1.20/1.40  thf('31', plain,
% 1.20/1.40      (((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D_1))
% 1.20/1.40         <= (((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D_1)))),
% 1.20/1.40      inference('split', [status(esa)], ['0'])).
% 1.20/1.40  thf('32', plain,
% 1.20/1.40      (((m1_orders_2 @ sk_C_1 @ sk_A @ sk_C_1))
% 1.20/1.40         <= (~ ((r2_xboole_0 @ sk_C_1 @ sk_D_1)) & 
% 1.20/1.40             ((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D_1)))),
% 1.20/1.40      inference('sup+', [status(thm)], ['30', '31'])).
% 1.20/1.40  thf('33', plain, ((m2_orders_2 @ sk_C_1 @ sk_A @ sk_B)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('34', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.20/1.40          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))),
% 1.20/1.40      inference('clc', [status(thm)], ['13', '14'])).
% 1.20/1.40  thf('35', plain,
% 1.20/1.40      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.20/1.40      inference('sup-', [status(thm)], ['33', '34'])).
% 1.20/1.40  thf('36', plain,
% 1.20/1.40      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.20/1.40      inference('sup-', [status(thm)], ['33', '34'])).
% 1.20/1.40  thf(t69_orders_2, axiom,
% 1.20/1.40    (![A:$i]:
% 1.20/1.40     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.20/1.40         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.20/1.40       ( ![B:$i]:
% 1.20/1.40         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.20/1.40           ( ![C:$i]:
% 1.20/1.40             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.20/1.40               ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.20/1.40                    ( m1_orders_2 @ B @ A @ C ) & ( m1_orders_2 @ C @ A @ B ) ) ) ) ) ) ) ))).
% 1.20/1.40  thf('37', plain,
% 1.20/1.40      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.20/1.40         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 1.20/1.40          | ((X31) = (k1_xboole_0))
% 1.20/1.40          | ~ (m1_orders_2 @ X33 @ X32 @ X31)
% 1.20/1.40          | ~ (m1_orders_2 @ X31 @ X32 @ X33)
% 1.20/1.40          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 1.20/1.40          | ~ (l1_orders_2 @ X32)
% 1.20/1.40          | ~ (v5_orders_2 @ X32)
% 1.20/1.40          | ~ (v4_orders_2 @ X32)
% 1.20/1.40          | ~ (v3_orders_2 @ X32)
% 1.20/1.40          | (v2_struct_0 @ X32))),
% 1.20/1.40      inference('cnf', [status(esa)], [t69_orders_2])).
% 1.20/1.40  thf('38', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         ((v2_struct_0 @ sk_A)
% 1.20/1.40          | ~ (v3_orders_2 @ sk_A)
% 1.20/1.40          | ~ (v4_orders_2 @ sk_A)
% 1.20/1.40          | ~ (v5_orders_2 @ sk_A)
% 1.20/1.40          | ~ (l1_orders_2 @ sk_A)
% 1.20/1.40          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.20/1.40          | ~ (m1_orders_2 @ sk_C_1 @ sk_A @ X0)
% 1.20/1.40          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C_1)
% 1.20/1.40          | ((sk_C_1) = (k1_xboole_0)))),
% 1.20/1.40      inference('sup-', [status(thm)], ['36', '37'])).
% 1.20/1.40  thf('39', plain, ((v3_orders_2 @ sk_A)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('40', plain, ((v4_orders_2 @ sk_A)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('41', plain, ((v5_orders_2 @ sk_A)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('42', plain, ((l1_orders_2 @ sk_A)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('43', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         ((v2_struct_0 @ sk_A)
% 1.20/1.40          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.20/1.40          | ~ (m1_orders_2 @ sk_C_1 @ sk_A @ X0)
% 1.20/1.40          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C_1)
% 1.20/1.40          | ((sk_C_1) = (k1_xboole_0)))),
% 1.20/1.40      inference('demod', [status(thm)], ['38', '39', '40', '41', '42'])).
% 1.20/1.40  thf('44', plain,
% 1.20/1.40      ((((sk_C_1) = (k1_xboole_0))
% 1.20/1.40        | ~ (m1_orders_2 @ sk_C_1 @ sk_A @ sk_C_1)
% 1.20/1.40        | ~ (m1_orders_2 @ sk_C_1 @ sk_A @ sk_C_1)
% 1.20/1.40        | (v2_struct_0 @ sk_A))),
% 1.20/1.40      inference('sup-', [status(thm)], ['35', '43'])).
% 1.20/1.40  thf('45', plain,
% 1.20/1.40      (((v2_struct_0 @ sk_A)
% 1.20/1.40        | ~ (m1_orders_2 @ sk_C_1 @ sk_A @ sk_C_1)
% 1.20/1.40        | ((sk_C_1) = (k1_xboole_0)))),
% 1.20/1.40      inference('simplify', [status(thm)], ['44'])).
% 1.20/1.40  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('47', plain,
% 1.20/1.40      ((((sk_C_1) = (k1_xboole_0)) | ~ (m1_orders_2 @ sk_C_1 @ sk_A @ sk_C_1))),
% 1.20/1.40      inference('clc', [status(thm)], ['45', '46'])).
% 1.20/1.40  thf('48', plain,
% 1.20/1.40      ((((sk_C_1) = (k1_xboole_0)))
% 1.20/1.40         <= (~ ((r2_xboole_0 @ sk_C_1 @ sk_D_1)) & 
% 1.20/1.40             ((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D_1)))),
% 1.20/1.40      inference('sup-', [status(thm)], ['32', '47'])).
% 1.20/1.40  thf('49', plain, ((m2_orders_2 @ sk_C_1 @ sk_A @ sk_B)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('50', plain,
% 1.20/1.40      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf(t79_orders_2, axiom,
% 1.20/1.40    (![A:$i]:
% 1.20/1.40     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.20/1.40         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.20/1.40       ( ![B:$i]:
% 1.20/1.40         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.20/1.40           ( ![C:$i]:
% 1.20/1.40             ( ( m2_orders_2 @ C @ A @ B ) =>
% 1.20/1.40               ( r2_hidden @ ( k1_funct_1 @ B @ ( u1_struct_0 @ A ) ) @ C ) ) ) ) ) ))).
% 1.20/1.40  thf('51', plain,
% 1.20/1.40      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.20/1.40         (~ (m1_orders_1 @ X34 @ (k1_orders_1 @ (u1_struct_0 @ X35)))
% 1.20/1.40          | (r2_hidden @ (k1_funct_1 @ X34 @ (u1_struct_0 @ X35)) @ X36)
% 1.20/1.40          | ~ (m2_orders_2 @ X36 @ X35 @ X34)
% 1.20/1.40          | ~ (l1_orders_2 @ X35)
% 1.20/1.40          | ~ (v5_orders_2 @ X35)
% 1.20/1.40          | ~ (v4_orders_2 @ X35)
% 1.20/1.40          | ~ (v3_orders_2 @ X35)
% 1.20/1.40          | (v2_struct_0 @ X35))),
% 1.20/1.40      inference('cnf', [status(esa)], [t79_orders_2])).
% 1.20/1.40  thf('52', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         ((v2_struct_0 @ sk_A)
% 1.20/1.40          | ~ (v3_orders_2 @ sk_A)
% 1.20/1.40          | ~ (v4_orders_2 @ sk_A)
% 1.20/1.40          | ~ (v5_orders_2 @ sk_A)
% 1.20/1.40          | ~ (l1_orders_2 @ sk_A)
% 1.20/1.40          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 1.20/1.40          | (r2_hidden @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ X0))),
% 1.20/1.40      inference('sup-', [status(thm)], ['50', '51'])).
% 1.20/1.40  thf('53', plain, ((v3_orders_2 @ sk_A)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('54', plain, ((v4_orders_2 @ sk_A)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('55', plain, ((v5_orders_2 @ sk_A)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('56', plain, ((l1_orders_2 @ sk_A)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('57', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         ((v2_struct_0 @ sk_A)
% 1.20/1.40          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 1.20/1.40          | (r2_hidden @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ X0))),
% 1.20/1.40      inference('demod', [status(thm)], ['52', '53', '54', '55', '56'])).
% 1.20/1.40  thf('58', plain, (~ (v2_struct_0 @ sk_A)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('59', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         ((r2_hidden @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ X0)
% 1.20/1.40          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B))),
% 1.20/1.40      inference('clc', [status(thm)], ['57', '58'])).
% 1.20/1.40  thf('60', plain,
% 1.20/1.40      ((r2_hidden @ (k1_funct_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_C_1)),
% 1.20/1.40      inference('sup-', [status(thm)], ['49', '59'])).
% 1.20/1.40  thf(d3_tarski, axiom,
% 1.20/1.40    (![A:$i,B:$i]:
% 1.20/1.40     ( ( r1_tarski @ A @ B ) <=>
% 1.20/1.40       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.20/1.40  thf('61', plain,
% 1.20/1.40      (![X1 : $i, X3 : $i]:
% 1.20/1.40         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.20/1.40      inference('cnf', [status(esa)], [d3_tarski])).
% 1.20/1.40  thf(t36_xboole_1, axiom,
% 1.20/1.40    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.20/1.40  thf('62', plain,
% 1.20/1.40      (![X17 : $i, X18 : $i]: (r1_tarski @ (k4_xboole_0 @ X17 @ X18) @ X17)),
% 1.20/1.40      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.20/1.40  thf('63', plain,
% 1.20/1.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.20/1.40         (~ (r2_hidden @ X0 @ X1)
% 1.20/1.40          | (r2_hidden @ X0 @ X2)
% 1.20/1.40          | ~ (r1_tarski @ X1 @ X2))),
% 1.20/1.40      inference('cnf', [status(esa)], [d3_tarski])).
% 1.20/1.40  thf('64', plain,
% 1.20/1.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.20/1.40         ((r2_hidden @ X2 @ X0) | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 1.20/1.40      inference('sup-', [status(thm)], ['62', '63'])).
% 1.20/1.40  thf('65', plain,
% 1.20/1.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.20/1.40         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 1.20/1.40          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 1.20/1.40      inference('sup-', [status(thm)], ['61', '64'])).
% 1.20/1.40  thf('66', plain,
% 1.20/1.40      (![X1 : $i, X3 : $i]:
% 1.20/1.40         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.20/1.40      inference('cnf', [status(esa)], [d3_tarski])).
% 1.20/1.40  thf(d5_xboole_0, axiom,
% 1.20/1.40    (![A:$i,B:$i,C:$i]:
% 1.20/1.40     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.20/1.40       ( ![D:$i]:
% 1.20/1.40         ( ( r2_hidden @ D @ C ) <=>
% 1.20/1.40           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.20/1.40  thf('67', plain,
% 1.20/1.40      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 1.20/1.40         (~ (r2_hidden @ X8 @ X7)
% 1.20/1.40          | ~ (r2_hidden @ X8 @ X6)
% 1.20/1.40          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 1.20/1.40      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.20/1.40  thf('68', plain,
% 1.20/1.40      (![X5 : $i, X6 : $i, X8 : $i]:
% 1.20/1.40         (~ (r2_hidden @ X8 @ X6)
% 1.20/1.40          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 1.20/1.40      inference('simplify', [status(thm)], ['67'])).
% 1.20/1.40  thf('69', plain,
% 1.20/1.40      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.20/1.40         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 1.20/1.40          | ~ (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 1.20/1.40      inference('sup-', [status(thm)], ['66', '68'])).
% 1.20/1.40  thf('70', plain,
% 1.20/1.40      (![X0 : $i, X1 : $i]:
% 1.20/1.40         ((r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 1.20/1.40          | (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X1))),
% 1.20/1.40      inference('sup-', [status(thm)], ['65', '69'])).
% 1.20/1.40  thf('71', plain,
% 1.20/1.40      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X1)),
% 1.20/1.40      inference('simplify', [status(thm)], ['70'])).
% 1.20/1.40  thf(t3_xboole_1, axiom,
% 1.20/1.40    (![A:$i]:
% 1.20/1.40     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.20/1.40  thf('72', plain,
% 1.20/1.40      (![X19 : $i]:
% 1.20/1.40         (((X19) = (k1_xboole_0)) | ~ (r1_tarski @ X19 @ k1_xboole_0))),
% 1.20/1.40      inference('cnf', [status(esa)], [t3_xboole_1])).
% 1.20/1.40  thf('73', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.20/1.40      inference('sup-', [status(thm)], ['71', '72'])).
% 1.20/1.40  thf('74', plain,
% 1.20/1.40      (![X17 : $i, X18 : $i]: (r1_tarski @ (k4_xboole_0 @ X17 @ X18) @ X17)),
% 1.20/1.40      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.20/1.40  thf('75', plain,
% 1.20/1.40      (![X10 : $i, X12 : $i]:
% 1.20/1.40         ((r2_xboole_0 @ X10 @ X12)
% 1.20/1.40          | ((X10) = (X12))
% 1.20/1.40          | ~ (r1_tarski @ X10 @ X12))),
% 1.20/1.40      inference('cnf', [status(esa)], [d8_xboole_0])).
% 1.20/1.40  thf('76', plain,
% 1.20/1.40      (![X0 : $i, X1 : $i]:
% 1.20/1.40         (((k4_xboole_0 @ X0 @ X1) = (X0))
% 1.20/1.40          | (r2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 1.20/1.40      inference('sup-', [status(thm)], ['74', '75'])).
% 1.20/1.40  thf('77', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         ((r2_xboole_0 @ k1_xboole_0 @ X0) | ((k4_xboole_0 @ X0 @ X0) = (X0)))),
% 1.20/1.40      inference('sup+', [status(thm)], ['73', '76'])).
% 1.20/1.40  thf('78', plain,
% 1.20/1.40      (![X5 : $i, X6 : $i, X8 : $i]:
% 1.20/1.40         (~ (r2_hidden @ X8 @ X6)
% 1.20/1.40          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 1.20/1.40      inference('simplify', [status(thm)], ['67'])).
% 1.20/1.40  thf('79', plain,
% 1.20/1.40      (![X0 : $i, X1 : $i]:
% 1.20/1.40         (~ (r2_hidden @ X1 @ X0)
% 1.20/1.40          | (r2_xboole_0 @ k1_xboole_0 @ X0)
% 1.20/1.40          | ~ (r2_hidden @ X1 @ X0))),
% 1.20/1.40      inference('sup-', [status(thm)], ['77', '78'])).
% 1.20/1.40  thf('80', plain,
% 1.20/1.40      (![X0 : $i, X1 : $i]:
% 1.20/1.40         ((r2_xboole_0 @ k1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 1.20/1.40      inference('simplify', [status(thm)], ['79'])).
% 1.20/1.40  thf('81', plain, ((r2_xboole_0 @ k1_xboole_0 @ sk_C_1)),
% 1.20/1.40      inference('sup-', [status(thm)], ['60', '80'])).
% 1.20/1.40  thf('82', plain,
% 1.20/1.40      (((r2_xboole_0 @ k1_xboole_0 @ k1_xboole_0))
% 1.20/1.40         <= (~ ((r2_xboole_0 @ sk_C_1 @ sk_D_1)) & 
% 1.20/1.40             ((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D_1)))),
% 1.20/1.40      inference('sup+', [status(thm)], ['48', '81'])).
% 1.20/1.40  thf('83', plain,
% 1.20/1.40      (![X10 : $i, X11 : $i]: (((X10) != (X11)) | ~ (r2_xboole_0 @ X10 @ X11))),
% 1.20/1.40      inference('cnf', [status(esa)], [d8_xboole_0])).
% 1.20/1.40  thf('84', plain, (![X11 : $i]: ~ (r2_xboole_0 @ X11 @ X11)),
% 1.20/1.40      inference('simplify', [status(thm)], ['83'])).
% 1.20/1.40  thf('85', plain,
% 1.20/1.40      (((r2_xboole_0 @ sk_C_1 @ sk_D_1)) | 
% 1.20/1.40       ~ ((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D_1))),
% 1.20/1.40      inference('sup-', [status(thm)], ['82', '84'])).
% 1.20/1.40  thf('86', plain,
% 1.20/1.40      (((r2_xboole_0 @ sk_C_1 @ sk_D_1)) | 
% 1.20/1.40       ((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D_1))),
% 1.20/1.40      inference('split', [status(esa)], ['0'])).
% 1.20/1.40  thf('87', plain, (((r2_xboole_0 @ sk_C_1 @ sk_D_1))),
% 1.20/1.40      inference('sat_resolution*', [status(thm)], ['3', '85', '86'])).
% 1.20/1.40  thf('88', plain, ((r2_xboole_0 @ sk_C_1 @ sk_D_1)),
% 1.20/1.40      inference('simpl_trail', [status(thm)], ['1', '87'])).
% 1.20/1.40  thf('89', plain, ((m2_orders_2 @ sk_D_1 @ sk_A @ sk_B)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('90', plain, ((m2_orders_2 @ sk_C_1 @ sk_A @ sk_B)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('91', plain,
% 1.20/1.40      ((m1_orders_1 @ sk_B @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf(t83_orders_2, axiom,
% 1.20/1.40    (![A:$i]:
% 1.20/1.40     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.20/1.40         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.20/1.40       ( ![B:$i]:
% 1.20/1.40         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.20/1.40           ( ![C:$i]:
% 1.20/1.40             ( ( m2_orders_2 @ C @ A @ B ) =>
% 1.20/1.40               ( ![D:$i]:
% 1.20/1.40                 ( ( m2_orders_2 @ D @ A @ B ) =>
% 1.20/1.40                   ( ( ( C ) != ( D ) ) =>
% 1.20/1.40                     ( ( m1_orders_2 @ C @ A @ D ) <=>
% 1.20/1.40                       ( ~( m1_orders_2 @ D @ A @ C ) ) ) ) ) ) ) ) ) ) ))).
% 1.20/1.40  thf('92', plain,
% 1.20/1.40      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 1.20/1.40         (~ (m1_orders_1 @ X37 @ (k1_orders_1 @ (u1_struct_0 @ X38)))
% 1.20/1.40          | ~ (m2_orders_2 @ X39 @ X38 @ X37)
% 1.20/1.40          | (m1_orders_2 @ X39 @ X38 @ X40)
% 1.20/1.40          | (m1_orders_2 @ X40 @ X38 @ X39)
% 1.20/1.40          | ((X40) = (X39))
% 1.20/1.40          | ~ (m2_orders_2 @ X40 @ X38 @ X37)
% 1.20/1.40          | ~ (l1_orders_2 @ X38)
% 1.20/1.40          | ~ (v5_orders_2 @ X38)
% 1.20/1.40          | ~ (v4_orders_2 @ X38)
% 1.20/1.40          | ~ (v3_orders_2 @ X38)
% 1.20/1.40          | (v2_struct_0 @ X38))),
% 1.20/1.40      inference('cnf', [status(esa)], [t83_orders_2])).
% 1.20/1.40  thf('93', plain,
% 1.20/1.40      (![X0 : $i, X1 : $i]:
% 1.20/1.40         ((v2_struct_0 @ sk_A)
% 1.20/1.40          | ~ (v3_orders_2 @ sk_A)
% 1.20/1.40          | ~ (v4_orders_2 @ sk_A)
% 1.20/1.40          | ~ (v5_orders_2 @ sk_A)
% 1.20/1.40          | ~ (l1_orders_2 @ sk_A)
% 1.20/1.40          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 1.20/1.40          | ((X0) = (X1))
% 1.20/1.40          | (m1_orders_2 @ X0 @ sk_A @ X1)
% 1.20/1.40          | (m1_orders_2 @ X1 @ sk_A @ X0)
% 1.20/1.40          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B))),
% 1.20/1.40      inference('sup-', [status(thm)], ['91', '92'])).
% 1.20/1.40  thf('94', plain, ((v3_orders_2 @ sk_A)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('95', plain, ((v4_orders_2 @ sk_A)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('96', plain, ((v5_orders_2 @ sk_A)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('97', plain, ((l1_orders_2 @ sk_A)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('98', plain,
% 1.20/1.40      (![X0 : $i, X1 : $i]:
% 1.20/1.40         ((v2_struct_0 @ sk_A)
% 1.20/1.40          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 1.20/1.40          | ((X0) = (X1))
% 1.20/1.40          | (m1_orders_2 @ X0 @ sk_A @ X1)
% 1.20/1.40          | (m1_orders_2 @ X1 @ sk_A @ X0)
% 1.20/1.40          | ~ (m2_orders_2 @ X1 @ sk_A @ sk_B))),
% 1.20/1.40      inference('demod', [status(thm)], ['93', '94', '95', '96', '97'])).
% 1.20/1.40  thf('99', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B)
% 1.20/1.40          | (m1_orders_2 @ X0 @ sk_A @ sk_C_1)
% 1.20/1.40          | (m1_orders_2 @ sk_C_1 @ sk_A @ X0)
% 1.20/1.40          | ((sk_C_1) = (X0))
% 1.20/1.40          | (v2_struct_0 @ sk_A))),
% 1.20/1.40      inference('sup-', [status(thm)], ['90', '98'])).
% 1.20/1.40  thf('100', plain,
% 1.20/1.40      (((v2_struct_0 @ sk_A)
% 1.20/1.40        | ((sk_C_1) = (sk_D_1))
% 1.20/1.40        | (m1_orders_2 @ sk_C_1 @ sk_A @ sk_D_1)
% 1.20/1.40        | (m1_orders_2 @ sk_D_1 @ sk_A @ sk_C_1))),
% 1.20/1.40      inference('sup-', [status(thm)], ['89', '99'])).
% 1.20/1.40  thf('101', plain,
% 1.20/1.40      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.20/1.40      inference('sup-', [status(thm)], ['33', '34'])).
% 1.20/1.40  thf('102', plain,
% 1.20/1.40      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.20/1.40         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 1.20/1.40          | (r1_tarski @ X30 @ X28)
% 1.20/1.40          | ~ (m1_orders_2 @ X30 @ X29 @ X28)
% 1.20/1.40          | ~ (l1_orders_2 @ X29)
% 1.20/1.40          | ~ (v5_orders_2 @ X29)
% 1.20/1.40          | ~ (v4_orders_2 @ X29)
% 1.20/1.40          | ~ (v3_orders_2 @ X29)
% 1.20/1.40          | (v2_struct_0 @ X29))),
% 1.20/1.40      inference('cnf', [status(esa)], [t67_orders_2])).
% 1.20/1.40  thf('103', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         ((v2_struct_0 @ sk_A)
% 1.20/1.40          | ~ (v3_orders_2 @ sk_A)
% 1.20/1.40          | ~ (v4_orders_2 @ sk_A)
% 1.20/1.40          | ~ (v5_orders_2 @ sk_A)
% 1.20/1.40          | ~ (l1_orders_2 @ sk_A)
% 1.20/1.40          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C_1)
% 1.20/1.40          | (r1_tarski @ X0 @ sk_C_1))),
% 1.20/1.40      inference('sup-', [status(thm)], ['101', '102'])).
% 1.20/1.40  thf('104', plain, ((v3_orders_2 @ sk_A)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('105', plain, ((v4_orders_2 @ sk_A)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('106', plain, ((v5_orders_2 @ sk_A)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('107', plain, ((l1_orders_2 @ sk_A)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('108', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         ((v2_struct_0 @ sk_A)
% 1.20/1.40          | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C_1)
% 1.20/1.40          | (r1_tarski @ X0 @ sk_C_1))),
% 1.20/1.40      inference('demod', [status(thm)], ['103', '104', '105', '106', '107'])).
% 1.20/1.40  thf('109', plain, (~ (v2_struct_0 @ sk_A)),
% 1.20/1.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.40  thf('110', plain,
% 1.20/1.40      (![X0 : $i]:
% 1.20/1.40         ((r1_tarski @ X0 @ sk_C_1) | ~ (m1_orders_2 @ X0 @ sk_A @ sk_C_1))),
% 1.20/1.40      inference('clc', [status(thm)], ['108', '109'])).
% 1.20/1.40  thf('111', plain,
% 1.20/1.40      (((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D_1)
% 1.20/1.40        | ((sk_C_1) = (sk_D_1))
% 1.20/1.40        | (v2_struct_0 @ sk_A)
% 1.20/1.40        | (r1_tarski @ sk_D_1 @ sk_C_1))),
% 1.20/1.40      inference('sup-', [status(thm)], ['100', '110'])).
% 1.20/1.40  thf('112', plain,
% 1.20/1.40      ((~ (m1_orders_2 @ sk_C_1 @ sk_A @ sk_D_1))
% 1.20/1.40         <= (~ ((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D_1)))),
% 1.20/1.40      inference('split', [status(esa)], ['2'])).
% 1.20/1.40  thf('113', plain, (~ ((m1_orders_2 @ sk_C_1 @ sk_A @ sk_D_1))),
% 1.20/1.40      inference('sat_resolution*', [status(thm)], ['3', '85'])).
% 1.20/1.40  thf('114', plain, (~ (m1_orders_2 @ sk_C_1 @ sk_A @ sk_D_1)),
% 1.20/1.40      inference('simpl_trail', [status(thm)], ['112', '113'])).
% 1.20/1.40  thf('115', plain,
% 1.20/1.40      (((r1_tarski @ sk_D_1 @ sk_C_1)
% 1.20/1.40        | (v2_struct_0 @ sk_A)
% 1.20/1.40        | ((sk_C_1) = (sk_D_1)))),
% 1.20/1.40      inference('sup-', [status(thm)], ['111', '114'])).
% 1.20/1.40  thf('116', plain,
% 1.20/1.40      (((r2_xboole_0 @ sk_C_1 @ sk_D_1)) <= (((r2_xboole_0 @ sk_C_1 @ sk_D_1)))),
% 1.20/1.40      inference('split', [status(esa)], ['0'])).
% 1.20/1.40  thf('117', plain,
% 1.20/1.41      (![X10 : $i, X11 : $i]:
% 1.20/1.41         ((r1_tarski @ X10 @ X11) | ~ (r2_xboole_0 @ X10 @ X11))),
% 1.20/1.41      inference('cnf', [status(esa)], [d8_xboole_0])).
% 1.20/1.41  thf('118', plain,
% 1.20/1.41      (((r1_tarski @ sk_C_1 @ sk_D_1)) <= (((r2_xboole_0 @ sk_C_1 @ sk_D_1)))),
% 1.20/1.41      inference('sup-', [status(thm)], ['116', '117'])).
% 1.20/1.41  thf(d10_xboole_0, axiom,
% 1.20/1.41    (![A:$i,B:$i]:
% 1.20/1.41     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.20/1.41  thf('119', plain,
% 1.20/1.41      (![X13 : $i, X15 : $i]:
% 1.20/1.41         (((X13) = (X15))
% 1.20/1.41          | ~ (r1_tarski @ X15 @ X13)
% 1.20/1.41          | ~ (r1_tarski @ X13 @ X15))),
% 1.20/1.41      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.20/1.41  thf('120', plain,
% 1.20/1.41      (((~ (r1_tarski @ sk_D_1 @ sk_C_1) | ((sk_D_1) = (sk_C_1))))
% 1.20/1.41         <= (((r2_xboole_0 @ sk_C_1 @ sk_D_1)))),
% 1.20/1.41      inference('sup-', [status(thm)], ['118', '119'])).
% 1.20/1.41  thf('121', plain, (((r2_xboole_0 @ sk_C_1 @ sk_D_1))),
% 1.20/1.41      inference('sat_resolution*', [status(thm)], ['3', '85', '86'])).
% 1.20/1.41  thf('122', plain,
% 1.20/1.41      ((~ (r1_tarski @ sk_D_1 @ sk_C_1) | ((sk_D_1) = (sk_C_1)))),
% 1.20/1.41      inference('simpl_trail', [status(thm)], ['120', '121'])).
% 1.20/1.41  thf('123', plain, ((((sk_C_1) = (sk_D_1)) | (v2_struct_0 @ sk_A))),
% 1.20/1.41      inference('clc', [status(thm)], ['115', '122'])).
% 1.20/1.41  thf('124', plain, (~ (v2_struct_0 @ sk_A)),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.41  thf('125', plain, (((sk_C_1) = (sk_D_1))),
% 1.20/1.41      inference('clc', [status(thm)], ['123', '124'])).
% 1.20/1.41  thf('126', plain, ((r2_xboole_0 @ sk_C_1 @ sk_C_1)),
% 1.20/1.41      inference('demod', [status(thm)], ['88', '125'])).
% 1.20/1.41  thf('127', plain, (![X11 : $i]: ~ (r2_xboole_0 @ X11 @ X11)),
% 1.20/1.41      inference('simplify', [status(thm)], ['83'])).
% 1.20/1.41  thf('128', plain, ($false), inference('sup-', [status(thm)], ['126', '127'])).
% 1.20/1.41  
% 1.20/1.41  % SZS output end Refutation
% 1.20/1.41  
% 1.20/1.41  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
