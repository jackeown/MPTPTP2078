%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1101+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MD2xRfdGjH

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:06 EST 2020

% Result     : Theorem 9.61s
% Output     : Refutation 9.61s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 364 expanded)
%              Number of leaves         :   28 ( 125 expanded)
%              Depth                    :   12
%              Number of atoms          :  557 (2907 expanded)
%              Number of equality atoms :   54 ( 241 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_B_112_type,type,(
    sk_B_112: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_22_type,type,(
    sk_A_22: $i )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X5877: $i] :
      ( ( ( k2_struct_0 @ X5877 )
        = ( u1_struct_0 @ X5877 ) )
      | ~ ( l1_struct_0 @ X5877 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t18_pre_topc,conjecture,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( k4_subset_1 @ ( u1_struct_0 @ A @ ( B @ ( k3_subset_1 @ ( u1_struct_0 @ A @ B ) ) ) ) )
            = ( k2_struct_0 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_struct_0 @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( ( k4_subset_1 @ ( u1_struct_0 @ A @ ( B @ ( k3_subset_1 @ ( u1_struct_0 @ A @ B ) ) ) ) )
              = ( k2_struct_0 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t18_pre_topc])).

thf('1',plain,(
    m1_subset_1 @ ( sk_B_112 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A_22 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X4951: $i] :
      ( ( k9_setfam_1 @ X4951 )
      = ( k1_zfmisc_1 @ X4951 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('3',plain,(
    m1_subset_1 @ ( sk_B_112 @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A_22 ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ( m1_subset_1 @ ( sk_B_112 @ ( k9_setfam_1 @ ( k2_struct_0 @ sk_A_22 ) ) ) )
    | ~ ( l1_struct_0 @ sk_A_22 ) ),
    inference('sup+',[status(thm)],['0','3'])).

thf('5',plain,(
    l1_struct_0 @ sk_A_22 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ ( sk_B_112 @ ( k9_setfam_1 @ ( k2_struct_0 @ sk_A_22 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t25_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ ( A @ ( B @ ( k3_subset_1 @ ( A @ B ) ) ) ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X1676: $i,X1677: $i] :
      ( ( ( k4_subset_1 @ ( X1676 @ ( X1677 @ ( k3_subset_1 @ ( X1676 @ X1677 ) ) ) ) )
        = ( k2_subset_1 @ X1676 ) )
      | ~ ( m1_subset_1 @ ( X1677 @ ( k1_zfmisc_1 @ X1676 ) ) ) ) ),
    inference(cnf,[status(esa)],[t25_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('8',plain,(
    ! [X1521: $i] :
      ( ( k2_subset_1 @ X1521 )
      = X1521 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('9',plain,(
    ! [X4951: $i] :
      ( ( k9_setfam_1 @ X4951 )
      = ( k1_zfmisc_1 @ X4951 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('10',plain,(
    ! [X1676: $i,X1677: $i] :
      ( ( ( k4_subset_1 @ ( X1676 @ ( X1677 @ ( k3_subset_1 @ ( X1676 @ X1677 ) ) ) ) )
        = X1676 )
      | ~ ( m1_subset_1 @ ( X1677 @ ( k9_setfam_1 @ X1676 ) ) ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,
    ( ( k4_subset_1 @ ( k2_struct_0 @ sk_A_22 @ ( sk_B_112 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A_22 @ sk_B_112 ) ) ) ) )
    = ( k2_struct_0 @ sk_A_22 ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf('12',plain,(
    m1_subset_1 @ ( sk_B_112 @ ( k9_setfam_1 @ ( k2_struct_0 @ sk_A_22 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k3_subset_1 @ ( A @ B ) )
        = ( k4_xboole_0 @ ( A @ B ) ) ) ) )).

thf('13',plain,(
    ! [X1542: $i,X1543: $i] :
      ( ( ( k3_subset_1 @ ( X1542 @ X1543 ) )
        = ( k4_xboole_0 @ ( X1542 @ X1543 ) ) )
      | ~ ( m1_subset_1 @ ( X1543 @ ( k1_zfmisc_1 @ X1542 ) ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ ( A @ B ) )
      = ( k4_xboole_0 @ ( A @ B ) ) ) )).

thf('14',plain,(
    ! [X1646: $i,X1647: $i] :
      ( ( k6_subset_1 @ ( X1646 @ X1647 ) )
      = ( k4_xboole_0 @ ( X1646 @ X1647 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('15',plain,(
    ! [X4951: $i] :
      ( ( k9_setfam_1 @ X4951 )
      = ( k1_zfmisc_1 @ X4951 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('16',plain,(
    ! [X1542: $i,X1543: $i] :
      ( ( ( k3_subset_1 @ ( X1542 @ X1543 ) )
        = ( k6_subset_1 @ ( X1542 @ X1543 ) ) )
      | ~ ( m1_subset_1 @ ( X1543 @ ( k9_setfam_1 @ X1542 ) ) ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A_22 @ sk_B_112 ) )
    = ( k6_subset_1 @ ( k2_struct_0 @ sk_A_22 @ sk_B_112 ) ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,(
    m1_subset_1 @ ( sk_B_112 @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A_22 ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ ( A @ ( k1_zfmisc_1 @ B ) ) )
    <=> ( r1_tarski @ ( A @ B ) ) ) )).

thf('19',plain,(
    ! [X1964: $i,X1965: $i] :
      ( ( r1_tarski @ ( X1964 @ X1965 ) )
      | ~ ( m1_subset_1 @ ( X1964 @ ( k1_zfmisc_1 @ X1965 ) ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('20',plain,(
    ! [X4951: $i] :
      ( ( k9_setfam_1 @ X4951 )
      = ( k1_zfmisc_1 @ X4951 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('21',plain,(
    ! [X1964: $i,X1965: $i] :
      ( ( r1_tarski @ ( X1964 @ X1965 ) )
      | ~ ( m1_subset_1 @ ( X1964 @ ( k9_setfam_1 @ X1965 ) ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    r1_tarski @ ( sk_B_112 @ ( u1_struct_0 @ sk_A_22 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( ( k2_xboole_0 @ ( A @ B ) )
        = B ) ) )).

thf('23',plain,(
    ! [X161: $i,X162: $i] :
      ( ( ( k2_xboole_0 @ ( X162 @ X161 ) )
        = X161 )
      | ~ ( r1_tarski @ ( X162 @ X161 ) ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('24',plain,
    ( ( k2_xboole_0 @ ( sk_B_112 @ ( u1_struct_0 @ sk_A_22 ) ) )
    = ( u1_struct_0 @ sk_A_22 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ ( k2_xboole_0 @ ( A @ B ) ) ) )
      = A ) )).

thf('25',plain,(
    ! [X190: $i,X191: $i] :
      ( ( k3_xboole_0 @ ( X190 @ ( k2_xboole_0 @ ( X190 @ X191 ) ) ) )
      = X190 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('26',plain,
    ( ( k3_xboole_0 @ ( sk_B_112 @ ( u1_struct_0 @ sk_A_22 ) ) )
    = sk_B_112 ),
    inference('sup+',[status(thm)],['24','25'])).

thf(l98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ ( A @ B ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ ( A @ B ) @ ( k3_xboole_0 @ ( A @ B ) ) ) ) ) )).

thf('27',plain,(
    ! [X99: $i,X100: $i] :
      ( ( k5_xboole_0 @ ( X99 @ X100 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ ( X99 @ X100 ) @ ( k3_xboole_0 @ ( X99 @ X100 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('28',plain,(
    ! [X1646: $i,X1647: $i] :
      ( ( k6_subset_1 @ ( X1646 @ X1647 ) )
      = ( k4_xboole_0 @ ( X1646 @ X1647 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('29',plain,(
    ! [X99: $i,X100: $i] :
      ( ( k5_xboole_0 @ ( X99 @ X100 ) )
      = ( k6_subset_1 @ ( k2_xboole_0 @ ( X99 @ X100 ) @ ( k3_xboole_0 @ ( X99 @ X100 ) ) ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k5_xboole_0 @ ( sk_B_112 @ ( u1_struct_0 @ sk_A_22 ) ) )
    = ( k6_subset_1 @ ( k2_xboole_0 @ ( sk_B_112 @ ( u1_struct_0 @ sk_A_22 ) ) @ sk_B_112 ) ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('31',plain,
    ( ( k2_xboole_0 @ ( sk_B_112 @ ( u1_struct_0 @ sk_A_22 ) ) )
    = ( u1_struct_0 @ sk_A_22 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('32',plain,
    ( ( k5_xboole_0 @ ( sk_B_112 @ ( u1_struct_0 @ sk_A_22 ) ) )
    = ( k6_subset_1 @ ( u1_struct_0 @ sk_A_22 @ sk_B_112 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X5877: $i] :
      ( ( ( k2_struct_0 @ X5877 )
        = ( u1_struct_0 @ X5877 ) )
      | ~ ( l1_struct_0 @ X5877 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('34',plain,
    ( ( k2_xboole_0 @ ( sk_B_112 @ ( u1_struct_0 @ sk_A_22 ) ) )
    = ( u1_struct_0 @ sk_A_22 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('35',plain,
    ( ( ( k2_xboole_0 @ ( sk_B_112 @ ( k2_struct_0 @ sk_A_22 ) ) )
      = ( u1_struct_0 @ sk_A_22 ) )
    | ~ ( l1_struct_0 @ sk_A_22 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_struct_0 @ sk_A_22 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k2_xboole_0 @ ( sk_B_112 @ ( k2_struct_0 @ sk_A_22 ) ) )
    = ( u1_struct_0 @ sk_A_22 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ ( sk_B_112 @ ( k9_setfam_1 @ ( k2_struct_0 @ sk_A_22 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('39',plain,(
    ! [X1964: $i,X1965: $i] :
      ( ( r1_tarski @ ( X1964 @ X1965 ) )
      | ~ ( m1_subset_1 @ ( X1964 @ ( k9_setfam_1 @ X1965 ) ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('40',plain,(
    r1_tarski @ ( sk_B_112 @ ( k2_struct_0 @ sk_A_22 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X161: $i,X162: $i] :
      ( ( ( k2_xboole_0 @ ( X162 @ X161 ) )
        = X161 )
      | ~ ( r1_tarski @ ( X162 @ X161 ) ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('42',plain,
    ( ( k2_xboole_0 @ ( sk_B_112 @ ( k2_struct_0 @ sk_A_22 ) ) )
    = ( k2_struct_0 @ sk_A_22 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( u1_struct_0 @ sk_A_22 )
    = ( k2_struct_0 @ sk_A_22 ) ),
    inference('sup+',[status(thm)],['37','42'])).

thf('44',plain,
    ( ( u1_struct_0 @ sk_A_22 )
    = ( k2_struct_0 @ sk_A_22 ) ),
    inference('sup+',[status(thm)],['37','42'])).

thf('45',plain,
    ( ( k5_xboole_0 @ ( sk_B_112 @ ( k2_struct_0 @ sk_A_22 ) ) )
    = ( k6_subset_1 @ ( k2_struct_0 @ sk_A_22 @ sk_B_112 ) ) ),
    inference(demod,[status(thm)],['32','43','44'])).

thf('46',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A_22 @ sk_B_112 ) )
    = ( k5_xboole_0 @ ( sk_B_112 @ ( k2_struct_0 @ sk_A_22 ) ) ) ),
    inference(demod,[status(thm)],['17','45'])).

thf('47',plain,
    ( ( k4_subset_1 @ ( k2_struct_0 @ sk_A_22 @ ( sk_B_112 @ ( k5_xboole_0 @ ( sk_B_112 @ ( k2_struct_0 @ sk_A_22 ) ) ) ) ) )
    = ( k2_struct_0 @ sk_A_22 ) ),
    inference(demod,[status(thm)],['11','46'])).

thf('48',plain,(
    ! [X5877: $i] :
      ( ( ( k2_struct_0 @ X5877 )
        = ( u1_struct_0 @ X5877 ) )
      | ~ ( l1_struct_0 @ X5877 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('49',plain,(
    ! [X5877: $i] :
      ( ( ( k2_struct_0 @ X5877 )
        = ( u1_struct_0 @ X5877 ) )
      | ~ ( l1_struct_0 @ X5877 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('50',plain,(
    ( k4_subset_1 @ ( u1_struct_0 @ sk_A_22 @ ( sk_B_112 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A_22 @ sk_B_112 ) ) ) ) )
 != ( k2_struct_0 @ sk_A_22 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A_22 @ ( sk_B_112 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A_22 @ sk_B_112 ) ) ) ) )
     != ( k2_struct_0 @ sk_A_22 ) )
    | ~ ( l1_struct_0 @ sk_A_22 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_struct_0 @ sk_A_22 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ( k4_subset_1 @ ( u1_struct_0 @ sk_A_22 @ ( sk_B_112 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A_22 @ sk_B_112 ) ) ) ) )
 != ( k2_struct_0 @ sk_A_22 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( k4_subset_1 @ ( k2_struct_0 @ sk_A_22 @ ( sk_B_112 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A_22 @ sk_B_112 ) ) ) ) )
     != ( k2_struct_0 @ sk_A_22 ) )
    | ~ ( l1_struct_0 @ sk_A_22 ) ),
    inference('sup-',[status(thm)],['48','53'])).

thf('55',plain,(
    l1_struct_0 @ sk_A_22 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ( k4_subset_1 @ ( k2_struct_0 @ sk_A_22 @ ( sk_B_112 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A_22 @ sk_B_112 ) ) ) ) )
 != ( k2_struct_0 @ sk_A_22 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A_22 @ sk_B_112 ) )
    = ( k5_xboole_0 @ ( sk_B_112 @ ( k2_struct_0 @ sk_A_22 ) ) ) ),
    inference(demod,[status(thm)],['17','45'])).

thf('58',plain,(
    ( k4_subset_1 @ ( k2_struct_0 @ sk_A_22 @ ( sk_B_112 @ ( k5_xboole_0 @ ( sk_B_112 @ ( k2_struct_0 @ sk_A_22 ) ) ) ) ) )
 != ( k2_struct_0 @ sk_A_22 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['47','58'])).

%------------------------------------------------------------------------------
