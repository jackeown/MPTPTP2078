%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.50NvZdoQ48

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:11 EST 2020

% Result     : Theorem 0.89s
% Output     : Refutation 0.89s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 310 expanded)
%              Number of leaves         :   21 (  99 expanded)
%              Depth                    :   14
%              Number of atoms          :  951 (3189 expanded)
%              Number of equality atoms :   66 ( 280 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(t46_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ~ ( ( B != k1_xboole_0 )
          & ( ( k7_setfam_1 @ A @ B )
            = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ~ ( ( B != k1_xboole_0 )
            & ( ( k7_setfam_1 @ A @ B )
              = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t46_setfam_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('2',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( k7_setfam_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
         => ( ( C
              = ( k7_setfam_1 @ A @ B ) )
          <=> ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
               => ( ( r2_hidden @ D @ C )
                <=> ( r2_hidden @ ( k3_subset_1 @ A @ D ) @ B ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) )
      | ( r2_hidden @ ( sk_D @ X12 @ X14 @ X13 ) @ X12 )
      | ( r2_hidden @ ( k3_subset_1 @ X13 @ ( sk_D @ X12 @ X14 @ X13 ) ) @ X14 )
      | ( X12
        = ( k7_setfam_1 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( sk_B
        = ( k7_setfam_1 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_D @ sk_B @ X0 @ sk_A ) ) @ X0 )
      | ( r2_hidden @ ( sk_D @ sk_B @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) ) @ k1_xboole_0 )
    | ( sk_B
      = ( k7_setfam_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) )
      | ( m1_subset_1 @ ( sk_D @ X12 @ X14 @ X13 ) @ ( k1_zfmisc_1 @ X13 ) )
      | ( X12
        = ( k7_setfam_1 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( sk_B
        = ( k7_setfam_1 @ sk_A @ X0 ) )
      | ( m1_subset_1 @ ( sk_D @ sk_B @ X0 @ sk_A ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( sk_B
      = ( k7_setfam_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_subset_1 @ X4 @ X5 )
        = ( k4_xboole_0 @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k6_subset_1 @ X10 @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('16',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_subset_1 @ X4 @ X5 )
        = ( k6_subset_1 @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_B
      = ( k7_setfam_1 @ sk_A @ k1_xboole_0 ) )
    | ( ( k3_subset_1 @ sk_A @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) )
      = ( k6_subset_1 @ sk_A @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('19',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('20',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) )
      | ( r2_hidden @ ( sk_D @ X12 @ X14 @ X13 ) @ X12 )
      | ( r2_hidden @ ( k3_subset_1 @ X13 @ ( sk_D @ X12 @ X14 @ X13 ) ) @ X14 )
      | ( X12
        = ( k7_setfam_1 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k7_setfam_1 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_D @ k1_xboole_0 @ X0 @ sk_A ) ) @ X0 )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ sk_A ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_A ) ) @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k7_setfam_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('24',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ( ( k4_xboole_0 @ X2 @ ( k1_tarski @ X1 ) )
       != X2 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ( k1_xboole_0
      = ( k7_setfam_1 @ sk_A @ k1_xboole_0 ) )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_A ) ) @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['22','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('29',plain,
    ( k1_xboole_0
    = ( k7_setfam_1 @ sk_A @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k3_subset_1 @ sk_A @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) )
      = ( k6_subset_1 @ sk_A @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['17','29'])).

thf('31',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( k3_subset_1 @ sk_A @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) )
    = ( k6_subset_1 @ sk_A @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['30','31'])).

thf('33',plain,
    ( k1_xboole_0
    = ( k7_setfam_1 @ sk_A @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('34',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( k6_subset_1 @ sk_A @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) ) @ k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','32','33'])).

thf('35',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( k6_subset_1 @ sk_A @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) ) @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( sk_B
      = ( k7_setfam_1 @ sk_A @ k1_xboole_0 ) )
    | ( ( k3_subset_1 @ sk_A @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) )
      = ( k6_subset_1 @ sk_A @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('38',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( sk_B
      = ( k7_setfam_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('39',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X9 @ ( k3_subset_1 @ X9 @ X8 ) )
        = X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('40',plain,
    ( ( sk_B
      = ( k7_setfam_1 @ sk_A @ k1_xboole_0 ) )
    | ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) ) )
      = ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( k3_subset_1 @ sk_A @ ( k6_subset_1 @ sk_A @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) ) )
      = ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) )
    | ( sk_B
      = ( k7_setfam_1 @ sk_A @ k1_xboole_0 ) )
    | ( sk_B
      = ( k7_setfam_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['37','40'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('42',plain,(
    ! [X6: $i,X7: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('43',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_subset_1 @ X4 @ X5 )
        = ( k6_subset_1 @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( k6_subset_1 @ sk_A @ ( k6_subset_1 @ sk_A @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) ) )
      = ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) )
    | ( sk_B
      = ( k7_setfam_1 @ sk_A @ k1_xboole_0 ) )
    | ( sk_B
      = ( k7_setfam_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['41','44'])).

thf('46',plain,
    ( ( sk_B
      = ( k7_setfam_1 @ sk_A @ k1_xboole_0 ) )
    | ( ( k6_subset_1 @ sk_A @ ( k6_subset_1 @ sk_A @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) ) )
      = ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X6: $i,X7: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('48',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X9 @ ( k3_subset_1 @ X9 @ X8 ) )
        = X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) )
      = ( k6_subset_1 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) )
      = ( k6_subset_1 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('54',plain,
    ( ( k7_setfam_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) )
      | ( X12
       != ( k7_setfam_1 @ X13 @ X14 ) )
      | ( r2_hidden @ X15 @ X12 )
      | ~ ( r2_hidden @ ( k3_subset_1 @ X13 @ X15 ) @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('56',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ X13 @ X15 ) @ X14 )
      | ( r2_hidden @ X15 @ ( k7_setfam_1 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ ( k7_setfam_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['54','56'])).

thf('58',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('59',plain,
    ( ( k7_setfam_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['57','58','59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k6_subset_1 @ sk_A @ ( k6_subset_1 @ sk_A @ X0 ) ) @ sk_B )
      | ~ ( m1_subset_1 @ ( k6_subset_1 @ sk_A @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['53','63'])).

thf('65',plain,(
    ! [X6: $i,X7: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('66',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ ( k6_subset_1 @ sk_A @ ( k6_subset_1 @ sk_A @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ ( k6_subset_1 @ sk_A @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['52','66'])).

thf('68',plain,
    ( ~ ( r2_hidden @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) @ sk_B )
    | ( sk_B
      = ( k7_setfam_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['46','67'])).

thf('69',plain,
    ( k1_xboole_0
    = ( k7_setfam_1 @ sk_A @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('70',plain,
    ( ~ ( r2_hidden @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ~ ( r2_hidden @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['70','71'])).

thf('73',plain,(
    r2_hidden @ ( k6_subset_1 @ sk_A @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) ) @ k1_xboole_0 ),
    inference(clc,[status(thm)],['36','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('75',plain,(
    $false ),
    inference('sup-',[status(thm)],['73','74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.50NvZdoQ48
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:46:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.89/1.16  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.89/1.16  % Solved by: fo/fo7.sh
% 0.89/1.16  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.89/1.16  % done 955 iterations in 0.717s
% 0.89/1.16  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.89/1.16  % SZS output start Refutation
% 0.89/1.16  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.89/1.16  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.89/1.16  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.89/1.16  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.89/1.16  thf(sk_A_type, type, sk_A: $i).
% 0.89/1.16  thf(sk_B_type, type, sk_B: $i).
% 0.89/1.16  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.89/1.16  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.89/1.16  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.89/1.16  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.89/1.16  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.89/1.16  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.89/1.16  thf(t46_setfam_1, conjecture,
% 0.89/1.16    (![A:$i,B:$i]:
% 0.89/1.16     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.89/1.16       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.89/1.16            ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.89/1.16  thf(zf_stmt_0, negated_conjecture,
% 0.89/1.16    (~( ![A:$i,B:$i]:
% 0.89/1.16        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.89/1.16          ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.89/1.16               ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) )),
% 0.89/1.16    inference('cnf.neg', [status(esa)], [t46_setfam_1])).
% 0.89/1.16  thf('0', plain,
% 0.89/1.16      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.89/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.16  thf(dt_k7_setfam_1, axiom,
% 0.89/1.16    (![A:$i,B:$i]:
% 0.89/1.16     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.89/1.16       ( m1_subset_1 @
% 0.89/1.16         ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.89/1.16  thf('1', plain,
% 0.89/1.16      (![X16 : $i, X17 : $i]:
% 0.89/1.16         ((m1_subset_1 @ (k7_setfam_1 @ X16 @ X17) @ 
% 0.89/1.16           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16)))
% 0.89/1.16          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16))))),
% 0.89/1.16      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 0.89/1.16  thf('2', plain,
% 0.89/1.16      ((m1_subset_1 @ (k7_setfam_1 @ sk_A @ sk_B) @ 
% 0.89/1.16        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.89/1.16      inference('sup-', [status(thm)], ['0', '1'])).
% 0.89/1.16  thf('3', plain, (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.89/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.16  thf('4', plain,
% 0.89/1.16      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.89/1.16      inference('demod', [status(thm)], ['2', '3'])).
% 0.89/1.16  thf('5', plain,
% 0.89/1.16      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.89/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.16  thf(d8_setfam_1, axiom,
% 0.89/1.16    (![A:$i,B:$i]:
% 0.89/1.16     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.89/1.16       ( ![C:$i]:
% 0.89/1.16         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.89/1.16           ( ( ( C ) = ( k7_setfam_1 @ A @ B ) ) <=>
% 0.89/1.16             ( ![D:$i]:
% 0.89/1.16               ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.89/1.16                 ( ( r2_hidden @ D @ C ) <=>
% 0.89/1.16                   ( r2_hidden @ ( k3_subset_1 @ A @ D ) @ B ) ) ) ) ) ) ) ))).
% 0.89/1.16  thf('6', plain,
% 0.89/1.16      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.89/1.16         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X13)))
% 0.89/1.16          | (r2_hidden @ (sk_D @ X12 @ X14 @ X13) @ X12)
% 0.89/1.16          | (r2_hidden @ (k3_subset_1 @ X13 @ (sk_D @ X12 @ X14 @ X13)) @ X14)
% 0.89/1.16          | ((X12) = (k7_setfam_1 @ X13 @ X14))
% 0.89/1.16          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X13))))),
% 0.89/1.16      inference('cnf', [status(esa)], [d8_setfam_1])).
% 0.89/1.16  thf('7', plain,
% 0.89/1.16      (![X0 : $i]:
% 0.89/1.16         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.89/1.16          | ((sk_B) = (k7_setfam_1 @ sk_A @ X0))
% 0.89/1.16          | (r2_hidden @ (k3_subset_1 @ sk_A @ (sk_D @ sk_B @ X0 @ sk_A)) @ X0)
% 0.89/1.16          | (r2_hidden @ (sk_D @ sk_B @ X0 @ sk_A) @ sk_B))),
% 0.89/1.16      inference('sup-', [status(thm)], ['5', '6'])).
% 0.89/1.16  thf('8', plain,
% 0.89/1.16      (((r2_hidden @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A) @ sk_B)
% 0.89/1.16        | (r2_hidden @ 
% 0.89/1.16           (k3_subset_1 @ sk_A @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A)) @ 
% 0.89/1.16           k1_xboole_0)
% 0.89/1.16        | ((sk_B) = (k7_setfam_1 @ sk_A @ k1_xboole_0)))),
% 0.89/1.16      inference('sup-', [status(thm)], ['4', '7'])).
% 0.89/1.16  thf('9', plain,
% 0.89/1.16      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.89/1.16      inference('demod', [status(thm)], ['2', '3'])).
% 0.89/1.16  thf('10', plain,
% 0.89/1.16      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.89/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.16  thf('11', plain,
% 0.89/1.16      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.89/1.16         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X13)))
% 0.89/1.16          | (m1_subset_1 @ (sk_D @ X12 @ X14 @ X13) @ (k1_zfmisc_1 @ X13))
% 0.89/1.16          | ((X12) = (k7_setfam_1 @ X13 @ X14))
% 0.89/1.16          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X13))))),
% 0.89/1.16      inference('cnf', [status(esa)], [d8_setfam_1])).
% 0.89/1.16  thf('12', plain,
% 0.89/1.16      (![X0 : $i]:
% 0.89/1.16         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.89/1.16          | ((sk_B) = (k7_setfam_1 @ sk_A @ X0))
% 0.89/1.16          | (m1_subset_1 @ (sk_D @ sk_B @ X0 @ sk_A) @ (k1_zfmisc_1 @ sk_A)))),
% 0.89/1.16      inference('sup-', [status(thm)], ['10', '11'])).
% 0.89/1.16  thf('13', plain,
% 0.89/1.16      (((m1_subset_1 @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A) @ 
% 0.89/1.16         (k1_zfmisc_1 @ sk_A))
% 0.89/1.16        | ((sk_B) = (k7_setfam_1 @ sk_A @ k1_xboole_0)))),
% 0.89/1.16      inference('sup-', [status(thm)], ['9', '12'])).
% 0.89/1.16  thf(d5_subset_1, axiom,
% 0.89/1.16    (![A:$i,B:$i]:
% 0.89/1.16     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.89/1.16       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.89/1.16  thf('14', plain,
% 0.89/1.16      (![X4 : $i, X5 : $i]:
% 0.89/1.16         (((k3_subset_1 @ X4 @ X5) = (k4_xboole_0 @ X4 @ X5))
% 0.89/1.16          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.89/1.16      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.89/1.16  thf(redefinition_k6_subset_1, axiom,
% 0.89/1.16    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.89/1.16  thf('15', plain,
% 0.89/1.16      (![X10 : $i, X11 : $i]:
% 0.89/1.16         ((k6_subset_1 @ X10 @ X11) = (k4_xboole_0 @ X10 @ X11))),
% 0.89/1.16      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.89/1.16  thf('16', plain,
% 0.89/1.16      (![X4 : $i, X5 : $i]:
% 0.89/1.16         (((k3_subset_1 @ X4 @ X5) = (k6_subset_1 @ X4 @ X5))
% 0.89/1.16          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.89/1.16      inference('demod', [status(thm)], ['14', '15'])).
% 0.89/1.16  thf('17', plain,
% 0.89/1.16      ((((sk_B) = (k7_setfam_1 @ sk_A @ k1_xboole_0))
% 0.89/1.16        | ((k3_subset_1 @ sk_A @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A))
% 0.89/1.16            = (k6_subset_1 @ sk_A @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A))))),
% 0.89/1.16      inference('sup-', [status(thm)], ['13', '16'])).
% 0.89/1.16  thf('18', plain,
% 0.89/1.16      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.89/1.16      inference('demod', [status(thm)], ['2', '3'])).
% 0.89/1.16  thf('19', plain,
% 0.89/1.16      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.89/1.16      inference('demod', [status(thm)], ['2', '3'])).
% 0.89/1.16  thf('20', plain,
% 0.89/1.16      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.89/1.16         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X13)))
% 0.89/1.16          | (r2_hidden @ (sk_D @ X12 @ X14 @ X13) @ X12)
% 0.89/1.16          | (r2_hidden @ (k3_subset_1 @ X13 @ (sk_D @ X12 @ X14 @ X13)) @ X14)
% 0.89/1.16          | ((X12) = (k7_setfam_1 @ X13 @ X14))
% 0.89/1.16          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X13))))),
% 0.89/1.16      inference('cnf', [status(esa)], [d8_setfam_1])).
% 0.89/1.16  thf('21', plain,
% 0.89/1.16      (![X0 : $i]:
% 0.89/1.16         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.89/1.16          | ((k1_xboole_0) = (k7_setfam_1 @ sk_A @ X0))
% 0.89/1.16          | (r2_hidden @ 
% 0.89/1.16             (k3_subset_1 @ sk_A @ (sk_D @ k1_xboole_0 @ X0 @ sk_A)) @ X0)
% 0.89/1.16          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ sk_A) @ k1_xboole_0))),
% 0.89/1.16      inference('sup-', [status(thm)], ['19', '20'])).
% 0.89/1.16  thf('22', plain,
% 0.89/1.16      (((r2_hidden @ (sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_A) @ k1_xboole_0)
% 0.89/1.16        | (r2_hidden @ 
% 0.89/1.16           (k3_subset_1 @ sk_A @ (sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_A)) @ 
% 0.89/1.16           k1_xboole_0)
% 0.89/1.16        | ((k1_xboole_0) = (k7_setfam_1 @ sk_A @ k1_xboole_0)))),
% 0.89/1.16      inference('sup-', [status(thm)], ['18', '21'])).
% 0.89/1.16  thf(t4_boole, axiom,
% 0.89/1.16    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.89/1.16  thf('23', plain,
% 0.89/1.16      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.89/1.16      inference('cnf', [status(esa)], [t4_boole])).
% 0.89/1.16  thf(t65_zfmisc_1, axiom,
% 0.89/1.16    (![A:$i,B:$i]:
% 0.89/1.16     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.89/1.16       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.89/1.16  thf('24', plain,
% 0.89/1.16      (![X1 : $i, X2 : $i]:
% 0.89/1.16         (~ (r2_hidden @ X1 @ X2)
% 0.89/1.16          | ((k4_xboole_0 @ X2 @ (k1_tarski @ X1)) != (X2)))),
% 0.89/1.16      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.89/1.16  thf('25', plain,
% 0.89/1.16      (![X0 : $i]:
% 0.89/1.16         (((k1_xboole_0) != (k1_xboole_0)) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.89/1.16      inference('sup-', [status(thm)], ['23', '24'])).
% 0.89/1.16  thf('26', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.89/1.16      inference('simplify', [status(thm)], ['25'])).
% 0.89/1.16  thf('27', plain,
% 0.89/1.16      ((((k1_xboole_0) = (k7_setfam_1 @ sk_A @ k1_xboole_0))
% 0.89/1.16        | (r2_hidden @ 
% 0.89/1.16           (k3_subset_1 @ sk_A @ (sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_A)) @ 
% 0.89/1.16           k1_xboole_0))),
% 0.89/1.16      inference('clc', [status(thm)], ['22', '26'])).
% 0.89/1.16  thf('28', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.89/1.16      inference('simplify', [status(thm)], ['25'])).
% 0.89/1.16  thf('29', plain, (((k1_xboole_0) = (k7_setfam_1 @ sk_A @ k1_xboole_0))),
% 0.89/1.16      inference('clc', [status(thm)], ['27', '28'])).
% 0.89/1.16  thf('30', plain,
% 0.89/1.16      ((((sk_B) = (k1_xboole_0))
% 0.89/1.16        | ((k3_subset_1 @ sk_A @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A))
% 0.89/1.16            = (k6_subset_1 @ sk_A @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A))))),
% 0.89/1.16      inference('demod', [status(thm)], ['17', '29'])).
% 0.89/1.16  thf('31', plain, (((sk_B) != (k1_xboole_0))),
% 0.89/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.16  thf('32', plain,
% 0.89/1.16      (((k3_subset_1 @ sk_A @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A))
% 0.89/1.16         = (k6_subset_1 @ sk_A @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A)))),
% 0.89/1.16      inference('simplify_reflect-', [status(thm)], ['30', '31'])).
% 0.89/1.16  thf('33', plain, (((k1_xboole_0) = (k7_setfam_1 @ sk_A @ k1_xboole_0))),
% 0.89/1.16      inference('clc', [status(thm)], ['27', '28'])).
% 0.89/1.16  thf('34', plain,
% 0.89/1.16      (((r2_hidden @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A) @ sk_B)
% 0.89/1.16        | (r2_hidden @ 
% 0.89/1.16           (k6_subset_1 @ sk_A @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A)) @ 
% 0.89/1.16           k1_xboole_0)
% 0.89/1.16        | ((sk_B) = (k1_xboole_0)))),
% 0.89/1.16      inference('demod', [status(thm)], ['8', '32', '33'])).
% 0.89/1.16  thf('35', plain, (((sk_B) != (k1_xboole_0))),
% 0.89/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.16  thf('36', plain,
% 0.89/1.16      (((r2_hidden @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A) @ sk_B)
% 0.89/1.16        | (r2_hidden @ 
% 0.89/1.16           (k6_subset_1 @ sk_A @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A)) @ 
% 0.89/1.16           k1_xboole_0))),
% 0.89/1.16      inference('simplify_reflect-', [status(thm)], ['34', '35'])).
% 0.89/1.16  thf('37', plain,
% 0.89/1.16      ((((sk_B) = (k7_setfam_1 @ sk_A @ k1_xboole_0))
% 0.89/1.16        | ((k3_subset_1 @ sk_A @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A))
% 0.89/1.16            = (k6_subset_1 @ sk_A @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A))))),
% 0.89/1.16      inference('sup-', [status(thm)], ['13', '16'])).
% 0.89/1.16  thf('38', plain,
% 0.89/1.16      (((m1_subset_1 @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A) @ 
% 0.89/1.16         (k1_zfmisc_1 @ sk_A))
% 0.89/1.16        | ((sk_B) = (k7_setfam_1 @ sk_A @ k1_xboole_0)))),
% 0.89/1.16      inference('sup-', [status(thm)], ['9', '12'])).
% 0.89/1.16  thf(involutiveness_k3_subset_1, axiom,
% 0.89/1.16    (![A:$i,B:$i]:
% 0.89/1.16     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.89/1.16       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.89/1.16  thf('39', plain,
% 0.89/1.16      (![X8 : $i, X9 : $i]:
% 0.89/1.16         (((k3_subset_1 @ X9 @ (k3_subset_1 @ X9 @ X8)) = (X8))
% 0.89/1.16          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.89/1.16      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.89/1.16  thf('40', plain,
% 0.89/1.16      ((((sk_B) = (k7_setfam_1 @ sk_A @ k1_xboole_0))
% 0.89/1.16        | ((k3_subset_1 @ sk_A @ 
% 0.89/1.16            (k3_subset_1 @ sk_A @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A)))
% 0.89/1.16            = (sk_D @ sk_B @ k1_xboole_0 @ sk_A)))),
% 0.89/1.16      inference('sup-', [status(thm)], ['38', '39'])).
% 0.89/1.16  thf('41', plain,
% 0.89/1.16      ((((k3_subset_1 @ sk_A @ 
% 0.89/1.16          (k6_subset_1 @ sk_A @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A)))
% 0.89/1.16          = (sk_D @ sk_B @ k1_xboole_0 @ sk_A))
% 0.89/1.16        | ((sk_B) = (k7_setfam_1 @ sk_A @ k1_xboole_0))
% 0.89/1.16        | ((sk_B) = (k7_setfam_1 @ sk_A @ k1_xboole_0)))),
% 0.89/1.16      inference('sup+', [status(thm)], ['37', '40'])).
% 0.89/1.16  thf(dt_k6_subset_1, axiom,
% 0.89/1.16    (![A:$i,B:$i]:
% 0.89/1.16     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.89/1.16  thf('42', plain,
% 0.89/1.16      (![X6 : $i, X7 : $i]:
% 0.89/1.16         (m1_subset_1 @ (k6_subset_1 @ X6 @ X7) @ (k1_zfmisc_1 @ X6))),
% 0.89/1.16      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.89/1.16  thf('43', plain,
% 0.89/1.16      (![X4 : $i, X5 : $i]:
% 0.89/1.16         (((k3_subset_1 @ X4 @ X5) = (k6_subset_1 @ X4 @ X5))
% 0.89/1.16          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.89/1.16      inference('demod', [status(thm)], ['14', '15'])).
% 0.89/1.16  thf('44', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 0.89/1.16           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 0.89/1.16      inference('sup-', [status(thm)], ['42', '43'])).
% 0.89/1.16  thf('45', plain,
% 0.89/1.16      ((((k6_subset_1 @ sk_A @ 
% 0.89/1.16          (k6_subset_1 @ sk_A @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A)))
% 0.89/1.16          = (sk_D @ sk_B @ k1_xboole_0 @ sk_A))
% 0.89/1.16        | ((sk_B) = (k7_setfam_1 @ sk_A @ k1_xboole_0))
% 0.89/1.16        | ((sk_B) = (k7_setfam_1 @ sk_A @ k1_xboole_0)))),
% 0.89/1.16      inference('demod', [status(thm)], ['41', '44'])).
% 0.89/1.16  thf('46', plain,
% 0.89/1.16      ((((sk_B) = (k7_setfam_1 @ sk_A @ k1_xboole_0))
% 0.89/1.16        | ((k6_subset_1 @ sk_A @ 
% 0.89/1.16            (k6_subset_1 @ sk_A @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A)))
% 0.89/1.16            = (sk_D @ sk_B @ k1_xboole_0 @ sk_A)))),
% 0.89/1.16      inference('simplify', [status(thm)], ['45'])).
% 0.89/1.16  thf('47', plain,
% 0.89/1.16      (![X6 : $i, X7 : $i]:
% 0.89/1.16         (m1_subset_1 @ (k6_subset_1 @ X6 @ X7) @ (k1_zfmisc_1 @ X6))),
% 0.89/1.16      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.89/1.16  thf('48', plain,
% 0.89/1.16      (![X8 : $i, X9 : $i]:
% 0.89/1.16         (((k3_subset_1 @ X9 @ (k3_subset_1 @ X9 @ X8)) = (X8))
% 0.89/1.16          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.89/1.16      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.89/1.16  thf('49', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))
% 0.89/1.16           = (k6_subset_1 @ X0 @ X1))),
% 0.89/1.16      inference('sup-', [status(thm)], ['47', '48'])).
% 0.89/1.16  thf('50', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 0.89/1.16           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 0.89/1.16      inference('sup-', [status(thm)], ['42', '43'])).
% 0.89/1.16  thf('51', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 0.89/1.16           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 0.89/1.16      inference('sup-', [status(thm)], ['42', '43'])).
% 0.89/1.16  thf('52', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))
% 0.89/1.16           = (k6_subset_1 @ X0 @ X1))),
% 0.89/1.16      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.89/1.16  thf('53', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 0.89/1.16           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 0.89/1.16      inference('sup-', [status(thm)], ['42', '43'])).
% 0.89/1.16  thf('54', plain, (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.89/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.16  thf('55', plain,
% 0.89/1.16      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.89/1.16         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X13)))
% 0.89/1.16          | ((X12) != (k7_setfam_1 @ X13 @ X14))
% 0.89/1.16          | (r2_hidden @ X15 @ X12)
% 0.89/1.16          | ~ (r2_hidden @ (k3_subset_1 @ X13 @ X15) @ X14)
% 0.89/1.16          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X13))
% 0.89/1.16          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X13))))),
% 0.89/1.16      inference('cnf', [status(esa)], [d8_setfam_1])).
% 0.89/1.16  thf('56', plain,
% 0.89/1.16      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.89/1.16         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X13)))
% 0.89/1.16          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X13))
% 0.89/1.16          | ~ (r2_hidden @ (k3_subset_1 @ X13 @ X15) @ X14)
% 0.89/1.16          | (r2_hidden @ X15 @ (k7_setfam_1 @ X13 @ X14))
% 0.89/1.16          | ~ (m1_subset_1 @ (k7_setfam_1 @ X13 @ X14) @ 
% 0.89/1.16               (k1_zfmisc_1 @ (k1_zfmisc_1 @ X13))))),
% 0.89/1.16      inference('simplify', [status(thm)], ['55'])).
% 0.89/1.16  thf('57', plain,
% 0.89/1.16      (![X0 : $i]:
% 0.89/1.16         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.89/1.16          | (r2_hidden @ X0 @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.89/1.16          | ~ (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ sk_B)
% 0.89/1.16          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.89/1.16          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 0.89/1.16      inference('sup-', [status(thm)], ['54', '56'])).
% 0.89/1.16  thf('58', plain,
% 0.89/1.16      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.89/1.16      inference('demod', [status(thm)], ['2', '3'])).
% 0.89/1.16  thf('59', plain, (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.89/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.16  thf('60', plain,
% 0.89/1.16      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.89/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.16  thf('61', plain,
% 0.89/1.16      (![X0 : $i]:
% 0.89/1.16         ((r2_hidden @ X0 @ k1_xboole_0)
% 0.89/1.16          | ~ (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ sk_B)
% 0.89/1.16          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.89/1.16      inference('demod', [status(thm)], ['57', '58', '59', '60'])).
% 0.89/1.16  thf('62', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.89/1.16      inference('simplify', [status(thm)], ['25'])).
% 0.89/1.16  thf('63', plain,
% 0.89/1.16      (![X0 : $i]:
% 0.89/1.16         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.89/1.16          | ~ (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ sk_B))),
% 0.89/1.16      inference('clc', [status(thm)], ['61', '62'])).
% 0.89/1.16  thf('64', plain,
% 0.89/1.16      (![X0 : $i]:
% 0.89/1.16         (~ (r2_hidden @ (k6_subset_1 @ sk_A @ (k6_subset_1 @ sk_A @ X0)) @ 
% 0.89/1.16             sk_B)
% 0.89/1.16          | ~ (m1_subset_1 @ (k6_subset_1 @ sk_A @ X0) @ (k1_zfmisc_1 @ sk_A)))),
% 0.89/1.16      inference('sup-', [status(thm)], ['53', '63'])).
% 0.89/1.16  thf('65', plain,
% 0.89/1.16      (![X6 : $i, X7 : $i]:
% 0.89/1.16         (m1_subset_1 @ (k6_subset_1 @ X6 @ X7) @ (k1_zfmisc_1 @ X6))),
% 0.89/1.16      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.89/1.16  thf('66', plain,
% 0.89/1.16      (![X0 : $i]:
% 0.89/1.16         ~ (r2_hidden @ (k6_subset_1 @ sk_A @ (k6_subset_1 @ sk_A @ X0)) @ sk_B)),
% 0.89/1.16      inference('demod', [status(thm)], ['64', '65'])).
% 0.89/1.16  thf('67', plain,
% 0.89/1.16      (![X0 : $i]: ~ (r2_hidden @ (k6_subset_1 @ sk_A @ X0) @ sk_B)),
% 0.89/1.16      inference('sup-', [status(thm)], ['52', '66'])).
% 0.89/1.16  thf('68', plain,
% 0.89/1.16      ((~ (r2_hidden @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A) @ sk_B)
% 0.89/1.16        | ((sk_B) = (k7_setfam_1 @ sk_A @ k1_xboole_0)))),
% 0.89/1.16      inference('sup-', [status(thm)], ['46', '67'])).
% 0.89/1.16  thf('69', plain, (((k1_xboole_0) = (k7_setfam_1 @ sk_A @ k1_xboole_0))),
% 0.89/1.16      inference('clc', [status(thm)], ['27', '28'])).
% 0.89/1.16  thf('70', plain,
% 0.89/1.16      ((~ (r2_hidden @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A) @ sk_B)
% 0.89/1.16        | ((sk_B) = (k1_xboole_0)))),
% 0.89/1.16      inference('demod', [status(thm)], ['68', '69'])).
% 0.89/1.16  thf('71', plain, (((sk_B) != (k1_xboole_0))),
% 0.89/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.16  thf('72', plain, (~ (r2_hidden @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A) @ sk_B)),
% 0.89/1.16      inference('simplify_reflect-', [status(thm)], ['70', '71'])).
% 0.89/1.16  thf('73', plain,
% 0.89/1.16      ((r2_hidden @ 
% 0.89/1.16        (k6_subset_1 @ sk_A @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A)) @ k1_xboole_0)),
% 0.89/1.16      inference('clc', [status(thm)], ['36', '72'])).
% 0.89/1.16  thf('74', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.89/1.16      inference('simplify', [status(thm)], ['25'])).
% 0.89/1.16  thf('75', plain, ($false), inference('sup-', [status(thm)], ['73', '74'])).
% 0.89/1.16  
% 0.89/1.16  % SZS output end Refutation
% 0.89/1.16  
% 0.89/1.17  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
