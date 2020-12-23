%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jz6yFB9bfY

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:13 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 524 expanded)
%              Number of leaves         :   23 ( 165 expanded)
%              Depth                    :   17
%              Number of atoms          :  963 (6569 expanded)
%              Number of equality atoms :   47 ( 461 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t12_tops_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( B != k1_xboole_0 )
       => ( ( k5_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
          = ( k3_subset_1 @ A @ ( k6_setfam_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ( ( B != k1_xboole_0 )
         => ( ( k5_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
            = ( k3_subset_1 @ A @ ( k6_setfam_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t12_tops_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('1',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(dt_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

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

thf('4',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X4 ) ) )
      | ( r2_hidden @ ( sk_D @ X3 @ X5 @ X4 ) @ X3 )
      | ( r2_hidden @ ( k3_subset_1 @ X4 @ ( sk_D @ X3 @ X5 @ X4 ) ) @ X5 )
      | ( X3
        = ( k7_setfam_1 @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) )
      | ( ( k7_setfam_1 @ X0 @ k1_xboole_0 )
        = ( k7_setfam_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X0 @ ( sk_D @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) @ X1 @ X0 ) ) @ X1 )
      | ( r2_hidden @ ( sk_D @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) @ X1 @ X0 ) @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( r2_hidden @ ( sk_D @ ( k7_setfam_1 @ sk_A @ k1_xboole_0 ) @ sk_B @ sk_A ) @ ( k7_setfam_1 @ sk_A @ k1_xboole_0 ) )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_D @ ( k7_setfam_1 @ sk_A @ k1_xboole_0 ) @ sk_B @ sk_A ) ) @ sk_B )
    | ( ( k7_setfam_1 @ sk_A @ k1_xboole_0 )
      = ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
        = B ) ) )).

thf('8',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k7_setfam_1 @ X12 @ ( k7_setfam_1 @ X12 @ X11 ) )
        = X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k7_setfam_1])).

thf('9',plain,
    ( ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('12',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t11_tops_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( B != k1_xboole_0 )
       => ( ( k6_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
          = ( k3_subset_1 @ A @ ( k5_setfam_1 @ A @ B ) ) ) ) ) )).

thf('13',plain,(
    ! [X21: $i,X22: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( ( k6_setfam_1 @ X22 @ ( k7_setfam_1 @ X22 @ X21 ) )
        = ( k3_subset_1 @ X22 @ ( k5_setfam_1 @ X22 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[t11_tops_2])).

thf('14',plain,
    ( ( ( k6_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) )
      = ( k3_subset_1 @ sk_A @ ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ) )
    | ( ( k7_setfam_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf('16',plain,
    ( ( ( k6_setfam_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ sk_A @ ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ) )
    | ( ( k7_setfam_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(dt_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('18',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k5_setfam_1 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_setfam_1])).

thf('19',plain,(
    m1_subset_1 @ ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_subset_1 @ X1 @ ( k3_subset_1 @ X1 @ X0 ) )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('21',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ) )
    = ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( k3_subset_1 @ sk_A @ ( k6_setfam_1 @ sk_A @ sk_B ) )
      = ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) )
    | ( ( k7_setfam_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','21'])).

thf('23',plain,(
    ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) )
 != ( k3_subset_1 @ sk_A @ ( k6_setfam_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( k7_setfam_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k7_setfam_1 @ sk_A @ k1_xboole_0 )
    = sk_B ),
    inference(demod,[status(thm)],['9','24'])).

thf('26',plain,
    ( ( k7_setfam_1 @ sk_A @ k1_xboole_0 )
    = sk_B ),
    inference(demod,[status(thm)],['9','24'])).

thf('27',plain,
    ( ( k7_setfam_1 @ sk_A @ k1_xboole_0 )
    = sk_B ),
    inference(demod,[status(thm)],['9','24'])).

thf('28',plain,
    ( ( k7_setfam_1 @ sk_A @ k1_xboole_0 )
    = sk_B ),
    inference(demod,[status(thm)],['9','24'])).

thf('29',plain,
    ( ( k7_setfam_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['22','23'])).

thf('30',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_D @ sk_B @ sk_B @ sk_A ) ) @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','25','26','27','28','29'])).

thf('31',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_D @ sk_B @ sk_B @ sk_A ) ) @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('34',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('35',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X4 ) ) )
      | ( X3
       != ( k7_setfam_1 @ X4 @ X5 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X4 @ X6 ) @ X5 )
      | ~ ( r2_hidden @ X6 @ X3 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('37',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X4 ) ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( r2_hidden @ X6 @ ( k7_setfam_1 @ X4 @ X5 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X4 @ X6 ) @ X5 )
      | ~ ( m1_subset_1 @ ( k7_setfam_1 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X4 ) ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ ( k7_setfam_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k7_setfam_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ ( k7_setfam_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('42',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( m1_subset_1 @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) ) )
      | ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['40','43'])).

thf('45',plain,
    ( ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ ( k7_setfam_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k7_setfam_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['22','23'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ ( sk_D @ sk_B @ sk_B @ sk_A ) ) ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X4 ) ) )
      | ( m1_subset_1 @ ( sk_D @ X3 @ X5 @ X4 ) @ ( k1_zfmisc_1 @ X4 ) )
      | ( X3
        = ( k7_setfam_1 @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( sk_B
        = ( k7_setfam_1 @ sk_A @ X0 ) )
      | ( m1_subset_1 @ ( sk_D @ sk_B @ X0 @ sk_A ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_B @ ( k7_setfam_1 @ sk_A @ k1_xboole_0 ) @ sk_A ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( sk_B
      = ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,
    ( ( k7_setfam_1 @ sk_A @ k1_xboole_0 )
    = sk_B ),
    inference(demod,[status(thm)],['9','24'])).

thf('56',plain,
    ( ( k7_setfam_1 @ sk_A @ k1_xboole_0 )
    = sk_B ),
    inference(demod,[status(thm)],['9','24'])).

thf('57',plain,
    ( ( k7_setfam_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['22','23'])).

thf('58',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55','56','57'])).

thf('59',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_subset_1 @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_subset_1 @ X1 @ ( k3_subset_1 @ X1 @ X0 ) )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('62',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ ( sk_D @ sk_B @ sk_B @ sk_A ) ) )
    = ( sk_D @ sk_B @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('65',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ k1_xboole_0 )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_D @ sk_B @ sk_B @ sk_A ) ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('66',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( r1_tarski @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('67',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ k1_xboole_0 )
    | ~ ( r1_tarski @ k1_xboole_0 @ ( k3_subset_1 @ sk_A @ ( sk_D @ sk_B @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('69',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('70',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    r2_hidden @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['67','70'])).

thf('72',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( r1_tarski @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('73',plain,(
    ~ ( r1_tarski @ k1_xboole_0 @ ( sk_D @ sk_B @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('75',plain,(
    $false ),
    inference(demod,[status(thm)],['73','74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jz6yFB9bfY
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:23:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.38/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.62  % Solved by: fo/fo7.sh
% 0.38/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.62  % done 352 iterations in 0.184s
% 0.38/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.62  % SZS output start Refutation
% 0.38/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.62  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.38/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.62  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.38/0.62  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.38/0.62  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.38/0.62  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.38/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.62  thf(t12_tops_2, conjecture,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.38/0.62       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.38/0.62         ( ( k5_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) =
% 0.38/0.62           ( k3_subset_1 @ A @ ( k6_setfam_1 @ A @ B ) ) ) ) ))).
% 0.38/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.62    (~( ![A:$i,B:$i]:
% 0.38/0.62        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.38/0.62          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.38/0.62            ( ( k5_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) =
% 0.38/0.62              ( k3_subset_1 @ A @ ( k6_setfam_1 @ A @ B ) ) ) ) ) )),
% 0.38/0.62    inference('cnf.neg', [status(esa)], [t12_tops_2])).
% 0.38/0.62  thf('0', plain,
% 0.38/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf(t4_subset_1, axiom,
% 0.38/0.62    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.38/0.62  thf('1', plain,
% 0.38/0.62      (![X2 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X2))),
% 0.38/0.62      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.38/0.62  thf(dt_k7_setfam_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.38/0.62       ( m1_subset_1 @
% 0.38/0.62         ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.38/0.62  thf('2', plain,
% 0.38/0.62      (![X9 : $i, X10 : $i]:
% 0.38/0.62         ((m1_subset_1 @ (k7_setfam_1 @ X9 @ X10) @ 
% 0.38/0.62           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X9)))
% 0.38/0.62          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X9))))),
% 0.38/0.62      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 0.38/0.62  thf('3', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (m1_subset_1 @ (k7_setfam_1 @ X0 @ k1_xboole_0) @ 
% 0.38/0.62          (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.62  thf(d8_setfam_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.38/0.62       ( ![C:$i]:
% 0.38/0.62         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.38/0.62           ( ( ( C ) = ( k7_setfam_1 @ A @ B ) ) <=>
% 0.38/0.62             ( ![D:$i]:
% 0.38/0.62               ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.62                 ( ( r2_hidden @ D @ C ) <=>
% 0.38/0.62                   ( r2_hidden @ ( k3_subset_1 @ A @ D ) @ B ) ) ) ) ) ) ) ))).
% 0.38/0.62  thf('4', plain,
% 0.38/0.62      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.38/0.62         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X4)))
% 0.38/0.62          | (r2_hidden @ (sk_D @ X3 @ X5 @ X4) @ X3)
% 0.38/0.62          | (r2_hidden @ (k3_subset_1 @ X4 @ (sk_D @ X3 @ X5 @ X4)) @ X5)
% 0.38/0.62          | ((X3) = (k7_setfam_1 @ X4 @ X5))
% 0.38/0.62          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X4))))),
% 0.38/0.62      inference('cnf', [status(esa)], [d8_setfam_1])).
% 0.38/0.62  thf('5', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))
% 0.38/0.62          | ((k7_setfam_1 @ X0 @ k1_xboole_0) = (k7_setfam_1 @ X0 @ X1))
% 0.38/0.62          | (r2_hidden @ 
% 0.38/0.62             (k3_subset_1 @ X0 @ 
% 0.38/0.62              (sk_D @ (k7_setfam_1 @ X0 @ k1_xboole_0) @ X1 @ X0)) @ 
% 0.38/0.62             X1)
% 0.38/0.62          | (r2_hidden @ (sk_D @ (k7_setfam_1 @ X0 @ k1_xboole_0) @ X1 @ X0) @ 
% 0.38/0.62             (k7_setfam_1 @ X0 @ k1_xboole_0)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['3', '4'])).
% 0.38/0.62  thf('6', plain,
% 0.38/0.62      (((r2_hidden @ 
% 0.38/0.62         (sk_D @ (k7_setfam_1 @ sk_A @ k1_xboole_0) @ sk_B @ sk_A) @ 
% 0.38/0.62         (k7_setfam_1 @ sk_A @ k1_xboole_0))
% 0.38/0.62        | (r2_hidden @ 
% 0.38/0.62           (k3_subset_1 @ sk_A @ 
% 0.38/0.62            (sk_D @ (k7_setfam_1 @ sk_A @ k1_xboole_0) @ sk_B @ sk_A)) @ 
% 0.38/0.62           sk_B)
% 0.38/0.62        | ((k7_setfam_1 @ sk_A @ k1_xboole_0) = (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['0', '5'])).
% 0.38/0.62  thf('7', plain,
% 0.38/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf(involutiveness_k7_setfam_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.38/0.62       ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) = ( B ) ) ))).
% 0.38/0.62  thf('8', plain,
% 0.38/0.62      (![X11 : $i, X12 : $i]:
% 0.38/0.62         (((k7_setfam_1 @ X12 @ (k7_setfam_1 @ X12 @ X11)) = (X11))
% 0.38/0.62          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X12))))),
% 0.38/0.62      inference('cnf', [status(esa)], [involutiveness_k7_setfam_1])).
% 0.38/0.62  thf('9', plain,
% 0.38/0.62      (((k7_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.38/0.62      inference('sup-', [status(thm)], ['7', '8'])).
% 0.38/0.62  thf('10', plain,
% 0.38/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('11', plain,
% 0.38/0.62      (![X9 : $i, X10 : $i]:
% 0.38/0.62         ((m1_subset_1 @ (k7_setfam_1 @ X9 @ X10) @ 
% 0.38/0.62           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X9)))
% 0.38/0.62          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X9))))),
% 0.38/0.62      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 0.38/0.62  thf('12', plain,
% 0.38/0.62      ((m1_subset_1 @ (k7_setfam_1 @ sk_A @ sk_B) @ 
% 0.38/0.62        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['10', '11'])).
% 0.38/0.62  thf(t11_tops_2, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.38/0.62       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.38/0.62         ( ( k6_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) =
% 0.38/0.62           ( k3_subset_1 @ A @ ( k5_setfam_1 @ A @ B ) ) ) ) ))).
% 0.38/0.62  thf('13', plain,
% 0.38/0.62      (![X21 : $i, X22 : $i]:
% 0.38/0.62         (((X21) = (k1_xboole_0))
% 0.38/0.62          | ((k6_setfam_1 @ X22 @ (k7_setfam_1 @ X22 @ X21))
% 0.38/0.62              = (k3_subset_1 @ X22 @ (k5_setfam_1 @ X22 @ X21)))
% 0.38/0.62          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X22))))),
% 0.38/0.62      inference('cnf', [status(esa)], [t11_tops_2])).
% 0.38/0.62  thf('14', plain,
% 0.38/0.62      ((((k6_setfam_1 @ sk_A @ 
% 0.38/0.62          (k7_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)))
% 0.38/0.62          = (k3_subset_1 @ sk_A @ 
% 0.38/0.62             (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B))))
% 0.38/0.62        | ((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['12', '13'])).
% 0.38/0.62  thf('15', plain,
% 0.38/0.62      (((k7_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.38/0.62      inference('sup-', [status(thm)], ['7', '8'])).
% 0.38/0.62  thf('16', plain,
% 0.38/0.62      ((((k6_setfam_1 @ sk_A @ sk_B)
% 0.38/0.62          = (k3_subset_1 @ sk_A @ 
% 0.38/0.62             (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B))))
% 0.38/0.62        | ((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.38/0.62      inference('demod', [status(thm)], ['14', '15'])).
% 0.38/0.62  thf('17', plain,
% 0.38/0.62      ((m1_subset_1 @ (k7_setfam_1 @ sk_A @ sk_B) @ 
% 0.38/0.62        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['10', '11'])).
% 0.38/0.62  thf(dt_k5_setfam_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.38/0.62       ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.38/0.62  thf('18', plain,
% 0.38/0.62      (![X7 : $i, X8 : $i]:
% 0.38/0.62         ((m1_subset_1 @ (k5_setfam_1 @ X7 @ X8) @ (k1_zfmisc_1 @ X7))
% 0.38/0.62          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X7))))),
% 0.38/0.62      inference('cnf', [status(esa)], [dt_k5_setfam_1])).
% 0.38/0.62  thf('19', plain,
% 0.38/0.62      ((m1_subset_1 @ (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)) @ 
% 0.38/0.62        (k1_zfmisc_1 @ sk_A))),
% 0.38/0.62      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.62  thf(involutiveness_k3_subset_1, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.62       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.38/0.62  thf('20', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         (((k3_subset_1 @ X1 @ (k3_subset_1 @ X1 @ X0)) = (X0))
% 0.38/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.38/0.62      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.38/0.62  thf('21', plain,
% 0.38/0.62      (((k3_subset_1 @ sk_A @ 
% 0.38/0.62         (k3_subset_1 @ sk_A @ 
% 0.38/0.62          (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B))))
% 0.38/0.62         = (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['19', '20'])).
% 0.38/0.62  thf('22', plain,
% 0.38/0.62      ((((k3_subset_1 @ sk_A @ (k6_setfam_1 @ sk_A @ sk_B))
% 0.38/0.62          = (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)))
% 0.38/0.62        | ((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.38/0.62      inference('sup+', [status(thm)], ['16', '21'])).
% 0.38/0.62  thf('23', plain,
% 0.38/0.62      (((k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.38/0.62         != (k3_subset_1 @ sk_A @ (k6_setfam_1 @ sk_A @ sk_B)))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('24', plain, (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.38/0.62      inference('simplify_reflect-', [status(thm)], ['22', '23'])).
% 0.38/0.62  thf('25', plain, (((k7_setfam_1 @ sk_A @ k1_xboole_0) = (sk_B))),
% 0.38/0.62      inference('demod', [status(thm)], ['9', '24'])).
% 0.38/0.62  thf('26', plain, (((k7_setfam_1 @ sk_A @ k1_xboole_0) = (sk_B))),
% 0.38/0.62      inference('demod', [status(thm)], ['9', '24'])).
% 0.38/0.62  thf('27', plain, (((k7_setfam_1 @ sk_A @ k1_xboole_0) = (sk_B))),
% 0.38/0.62      inference('demod', [status(thm)], ['9', '24'])).
% 0.38/0.62  thf('28', plain, (((k7_setfam_1 @ sk_A @ k1_xboole_0) = (sk_B))),
% 0.38/0.62      inference('demod', [status(thm)], ['9', '24'])).
% 0.38/0.62  thf('29', plain, (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.38/0.62      inference('simplify_reflect-', [status(thm)], ['22', '23'])).
% 0.38/0.62  thf('30', plain,
% 0.38/0.62      (((r2_hidden @ (sk_D @ sk_B @ sk_B @ sk_A) @ sk_B)
% 0.38/0.62        | (r2_hidden @ (k3_subset_1 @ sk_A @ (sk_D @ sk_B @ sk_B @ sk_A)) @ 
% 0.38/0.62           sk_B)
% 0.38/0.62        | ((sk_B) = (k1_xboole_0)))),
% 0.38/0.62      inference('demod', [status(thm)], ['6', '25', '26', '27', '28', '29'])).
% 0.38/0.62  thf('31', plain, (((sk_B) != (k1_xboole_0))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('32', plain,
% 0.38/0.62      (((r2_hidden @ (sk_D @ sk_B @ sk_B @ sk_A) @ sk_B)
% 0.38/0.62        | (r2_hidden @ (k3_subset_1 @ sk_A @ (sk_D @ sk_B @ sk_B @ sk_A)) @ 
% 0.38/0.62           sk_B))),
% 0.38/0.62      inference('simplify_reflect-', [status(thm)], ['30', '31'])).
% 0.38/0.62  thf('33', plain,
% 0.38/0.62      ((m1_subset_1 @ (k7_setfam_1 @ sk_A @ sk_B) @ 
% 0.38/0.62        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['10', '11'])).
% 0.38/0.62  thf('34', plain,
% 0.38/0.62      (![X9 : $i, X10 : $i]:
% 0.38/0.62         ((m1_subset_1 @ (k7_setfam_1 @ X9 @ X10) @ 
% 0.38/0.62           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X9)))
% 0.38/0.62          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X9))))),
% 0.38/0.62      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 0.38/0.62  thf('35', plain,
% 0.38/0.62      ((m1_subset_1 @ (k7_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)) @ 
% 0.38/0.62        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['33', '34'])).
% 0.38/0.62  thf('36', plain,
% 0.38/0.62      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.38/0.62         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X4)))
% 0.38/0.62          | ((X3) != (k7_setfam_1 @ X4 @ X5))
% 0.38/0.62          | (r2_hidden @ (k3_subset_1 @ X4 @ X6) @ X5)
% 0.38/0.62          | ~ (r2_hidden @ X6 @ X3)
% 0.38/0.62          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X4))
% 0.38/0.62          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X4))))),
% 0.38/0.62      inference('cnf', [status(esa)], [d8_setfam_1])).
% 0.38/0.62  thf('37', plain,
% 0.38/0.62      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.38/0.62         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X4)))
% 0.38/0.62          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X4))
% 0.38/0.62          | ~ (r2_hidden @ X6 @ (k7_setfam_1 @ X4 @ X5))
% 0.38/0.62          | (r2_hidden @ (k3_subset_1 @ X4 @ X6) @ X5)
% 0.38/0.62          | ~ (m1_subset_1 @ (k7_setfam_1 @ X4 @ X5) @ 
% 0.38/0.62               (k1_zfmisc_1 @ (k1_zfmisc_1 @ X4))))),
% 0.38/0.62      inference('simplify', [status(thm)], ['36'])).
% 0.38/0.62  thf('38', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.38/0.62          | ~ (r2_hidden @ X0 @ 
% 0.38/0.62               (k7_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)))
% 0.38/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.38/0.62          | ~ (m1_subset_1 @ (k7_setfam_1 @ sk_A @ sk_B) @ 
% 0.38/0.62               (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['35', '37'])).
% 0.38/0.62  thf('39', plain,
% 0.38/0.62      ((m1_subset_1 @ (k7_setfam_1 @ sk_A @ sk_B) @ 
% 0.38/0.62        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['10', '11'])).
% 0.38/0.62  thf('40', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.38/0.62          | ~ (r2_hidden @ X0 @ 
% 0.38/0.62               (k7_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)))
% 0.38/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.38/0.62      inference('demod', [status(thm)], ['38', '39'])).
% 0.38/0.62  thf('41', plain,
% 0.38/0.62      ((m1_subset_1 @ (k7_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)) @ 
% 0.38/0.62        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['33', '34'])).
% 0.38/0.62  thf(t4_subset, axiom,
% 0.38/0.62    (![A:$i,B:$i,C:$i]:
% 0.38/0.62     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.38/0.62       ( m1_subset_1 @ A @ C ) ))).
% 0.38/0.62  thf('42', plain,
% 0.38/0.62      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.38/0.62         (~ (r2_hidden @ X16 @ X17)
% 0.38/0.62          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 0.38/0.62          | (m1_subset_1 @ X16 @ X18))),
% 0.38/0.62      inference('cnf', [status(esa)], [t4_subset])).
% 0.38/0.62  thf('43', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.38/0.62          | ~ (r2_hidden @ X0 @ 
% 0.38/0.62               (k7_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['41', '42'])).
% 0.38/0.62  thf('44', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (r2_hidden @ X0 @ 
% 0.38/0.62             (k7_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)))
% 0.38/0.62          | (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ 
% 0.38/0.62             (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.38/0.62      inference('clc', [status(thm)], ['40', '43'])).
% 0.38/0.62  thf('45', plain,
% 0.38/0.62      (((k7_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.38/0.62      inference('sup-', [status(thm)], ['7', '8'])).
% 0.38/0.62  thf('46', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (r2_hidden @ X0 @ sk_B)
% 0.38/0.62          | (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ 
% 0.38/0.62             (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.38/0.62      inference('demod', [status(thm)], ['44', '45'])).
% 0.38/0.62  thf('47', plain, (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.38/0.62      inference('simplify_reflect-', [status(thm)], ['22', '23'])).
% 0.38/0.62  thf('48', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (r2_hidden @ X0 @ sk_B)
% 0.38/0.62          | (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ k1_xboole_0))),
% 0.38/0.62      inference('demod', [status(thm)], ['46', '47'])).
% 0.38/0.62  thf('49', plain,
% 0.38/0.62      (((r2_hidden @ (sk_D @ sk_B @ sk_B @ sk_A) @ sk_B)
% 0.38/0.62        | (r2_hidden @ 
% 0.38/0.62           (k3_subset_1 @ sk_A @ 
% 0.38/0.62            (k3_subset_1 @ sk_A @ (sk_D @ sk_B @ sk_B @ sk_A))) @ 
% 0.38/0.62           k1_xboole_0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['32', '48'])).
% 0.38/0.62  thf('50', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (m1_subset_1 @ (k7_setfam_1 @ X0 @ k1_xboole_0) @ 
% 0.38/0.62          (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.62  thf('51', plain,
% 0.38/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('52', plain,
% 0.38/0.62      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.38/0.62         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X4)))
% 0.38/0.62          | (m1_subset_1 @ (sk_D @ X3 @ X5 @ X4) @ (k1_zfmisc_1 @ X4))
% 0.38/0.62          | ((X3) = (k7_setfam_1 @ X4 @ X5))
% 0.38/0.62          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X4))))),
% 0.38/0.62      inference('cnf', [status(esa)], [d8_setfam_1])).
% 0.38/0.62  thf('53', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.38/0.62          | ((sk_B) = (k7_setfam_1 @ sk_A @ X0))
% 0.38/0.62          | (m1_subset_1 @ (sk_D @ sk_B @ X0 @ sk_A) @ (k1_zfmisc_1 @ sk_A)))),
% 0.38/0.62      inference('sup-', [status(thm)], ['51', '52'])).
% 0.38/0.62  thf('54', plain,
% 0.38/0.62      (((m1_subset_1 @ 
% 0.38/0.62         (sk_D @ sk_B @ (k7_setfam_1 @ sk_A @ k1_xboole_0) @ sk_A) @ 
% 0.38/0.62         (k1_zfmisc_1 @ sk_A))
% 0.38/0.62        | ((sk_B) = (k7_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ k1_xboole_0))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['50', '53'])).
% 0.38/0.62  thf('55', plain, (((k7_setfam_1 @ sk_A @ k1_xboole_0) = (sk_B))),
% 0.38/0.62      inference('demod', [status(thm)], ['9', '24'])).
% 0.38/0.62  thf('56', plain, (((k7_setfam_1 @ sk_A @ k1_xboole_0) = (sk_B))),
% 0.38/0.62      inference('demod', [status(thm)], ['9', '24'])).
% 0.38/0.62  thf('57', plain, (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.38/0.62      inference('simplify_reflect-', [status(thm)], ['22', '23'])).
% 0.38/0.62  thf('58', plain,
% 0.38/0.62      (((m1_subset_1 @ (sk_D @ sk_B @ sk_B @ sk_A) @ (k1_zfmisc_1 @ sk_A))
% 0.38/0.62        | ((sk_B) = (k1_xboole_0)))),
% 0.38/0.62      inference('demod', [status(thm)], ['54', '55', '56', '57'])).
% 0.38/0.62  thf('59', plain, (((sk_B) != (k1_xboole_0))),
% 0.38/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.62  thf('60', plain,
% 0.38/0.62      ((m1_subset_1 @ (sk_D @ sk_B @ sk_B @ sk_A) @ (k1_zfmisc_1 @ sk_A))),
% 0.38/0.62      inference('simplify_reflect-', [status(thm)], ['58', '59'])).
% 0.38/0.62  thf('61', plain,
% 0.38/0.62      (![X0 : $i, X1 : $i]:
% 0.38/0.62         (((k3_subset_1 @ X1 @ (k3_subset_1 @ X1 @ X0)) = (X0))
% 0.38/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.38/0.62      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.38/0.62  thf('62', plain,
% 0.38/0.62      (((k3_subset_1 @ sk_A @ 
% 0.38/0.62         (k3_subset_1 @ sk_A @ (sk_D @ sk_B @ sk_B @ sk_A)))
% 0.38/0.62         = (sk_D @ sk_B @ sk_B @ sk_A))),
% 0.38/0.62      inference('sup-', [status(thm)], ['60', '61'])).
% 0.38/0.62  thf('63', plain,
% 0.38/0.62      (((r2_hidden @ (sk_D @ sk_B @ sk_B @ sk_A) @ sk_B)
% 0.38/0.62        | (r2_hidden @ (sk_D @ sk_B @ sk_B @ sk_A) @ k1_xboole_0))),
% 0.38/0.62      inference('demod', [status(thm)], ['49', '62'])).
% 0.38/0.62  thf('64', plain,
% 0.38/0.62      (![X0 : $i]:
% 0.38/0.62         (~ (r2_hidden @ X0 @ sk_B)
% 0.38/0.62          | (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ k1_xboole_0))),
% 0.38/0.62      inference('demod', [status(thm)], ['46', '47'])).
% 0.38/0.62  thf('65', plain,
% 0.38/0.62      (((r2_hidden @ (sk_D @ sk_B @ sk_B @ sk_A) @ k1_xboole_0)
% 0.38/0.62        | (r2_hidden @ (k3_subset_1 @ sk_A @ (sk_D @ sk_B @ sk_B @ sk_A)) @ 
% 0.38/0.62           k1_xboole_0))),
% 0.38/0.62      inference('sup-', [status(thm)], ['63', '64'])).
% 0.38/0.62  thf(t7_ordinal1, axiom,
% 0.38/0.62    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.62  thf('66', plain,
% 0.38/0.62      (![X19 : $i, X20 : $i]:
% 0.38/0.62         (~ (r2_hidden @ X19 @ X20) | ~ (r1_tarski @ X20 @ X19))),
% 0.38/0.62      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.38/0.62  thf('67', plain,
% 0.38/0.62      (((r2_hidden @ (sk_D @ sk_B @ sk_B @ sk_A) @ k1_xboole_0)
% 0.38/0.62        | ~ (r1_tarski @ k1_xboole_0 @ 
% 0.38/0.62             (k3_subset_1 @ sk_A @ (sk_D @ sk_B @ sk_B @ sk_A))))),
% 0.38/0.62      inference('sup-', [status(thm)], ['65', '66'])).
% 0.38/0.62  thf('68', plain,
% 0.38/0.62      (![X2 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X2))),
% 0.38/0.62      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.38/0.62  thf(t3_subset, axiom,
% 0.38/0.62    (![A:$i,B:$i]:
% 0.38/0.62     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.62  thf('69', plain,
% 0.38/0.62      (![X13 : $i, X14 : $i]:
% 0.38/0.62         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.38/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.62  thf('70', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.38/0.62      inference('sup-', [status(thm)], ['68', '69'])).
% 0.38/0.62  thf('71', plain, ((r2_hidden @ (sk_D @ sk_B @ sk_B @ sk_A) @ k1_xboole_0)),
% 0.38/0.62      inference('demod', [status(thm)], ['67', '70'])).
% 0.38/0.62  thf('72', plain,
% 0.38/0.62      (![X19 : $i, X20 : $i]:
% 0.38/0.62         (~ (r2_hidden @ X19 @ X20) | ~ (r1_tarski @ X20 @ X19))),
% 0.38/0.62      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.38/0.62  thf('73', plain, (~ (r1_tarski @ k1_xboole_0 @ (sk_D @ sk_B @ sk_B @ sk_A))),
% 0.38/0.62      inference('sup-', [status(thm)], ['71', '72'])).
% 0.38/0.62  thf('74', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.38/0.62      inference('sup-', [status(thm)], ['68', '69'])).
% 0.38/0.62  thf('75', plain, ($false), inference('demod', [status(thm)], ['73', '74'])).
% 0.38/0.62  
% 0.38/0.62  % SZS output end Refutation
% 0.38/0.62  
% 0.38/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
