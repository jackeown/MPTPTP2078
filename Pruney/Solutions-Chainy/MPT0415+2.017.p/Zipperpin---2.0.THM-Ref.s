%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KBZX2mMmeN

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:11 EST 2020

% Result     : Theorem 0.78s
% Output     : Refutation 0.78s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 207 expanded)
%              Number of leaves         :   19 (  69 expanded)
%              Depth                    :   12
%              Number of atoms          :  696 (2096 expanded)
%              Number of equality atoms :   35 ( 155 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X14: $i,X15: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X14 ) ) ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) )
      | ( r2_hidden @ ( sk_D @ X10 @ X12 @ X11 ) @ X10 )
      | ( r2_hidden @ ( k3_subset_1 @ X11 @ ( sk_D @ X10 @ X12 @ X11 ) ) @ X12 )
      | ( X10
        = ( k7_setfam_1 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) ) ) ),
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
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('11',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) )
      | ( r2_hidden @ ( sk_D @ X10 @ X12 @ X11 ) @ X10 )
      | ( r2_hidden @ ( k3_subset_1 @ X11 @ ( sk_D @ X10 @ X12 @ X11 ) ) @ X12 )
      | ( X10
        = ( k7_setfam_1 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( k1_xboole_0
        = ( k7_setfam_1 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_D @ k1_xboole_0 @ X0 @ sk_A ) ) @ X0 )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ sk_A ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_A ) ) @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k7_setfam_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('14',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('15',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('17',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('18',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k1_xboole_0
      = ( k7_setfam_1 @ sk_A @ k1_xboole_0 ) )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_A ) ) @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('21',plain,
    ( k1_xboole_0
    = ( k7_setfam_1 @ sk_A @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) ) @ k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','21'])).

thf('23',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) ) @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) )
      | ( m1_subset_1 @ ( sk_D @ X10 @ X12 @ X11 ) @ ( k1_zfmisc_1 @ X11 ) )
      | ( X10
        = ( k7_setfam_1 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( sk_B
        = ( k7_setfam_1 @ sk_A @ X0 ) )
      | ( m1_subset_1 @ ( sk_D @ sk_B @ X0 @ sk_A ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( sk_B
      = ( k7_setfam_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('30',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X9 @ ( k3_subset_1 @ X9 @ X8 ) )
        = X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('31',plain,
    ( ( sk_B
      = ( k7_setfam_1 @ sk_A @ k1_xboole_0 ) )
    | ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) ) )
      = ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k7_setfam_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) )
      | ( X10
       != ( k7_setfam_1 @ X11 @ X12 ) )
      | ( r2_hidden @ X13 @ X10 )
      | ~ ( r2_hidden @ ( k3_subset_1 @ X11 @ X13 ) @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('34',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ X11 @ X13 ) @ X12 )
      | ( r2_hidden @ X13 @ ( k7_setfam_1 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ ( k7_setfam_1 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('37',plain,
    ( ( k7_setfam_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['35','36','37','38'])).

thf('40',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( r2_hidden @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) @ sk_B )
    | ( sk_B
      = ( k7_setfam_1 @ sk_A @ k1_xboole_0 ) )
    | ~ ( m1_subset_1 @ ( k3_subset_1 @ sk_A @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','41'])).

thf('43',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( sk_B
      = ( k7_setfam_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('44',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('45',plain,
    ( ( sk_B
      = ( k7_setfam_1 @ sk_A @ k1_xboole_0 ) )
    | ( m1_subset_1 @ ( k3_subset_1 @ sk_A @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( sk_B
      = ( k7_setfam_1 @ sk_A @ k1_xboole_0 ) )
    | ~ ( r2_hidden @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['42','45'])).

thf('47',plain,
    ( k1_xboole_0
    = ( k7_setfam_1 @ sk_A @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('48',plain,
    ( ( sk_B = k1_xboole_0 )
    | ~ ( r2_hidden @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ~ ( r2_hidden @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['48','49'])).

thf('51',plain,(
    r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) ) @ k1_xboole_0 ),
    inference(clc,[status(thm)],['24','50'])).

thf('52',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('53',plain,(
    $false ),
    inference('sup-',[status(thm)],['51','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KBZX2mMmeN
% 0.12/0.35  % Computer   : n014.cluster.edu
% 0.12/0.35  % Model      : x86_64 x86_64
% 0.12/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.35  % Memory     : 8042.1875MB
% 0.12/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.35  % CPULimit   : 60
% 0.12/0.35  % DateTime   : Tue Dec  1 12:28:52 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.36  % Running in FO mode
% 0.78/0.99  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.78/0.99  % Solved by: fo/fo7.sh
% 0.78/0.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.78/0.99  % done 696 iterations in 0.527s
% 0.78/0.99  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.78/0.99  % SZS output start Refutation
% 0.78/0.99  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.78/0.99  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.78/0.99  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.78/0.99  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.78/0.99  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.78/0.99  thf(sk_B_type, type, sk_B: $i).
% 0.78/0.99  thf(sk_A_type, type, sk_A: $i).
% 0.78/0.99  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.78/0.99  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.78/0.99  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.78/0.99  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.78/0.99  thf(t46_setfam_1, conjecture,
% 0.78/0.99    (![A:$i,B:$i]:
% 0.78/0.99     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.78/0.99       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.78/0.99            ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.78/0.99  thf(zf_stmt_0, negated_conjecture,
% 0.78/0.99    (~( ![A:$i,B:$i]:
% 0.78/0.99        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.78/0.99          ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.78/0.99               ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) )),
% 0.78/0.99    inference('cnf.neg', [status(esa)], [t46_setfam_1])).
% 0.78/0.99  thf('0', plain,
% 0.78/0.99      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf(dt_k7_setfam_1, axiom,
% 0.78/0.99    (![A:$i,B:$i]:
% 0.78/0.99     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.78/0.99       ( m1_subset_1 @
% 0.78/0.99         ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.78/0.99  thf('1', plain,
% 0.78/0.99      (![X14 : $i, X15 : $i]:
% 0.78/0.99         ((m1_subset_1 @ (k7_setfam_1 @ X14 @ X15) @ 
% 0.78/0.99           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X14)))
% 0.78/0.99          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X14))))),
% 0.78/0.99      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 0.78/0.99  thf('2', plain,
% 0.78/0.99      ((m1_subset_1 @ (k7_setfam_1 @ sk_A @ sk_B) @ 
% 0.78/0.99        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.78/0.99      inference('sup-', [status(thm)], ['0', '1'])).
% 0.78/0.99  thf('3', plain, (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf('4', plain,
% 0.78/0.99      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.78/0.99      inference('demod', [status(thm)], ['2', '3'])).
% 0.78/0.99  thf('5', plain,
% 0.78/0.99      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf(d8_setfam_1, axiom,
% 0.78/0.99    (![A:$i,B:$i]:
% 0.78/0.99     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.78/0.99       ( ![C:$i]:
% 0.78/0.99         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.78/0.99           ( ( ( C ) = ( k7_setfam_1 @ A @ B ) ) <=>
% 0.78/0.99             ( ![D:$i]:
% 0.78/0.99               ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.78/0.99                 ( ( r2_hidden @ D @ C ) <=>
% 0.78/0.99                   ( r2_hidden @ ( k3_subset_1 @ A @ D ) @ B ) ) ) ) ) ) ) ))).
% 0.78/0.99  thf('6', plain,
% 0.78/0.99      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.78/0.99         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X11)))
% 0.78/0.99          | (r2_hidden @ (sk_D @ X10 @ X12 @ X11) @ X10)
% 0.78/0.99          | (r2_hidden @ (k3_subset_1 @ X11 @ (sk_D @ X10 @ X12 @ X11)) @ X12)
% 0.78/0.99          | ((X10) = (k7_setfam_1 @ X11 @ X12))
% 0.78/0.99          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X11))))),
% 0.78/0.99      inference('cnf', [status(esa)], [d8_setfam_1])).
% 0.78/0.99  thf('7', plain,
% 0.78/0.99      (![X0 : $i]:
% 0.78/0.99         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.78/0.99          | ((sk_B) = (k7_setfam_1 @ sk_A @ X0))
% 0.78/0.99          | (r2_hidden @ (k3_subset_1 @ sk_A @ (sk_D @ sk_B @ X0 @ sk_A)) @ X0)
% 0.78/0.99          | (r2_hidden @ (sk_D @ sk_B @ X0 @ sk_A) @ sk_B))),
% 0.78/0.99      inference('sup-', [status(thm)], ['5', '6'])).
% 0.78/0.99  thf('8', plain,
% 0.78/0.99      (((r2_hidden @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A) @ sk_B)
% 0.78/0.99        | (r2_hidden @ 
% 0.78/0.99           (k3_subset_1 @ sk_A @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A)) @ 
% 0.78/0.99           k1_xboole_0)
% 0.78/0.99        | ((sk_B) = (k7_setfam_1 @ sk_A @ k1_xboole_0)))),
% 0.78/0.99      inference('sup-', [status(thm)], ['4', '7'])).
% 0.78/0.99  thf('9', plain,
% 0.78/0.99      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.78/0.99      inference('demod', [status(thm)], ['2', '3'])).
% 0.78/0.99  thf('10', plain,
% 0.78/0.99      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.78/0.99      inference('demod', [status(thm)], ['2', '3'])).
% 0.78/0.99  thf('11', plain,
% 0.78/0.99      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.78/0.99         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X11)))
% 0.78/0.99          | (r2_hidden @ (sk_D @ X10 @ X12 @ X11) @ X10)
% 0.78/0.99          | (r2_hidden @ (k3_subset_1 @ X11 @ (sk_D @ X10 @ X12 @ X11)) @ X12)
% 0.78/0.99          | ((X10) = (k7_setfam_1 @ X11 @ X12))
% 0.78/0.99          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X11))))),
% 0.78/0.99      inference('cnf', [status(esa)], [d8_setfam_1])).
% 0.78/0.99  thf('12', plain,
% 0.78/0.99      (![X0 : $i]:
% 0.78/0.99         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.78/0.99          | ((k1_xboole_0) = (k7_setfam_1 @ sk_A @ X0))
% 0.78/0.99          | (r2_hidden @ 
% 0.78/0.99             (k3_subset_1 @ sk_A @ (sk_D @ k1_xboole_0 @ X0 @ sk_A)) @ X0)
% 0.78/0.99          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ sk_A) @ k1_xboole_0))),
% 0.78/0.99      inference('sup-', [status(thm)], ['10', '11'])).
% 0.78/0.99  thf('13', plain,
% 0.78/0.99      (((r2_hidden @ (sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_A) @ k1_xboole_0)
% 0.78/0.99        | (r2_hidden @ 
% 0.78/0.99           (k3_subset_1 @ sk_A @ (sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_A)) @ 
% 0.78/0.99           k1_xboole_0)
% 0.78/0.99        | ((k1_xboole_0) = (k7_setfam_1 @ sk_A @ k1_xboole_0)))),
% 0.78/0.99      inference('sup-', [status(thm)], ['9', '12'])).
% 0.78/0.99  thf(t2_boole, axiom,
% 0.78/0.99    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.78/0.99  thf('14', plain,
% 0.78/0.99      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.78/0.99      inference('cnf', [status(esa)], [t2_boole])).
% 0.78/0.99  thf(t4_xboole_0, axiom,
% 0.78/0.99    (![A:$i,B:$i]:
% 0.78/0.99     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.78/0.99            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.78/0.99       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.78/0.99            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.78/0.99  thf('15', plain,
% 0.78/0.99      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.78/0.99         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.78/0.99          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.78/0.99      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.78/0.99  thf('16', plain,
% 0.78/0.99      (![X0 : $i, X1 : $i]:
% 0.78/0.99         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.78/0.99      inference('sup-', [status(thm)], ['14', '15'])).
% 0.78/0.99  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.78/0.99  thf('17', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 0.78/0.99      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.78/0.99  thf('18', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.78/0.99      inference('demod', [status(thm)], ['16', '17'])).
% 0.78/0.99  thf('19', plain,
% 0.78/0.99      ((((k1_xboole_0) = (k7_setfam_1 @ sk_A @ k1_xboole_0))
% 0.78/0.99        | (r2_hidden @ 
% 0.78/0.99           (k3_subset_1 @ sk_A @ (sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_A)) @ 
% 0.78/0.99           k1_xboole_0))),
% 0.78/0.99      inference('clc', [status(thm)], ['13', '18'])).
% 0.78/0.99  thf('20', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.78/0.99      inference('demod', [status(thm)], ['16', '17'])).
% 0.78/0.99  thf('21', plain, (((k1_xboole_0) = (k7_setfam_1 @ sk_A @ k1_xboole_0))),
% 0.78/0.99      inference('clc', [status(thm)], ['19', '20'])).
% 0.78/0.99  thf('22', plain,
% 0.78/0.99      (((r2_hidden @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A) @ sk_B)
% 0.78/0.99        | (r2_hidden @ 
% 0.78/0.99           (k3_subset_1 @ sk_A @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A)) @ 
% 0.78/0.99           k1_xboole_0)
% 0.78/0.99        | ((sk_B) = (k1_xboole_0)))),
% 0.78/0.99      inference('demod', [status(thm)], ['8', '21'])).
% 0.78/0.99  thf('23', plain, (((sk_B) != (k1_xboole_0))),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf('24', plain,
% 0.78/0.99      (((r2_hidden @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A) @ sk_B)
% 0.78/0.99        | (r2_hidden @ 
% 0.78/0.99           (k3_subset_1 @ sk_A @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A)) @ 
% 0.78/0.99           k1_xboole_0))),
% 0.78/0.99      inference('simplify_reflect-', [status(thm)], ['22', '23'])).
% 0.78/0.99  thf('25', plain,
% 0.78/0.99      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.78/0.99      inference('demod', [status(thm)], ['2', '3'])).
% 0.78/0.99  thf('26', plain,
% 0.78/0.99      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf('27', plain,
% 0.78/0.99      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.78/0.99         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X11)))
% 0.78/0.99          | (m1_subset_1 @ (sk_D @ X10 @ X12 @ X11) @ (k1_zfmisc_1 @ X11))
% 0.78/0.99          | ((X10) = (k7_setfam_1 @ X11 @ X12))
% 0.78/0.99          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X11))))),
% 0.78/0.99      inference('cnf', [status(esa)], [d8_setfam_1])).
% 0.78/0.99  thf('28', plain,
% 0.78/0.99      (![X0 : $i]:
% 0.78/0.99         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.78/0.99          | ((sk_B) = (k7_setfam_1 @ sk_A @ X0))
% 0.78/0.99          | (m1_subset_1 @ (sk_D @ sk_B @ X0 @ sk_A) @ (k1_zfmisc_1 @ sk_A)))),
% 0.78/0.99      inference('sup-', [status(thm)], ['26', '27'])).
% 0.78/0.99  thf('29', plain,
% 0.78/0.99      (((m1_subset_1 @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A) @ 
% 0.78/0.99         (k1_zfmisc_1 @ sk_A))
% 0.78/0.99        | ((sk_B) = (k7_setfam_1 @ sk_A @ k1_xboole_0)))),
% 0.78/0.99      inference('sup-', [status(thm)], ['25', '28'])).
% 0.78/0.99  thf(involutiveness_k3_subset_1, axiom,
% 0.78/0.99    (![A:$i,B:$i]:
% 0.78/0.99     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.78/0.99       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.78/0.99  thf('30', plain,
% 0.78/0.99      (![X8 : $i, X9 : $i]:
% 0.78/0.99         (((k3_subset_1 @ X9 @ (k3_subset_1 @ X9 @ X8)) = (X8))
% 0.78/0.99          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.78/0.99      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.78/0.99  thf('31', plain,
% 0.78/0.99      ((((sk_B) = (k7_setfam_1 @ sk_A @ k1_xboole_0))
% 0.78/0.99        | ((k3_subset_1 @ sk_A @ 
% 0.78/0.99            (k3_subset_1 @ sk_A @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A)))
% 0.78/0.99            = (sk_D @ sk_B @ k1_xboole_0 @ sk_A)))),
% 0.78/0.99      inference('sup-', [status(thm)], ['29', '30'])).
% 0.78/0.99  thf('32', plain, (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf('33', plain,
% 0.78/0.99      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.78/0.99         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X11)))
% 0.78/0.99          | ((X10) != (k7_setfam_1 @ X11 @ X12))
% 0.78/0.99          | (r2_hidden @ X13 @ X10)
% 0.78/0.99          | ~ (r2_hidden @ (k3_subset_1 @ X11 @ X13) @ X12)
% 0.78/0.99          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X11))
% 0.78/0.99          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X11))))),
% 0.78/0.99      inference('cnf', [status(esa)], [d8_setfam_1])).
% 0.78/0.99  thf('34', plain,
% 0.78/0.99      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.78/0.99         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X11)))
% 0.78/0.99          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X11))
% 0.78/0.99          | ~ (r2_hidden @ (k3_subset_1 @ X11 @ X13) @ X12)
% 0.78/0.99          | (r2_hidden @ X13 @ (k7_setfam_1 @ X11 @ X12))
% 0.78/0.99          | ~ (m1_subset_1 @ (k7_setfam_1 @ X11 @ X12) @ 
% 0.78/0.99               (k1_zfmisc_1 @ (k1_zfmisc_1 @ X11))))),
% 0.78/0.99      inference('simplify', [status(thm)], ['33'])).
% 0.78/0.99  thf('35', plain,
% 0.78/0.99      (![X0 : $i]:
% 0.78/0.99         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.78/0.99          | (r2_hidden @ X0 @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.78/0.99          | ~ (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ sk_B)
% 0.78/0.99          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.78/0.99          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 0.78/0.99      inference('sup-', [status(thm)], ['32', '34'])).
% 0.78/0.99  thf('36', plain,
% 0.78/0.99      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.78/0.99      inference('demod', [status(thm)], ['2', '3'])).
% 0.78/0.99  thf('37', plain, (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf('38', plain,
% 0.78/0.99      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf('39', plain,
% 0.78/0.99      (![X0 : $i]:
% 0.78/0.99         ((r2_hidden @ X0 @ k1_xboole_0)
% 0.78/0.99          | ~ (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ sk_B)
% 0.78/0.99          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.78/0.99      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 0.78/0.99  thf('40', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.78/0.99      inference('demod', [status(thm)], ['16', '17'])).
% 0.78/0.99  thf('41', plain,
% 0.78/0.99      (![X0 : $i]:
% 0.78/0.99         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.78/0.99          | ~ (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ sk_B))),
% 0.78/0.99      inference('clc', [status(thm)], ['39', '40'])).
% 0.78/0.99  thf('42', plain,
% 0.78/0.99      ((~ (r2_hidden @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A) @ sk_B)
% 0.78/0.99        | ((sk_B) = (k7_setfam_1 @ sk_A @ k1_xboole_0))
% 0.78/0.99        | ~ (m1_subset_1 @ 
% 0.78/0.99             (k3_subset_1 @ sk_A @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A)) @ 
% 0.78/0.99             (k1_zfmisc_1 @ sk_A)))),
% 0.78/0.99      inference('sup-', [status(thm)], ['31', '41'])).
% 0.78/0.99  thf('43', plain,
% 0.78/0.99      (((m1_subset_1 @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A) @ 
% 0.78/0.99         (k1_zfmisc_1 @ sk_A))
% 0.78/0.99        | ((sk_B) = (k7_setfam_1 @ sk_A @ k1_xboole_0)))),
% 0.78/0.99      inference('sup-', [status(thm)], ['25', '28'])).
% 0.78/0.99  thf(dt_k3_subset_1, axiom,
% 0.78/0.99    (![A:$i,B:$i]:
% 0.78/0.99     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.78/0.99       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.78/0.99  thf('44', plain,
% 0.78/0.99      (![X6 : $i, X7 : $i]:
% 0.78/0.99         ((m1_subset_1 @ (k3_subset_1 @ X6 @ X7) @ (k1_zfmisc_1 @ X6))
% 0.78/0.99          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.78/0.99      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.78/0.99  thf('45', plain,
% 0.78/0.99      ((((sk_B) = (k7_setfam_1 @ sk_A @ k1_xboole_0))
% 0.78/0.99        | (m1_subset_1 @ 
% 0.78/0.99           (k3_subset_1 @ sk_A @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A)) @ 
% 0.78/0.99           (k1_zfmisc_1 @ sk_A)))),
% 0.78/0.99      inference('sup-', [status(thm)], ['43', '44'])).
% 0.78/0.99  thf('46', plain,
% 0.78/0.99      ((((sk_B) = (k7_setfam_1 @ sk_A @ k1_xboole_0))
% 0.78/0.99        | ~ (r2_hidden @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A) @ sk_B))),
% 0.78/0.99      inference('clc', [status(thm)], ['42', '45'])).
% 0.78/0.99  thf('47', plain, (((k1_xboole_0) = (k7_setfam_1 @ sk_A @ k1_xboole_0))),
% 0.78/0.99      inference('clc', [status(thm)], ['19', '20'])).
% 0.78/0.99  thf('48', plain,
% 0.78/0.99      ((((sk_B) = (k1_xboole_0))
% 0.78/0.99        | ~ (r2_hidden @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A) @ sk_B))),
% 0.78/0.99      inference('demod', [status(thm)], ['46', '47'])).
% 0.78/0.99  thf('49', plain, (((sk_B) != (k1_xboole_0))),
% 0.78/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.99  thf('50', plain, (~ (r2_hidden @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A) @ sk_B)),
% 0.78/0.99      inference('simplify_reflect-', [status(thm)], ['48', '49'])).
% 0.78/0.99  thf('51', plain,
% 0.78/0.99      ((r2_hidden @ 
% 0.78/0.99        (k3_subset_1 @ sk_A @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A)) @ k1_xboole_0)),
% 0.78/0.99      inference('clc', [status(thm)], ['24', '50'])).
% 0.78/0.99  thf('52', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.78/0.99      inference('demod', [status(thm)], ['16', '17'])).
% 0.78/0.99  thf('53', plain, ($false), inference('sup-', [status(thm)], ['51', '52'])).
% 0.78/0.99  
% 0.78/0.99  % SZS output end Refutation
% 0.78/0.99  
% 0.78/1.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
