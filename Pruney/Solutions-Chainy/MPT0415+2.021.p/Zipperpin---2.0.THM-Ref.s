%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YScTU8gnFj

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 143 expanded)
%              Number of leaves         :   25 (  52 expanded)
%              Depth                    :   16
%              Number of atoms          :  776 (1406 expanded)
%              Number of equality atoms :   47 ( 131 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

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

thf('1',plain,(
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

thf('2',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) )
      | ( r2_hidden @ ( sk_D @ X15 @ X17 @ X16 ) @ X15 )
      | ( r2_hidden @ ( k3_subset_1 @ X16 @ ( sk_D @ X15 @ X17 @ X16 ) ) @ X17 )
      | ( X15
        = ( k7_setfam_1 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( sk_B
        = ( k7_setfam_1 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_D @ sk_B @ X0 @ sk_A ) ) @ X0 )
      | ( r2_hidden @ ( sk_D @ sk_B @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_D @ sk_B @ sk_B @ sk_A ) ) @ sk_B )
    | ( sk_B
      = ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,
    ( ( k7_setfam_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_D @ sk_B @ sk_B @ sk_A ) ) @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_D @ sk_B @ sk_B @ sk_A ) ) @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k7_setfam_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) )
      | ( X15
       != ( k7_setfam_1 @ X16 @ X17 ) )
      | ( r2_hidden @ X18 @ X15 )
      | ~ ( r2_hidden @ ( k3_subset_1 @ X16 @ X18 ) @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('11',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ X16 @ X18 ) @ X17 )
      | ( r2_hidden @ X18 @ ( k7_setfam_1 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ ( k7_setfam_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('13',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('14',plain,
    ( ( k7_setfam_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['12','13','14','15'])).

thf('17',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ sk_B )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) )
      | ( m1_subset_1 @ ( sk_D @ X15 @ X17 @ X16 ) @ ( k1_zfmisc_1 @ X16 ) )
      | ( X15
        = ( k7_setfam_1 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( sk_B
        = ( k7_setfam_1 @ sk_A @ X0 ) )
      | ( m1_subset_1 @ ( sk_D @ sk_B @ X0 @ sk_A ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( sk_B
      = ( k7_setfam_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,
    ( ( k7_setfam_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','26'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('28',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X8 ) @ X10 )
      | ~ ( r2_hidden @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('29',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ sk_B )
    | ( r1_tarski @ ( k1_tarski @ ( sk_D @ sk_B @ sk_B @ sk_A ) ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('30',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('31',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ sk_B )
    | ( ( k1_tarski @ ( sk_D @ sk_B @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('32',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X12 != X11 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X12 ) @ ( k1_tarski @ X11 ) )
       != ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('33',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X11 ) @ ( k1_tarski @ X11 ) )
     != ( k1_tarski @ X11 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('35',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('37',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ X4 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('38',plain,(
    ! [X11: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X11 ) ) ),
    inference(demod,[status(thm)],['33','36','37'])).

thf('39',plain,(
    r2_hidden @ ( sk_D @ sk_B @ sk_B @ sk_A ) @ sk_B ),
    inference(clc,[status(thm)],['31','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
        = B ) ) )).

thf('41',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k7_setfam_1 @ X20 @ ( k7_setfam_1 @ X20 @ X19 ) )
        = X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k7_setfam_1])).

thf('42',plain,
    ( ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k7_setfam_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k7_setfam_1 @ sk_A @ k1_xboole_0 )
    = sk_B ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) )
      | ( X15
       != ( k7_setfam_1 @ X16 @ X17 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X16 @ X18 ) @ X17 )
      | ~ ( r2_hidden @ X18 @ X15 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('46',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r2_hidden @ X18 @ ( k7_setfam_1 @ X16 @ X17 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X16 @ X18 ) @ X17 )
      | ~ ( m1_subset_1 @ ( k7_setfam_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['44','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( k7_setfam_1 @ sk_A @ k1_xboole_0 )
    = sk_B ),
    inference(demod,[status(thm)],['42','43'])).

thf('50',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['47','48','49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('53',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( m1_subset_1 @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['51','54'])).

thf('56',plain,(
    r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_D @ sk_B @ sk_B @ sk_A ) ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['39','55'])).

thf('57',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X8 ) @ X10 )
      | ~ ( r2_hidden @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('58',plain,(
    r1_tarski @ ( k1_tarski @ ( k3_subset_1 @ sk_A @ ( sk_D @ sk_B @ sk_B @ sk_A ) ) ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('60',plain,
    ( ( k1_tarski @ ( k3_subset_1 @ sk_A @ ( sk_D @ sk_B @ sk_B @ sk_A ) ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X11: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X11 ) ) ),
    inference(demod,[status(thm)],['33','36','37'])).

thf('62',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    $false ),
    inference(simplify,[status(thm)],['62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YScTU8gnFj
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:20:59 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 230 iterations in 0.075s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.53  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.21/0.53  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.21/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.53  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(t46_setfam_1, conjecture,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.53       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.53            ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i,B:$i]:
% 0.21/0.53        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.53          ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.53               ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t46_setfam_1])).
% 0.21/0.53  thf('0', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(d8_setfam_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.53       ( ![C:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.53           ( ( ( C ) = ( k7_setfam_1 @ A @ B ) ) <=>
% 0.21/0.53             ( ![D:$i]:
% 0.21/0.54               ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.54                 ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.54                   ( r2_hidden @ ( k3_subset_1 @ A @ D ) @ B ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf('2', plain,
% 0.21/0.54      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16)))
% 0.21/0.54          | (r2_hidden @ (sk_D @ X15 @ X17 @ X16) @ X15)
% 0.21/0.54          | (r2_hidden @ (k3_subset_1 @ X16 @ (sk_D @ X15 @ X17 @ X16)) @ X17)
% 0.21/0.54          | ((X15) = (k7_setfam_1 @ X16 @ X17))
% 0.21/0.54          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16))))),
% 0.21/0.54      inference('cnf', [status(esa)], [d8_setfam_1])).
% 0.21/0.54  thf('3', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.21/0.54          | ((sk_B) = (k7_setfam_1 @ sk_A @ X0))
% 0.21/0.54          | (r2_hidden @ (k3_subset_1 @ sk_A @ (sk_D @ sk_B @ X0 @ sk_A)) @ X0)
% 0.21/0.54          | (r2_hidden @ (sk_D @ sk_B @ X0 @ sk_A) @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.54  thf('4', plain,
% 0.21/0.54      (((r2_hidden @ (sk_D @ sk_B @ sk_B @ sk_A) @ sk_B)
% 0.21/0.54        | (r2_hidden @ (k3_subset_1 @ sk_A @ (sk_D @ sk_B @ sk_B @ sk_A)) @ 
% 0.21/0.54           sk_B)
% 0.21/0.54        | ((sk_B) = (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['0', '3'])).
% 0.21/0.54  thf('5', plain, (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('6', plain,
% 0.21/0.54      (((r2_hidden @ (sk_D @ sk_B @ sk_B @ sk_A) @ sk_B)
% 0.21/0.54        | (r2_hidden @ (k3_subset_1 @ sk_A @ (sk_D @ sk_B @ sk_B @ sk_A)) @ 
% 0.21/0.54           sk_B)
% 0.21/0.54        | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.54      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.54  thf('7', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('8', plain,
% 0.21/0.54      (((r2_hidden @ (sk_D @ sk_B @ sk_B @ sk_A) @ sk_B)
% 0.21/0.54        | (r2_hidden @ (k3_subset_1 @ sk_A @ (sk_D @ sk_B @ sk_B @ sk_A)) @ 
% 0.21/0.54           sk_B))),
% 0.21/0.54      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 0.21/0.54  thf('9', plain, (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('10', plain,
% 0.21/0.54      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16)))
% 0.21/0.54          | ((X15) != (k7_setfam_1 @ X16 @ X17))
% 0.21/0.54          | (r2_hidden @ X18 @ X15)
% 0.21/0.54          | ~ (r2_hidden @ (k3_subset_1 @ X16 @ X18) @ X17)
% 0.21/0.54          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X16))
% 0.21/0.54          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16))))),
% 0.21/0.54      inference('cnf', [status(esa)], [d8_setfam_1])).
% 0.21/0.54  thf('11', plain,
% 0.21/0.54      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16)))
% 0.21/0.54          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X16))
% 0.21/0.54          | ~ (r2_hidden @ (k3_subset_1 @ X16 @ X18) @ X17)
% 0.21/0.54          | (r2_hidden @ X18 @ (k7_setfam_1 @ X16 @ X17))
% 0.21/0.54          | ~ (m1_subset_1 @ (k7_setfam_1 @ X16 @ X17) @ 
% 0.21/0.54               (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16))))),
% 0.21/0.54      inference('simplify', [status(thm)], ['10'])).
% 0.21/0.54  thf('12', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.21/0.54          | (r2_hidden @ X0 @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.21/0.54          | ~ (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ sk_B)
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.54          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['9', '11'])).
% 0.21/0.54  thf(t4_subset_1, axiom,
% 0.21/0.54    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.54  thf('13', plain,
% 0.21/0.54      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 0.21/0.54      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.54  thf('14', plain, (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('15', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('16', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((r2_hidden @ X0 @ k1_xboole_0)
% 0.21/0.54          | ~ (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ sk_B)
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.54      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 0.21/0.54  thf('17', plain,
% 0.21/0.54      (((r2_hidden @ (sk_D @ sk_B @ sk_B @ sk_A) @ sk_B)
% 0.21/0.54        | ~ (m1_subset_1 @ (sk_D @ sk_B @ sk_B @ sk_A) @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.54        | (r2_hidden @ (sk_D @ sk_B @ sk_B @ sk_A) @ k1_xboole_0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['8', '16'])).
% 0.21/0.54  thf('18', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('19', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('20', plain,
% 0.21/0.54      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16)))
% 0.21/0.54          | (m1_subset_1 @ (sk_D @ X15 @ X17 @ X16) @ (k1_zfmisc_1 @ X16))
% 0.21/0.54          | ((X15) = (k7_setfam_1 @ X16 @ X17))
% 0.21/0.54          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16))))),
% 0.21/0.54      inference('cnf', [status(esa)], [d8_setfam_1])).
% 0.21/0.54  thf('21', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.21/0.54          | ((sk_B) = (k7_setfam_1 @ sk_A @ X0))
% 0.21/0.54          | (m1_subset_1 @ (sk_D @ sk_B @ X0 @ sk_A) @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.54  thf('22', plain,
% 0.21/0.54      (((m1_subset_1 @ (sk_D @ sk_B @ sk_B @ sk_A) @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.54        | ((sk_B) = (k7_setfam_1 @ sk_A @ sk_B)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['18', '21'])).
% 0.21/0.54  thf('23', plain, (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('24', plain,
% 0.21/0.54      (((m1_subset_1 @ (sk_D @ sk_B @ sk_B @ sk_A) @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.54        | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.54      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.54  thf('25', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('26', plain,
% 0.21/0.54      ((m1_subset_1 @ (sk_D @ sk_B @ sk_B @ sk_A) @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.54      inference('simplify_reflect-', [status(thm)], ['24', '25'])).
% 0.21/0.54  thf('27', plain,
% 0.21/0.54      (((r2_hidden @ (sk_D @ sk_B @ sk_B @ sk_A) @ sk_B)
% 0.21/0.54        | (r2_hidden @ (sk_D @ sk_B @ sk_B @ sk_A) @ k1_xboole_0))),
% 0.21/0.54      inference('demod', [status(thm)], ['17', '26'])).
% 0.21/0.54  thf(l1_zfmisc_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.21/0.54  thf('28', plain,
% 0.21/0.54      (![X8 : $i, X10 : $i]:
% 0.21/0.54         ((r1_tarski @ (k1_tarski @ X8) @ X10) | ~ (r2_hidden @ X8 @ X10))),
% 0.21/0.54      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.21/0.54  thf('29', plain,
% 0.21/0.54      (((r2_hidden @ (sk_D @ sk_B @ sk_B @ sk_A) @ sk_B)
% 0.21/0.54        | (r1_tarski @ (k1_tarski @ (sk_D @ sk_B @ sk_B @ sk_A)) @ k1_xboole_0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.54  thf(t3_xboole_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.54  thf('30', plain,
% 0.21/0.54      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.21/0.54  thf('31', plain,
% 0.21/0.54      (((r2_hidden @ (sk_D @ sk_B @ sk_B @ sk_A) @ sk_B)
% 0.21/0.54        | ((k1_tarski @ (sk_D @ sk_B @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.54  thf(t20_zfmisc_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.21/0.54         ( k1_tarski @ A ) ) <=>
% 0.21/0.54       ( ( A ) != ( B ) ) ))).
% 0.21/0.54  thf('32', plain,
% 0.21/0.54      (![X11 : $i, X12 : $i]:
% 0.21/0.54         (((X12) != (X11))
% 0.21/0.54          | ((k4_xboole_0 @ (k1_tarski @ X12) @ (k1_tarski @ X11))
% 0.21/0.54              != (k1_tarski @ X12)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.21/0.54  thf('33', plain,
% 0.21/0.54      (![X11 : $i]:
% 0.21/0.54         ((k4_xboole_0 @ (k1_tarski @ X11) @ (k1_tarski @ X11))
% 0.21/0.54           != (k1_tarski @ X11))),
% 0.21/0.54      inference('simplify', [status(thm)], ['32'])).
% 0.21/0.54  thf(idempotence_k3_xboole_0, axiom,
% 0.21/0.54    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.21/0.54  thf('34', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.21/0.54      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.21/0.54  thf(t100_xboole_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.54  thf('35', plain,
% 0.21/0.54      (![X1 : $i, X2 : $i]:
% 0.21/0.54         ((k4_xboole_0 @ X1 @ X2)
% 0.21/0.54           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.54  thf('36', plain,
% 0.21/0.54      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.21/0.54      inference('sup+', [status(thm)], ['34', '35'])).
% 0.21/0.54  thf(t92_xboole_1, axiom,
% 0.21/0.54    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.54  thf('37', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ X4) = (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.21/0.54  thf('38', plain, (![X11 : $i]: ((k1_xboole_0) != (k1_tarski @ X11))),
% 0.21/0.54      inference('demod', [status(thm)], ['33', '36', '37'])).
% 0.21/0.54  thf('39', plain, ((r2_hidden @ (sk_D @ sk_B @ sk_B @ sk_A) @ sk_B)),
% 0.21/0.54      inference('clc', [status(thm)], ['31', '38'])).
% 0.21/0.54  thf('40', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(involutiveness_k7_setfam_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.54       ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) = ( B ) ) ))).
% 0.21/0.54  thf('41', plain,
% 0.21/0.54      (![X19 : $i, X20 : $i]:
% 0.21/0.54         (((k7_setfam_1 @ X20 @ (k7_setfam_1 @ X20 @ X19)) = (X19))
% 0.21/0.54          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X20))))),
% 0.21/0.54      inference('cnf', [status(esa)], [involutiveness_k7_setfam_1])).
% 0.21/0.54  thf('42', plain,
% 0.21/0.54      (((k7_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.54  thf('43', plain, (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('44', plain, (((k7_setfam_1 @ sk_A @ k1_xboole_0) = (sk_B))),
% 0.21/0.54      inference('demod', [status(thm)], ['42', '43'])).
% 0.21/0.54  thf('45', plain,
% 0.21/0.54      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16)))
% 0.21/0.54          | ((X15) != (k7_setfam_1 @ X16 @ X17))
% 0.21/0.54          | (r2_hidden @ (k3_subset_1 @ X16 @ X18) @ X17)
% 0.21/0.54          | ~ (r2_hidden @ X18 @ X15)
% 0.21/0.54          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X16))
% 0.21/0.54          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16))))),
% 0.21/0.54      inference('cnf', [status(esa)], [d8_setfam_1])).
% 0.21/0.54  thf('46', plain,
% 0.21/0.54      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16)))
% 0.21/0.54          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X16))
% 0.21/0.54          | ~ (r2_hidden @ X18 @ (k7_setfam_1 @ X16 @ X17))
% 0.21/0.54          | (r2_hidden @ (k3_subset_1 @ X16 @ X18) @ X17)
% 0.21/0.54          | ~ (m1_subset_1 @ (k7_setfam_1 @ X16 @ X17) @ 
% 0.21/0.54               (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16))))),
% 0.21/0.54      inference('simplify', [status(thm)], ['45'])).
% 0.21/0.54  thf('47', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.21/0.54          | (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ k1_xboole_0)
% 0.21/0.54          | ~ (r2_hidden @ X0 @ (k7_setfam_1 @ sk_A @ k1_xboole_0))
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.54          | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['44', '46'])).
% 0.21/0.54  thf('48', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('49', plain, (((k7_setfam_1 @ sk_A @ k1_xboole_0) = (sk_B))),
% 0.21/0.54      inference('demod', [status(thm)], ['42', '43'])).
% 0.21/0.54  thf('50', plain,
% 0.21/0.54      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 0.21/0.54      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.54  thf('51', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ k1_xboole_0)
% 0.21/0.54          | ~ (r2_hidden @ X0 @ sk_B)
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.54      inference('demod', [status(thm)], ['47', '48', '49', '50'])).
% 0.21/0.54  thf('52', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(t4_subset, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.21/0.54       ( m1_subset_1 @ A @ C ) ))).
% 0.21/0.54  thf('53', plain,
% 0.21/0.54      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X21 @ X22)
% 0.21/0.54          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 0.21/0.54          | (m1_subset_1 @ X21 @ X23))),
% 0.21/0.54      inference('cnf', [status(esa)], [t4_subset])).
% 0.21/0.54  thf('54', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.54  thf('55', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X0 @ sk_B)
% 0.21/0.54          | (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ k1_xboole_0))),
% 0.21/0.54      inference('clc', [status(thm)], ['51', '54'])).
% 0.21/0.54  thf('56', plain,
% 0.21/0.54      ((r2_hidden @ (k3_subset_1 @ sk_A @ (sk_D @ sk_B @ sk_B @ sk_A)) @ 
% 0.21/0.54        k1_xboole_0)),
% 0.21/0.54      inference('sup-', [status(thm)], ['39', '55'])).
% 0.21/0.54  thf('57', plain,
% 0.21/0.54      (![X8 : $i, X10 : $i]:
% 0.21/0.54         ((r1_tarski @ (k1_tarski @ X8) @ X10) | ~ (r2_hidden @ X8 @ X10))),
% 0.21/0.54      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.21/0.54  thf('58', plain,
% 0.21/0.54      ((r1_tarski @ 
% 0.21/0.54        (k1_tarski @ (k3_subset_1 @ sk_A @ (sk_D @ sk_B @ sk_B @ sk_A))) @ 
% 0.21/0.54        k1_xboole_0)),
% 0.21/0.54      inference('sup-', [status(thm)], ['56', '57'])).
% 0.21/0.54  thf('59', plain,
% 0.21/0.54      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.21/0.54  thf('60', plain,
% 0.21/0.54      (((k1_tarski @ (k3_subset_1 @ sk_A @ (sk_D @ sk_B @ sk_B @ sk_A)))
% 0.21/0.54         = (k1_xboole_0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['58', '59'])).
% 0.21/0.54  thf('61', plain, (![X11 : $i]: ((k1_xboole_0) != (k1_tarski @ X11))),
% 0.21/0.54      inference('demod', [status(thm)], ['33', '36', '37'])).
% 0.21/0.54  thf('62', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['60', '61'])).
% 0.21/0.54  thf('63', plain, ($false), inference('simplify', [status(thm)], ['62'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
