%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dh7URW0Xi1

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:11 EST 2020

% Result     : Theorem 1.00s
% Output     : Refutation 1.00s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 194 expanded)
%              Number of leaves         :   17 (  62 expanded)
%              Depth                    :   12
%              Number of atoms          :  684 (2024 expanded)
%              Number of equality atoms :   39 ( 179 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X11 @ X10 ) @ X9 )
      | ( r2_hidden @ ( k3_subset_1 @ X10 @ ( sk_D @ X9 @ X11 @ X10 ) ) @ X11 )
      | ( X9
        = ( k7_setfam_1 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X11 @ X10 ) @ X9 )
      | ( r2_hidden @ ( k3_subset_1 @ X10 @ ( sk_D @ X9 @ X11 @ X10 ) ) @ X11 )
      | ( X9
        = ( k7_setfam_1 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) ) ) ),
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

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('14',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('15',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('16',plain,(
    ! [X3: $i,X4: $i] :
      ~ ( r2_hidden @ X3 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k1_xboole_0
      = ( k7_setfam_1 @ sk_A @ k1_xboole_0 ) )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_A ) ) @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['13','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('20',plain,
    ( k1_xboole_0
    = ( k7_setfam_1 @ sk_A @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) ) @ k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','20'])).

thf('22',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) ) @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) )
      | ( m1_subset_1 @ ( sk_D @ X9 @ X11 @ X10 ) @ ( k1_zfmisc_1 @ X10 ) )
      | ( X9
        = ( k7_setfam_1 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( sk_B
        = ( k7_setfam_1 @ sk_A @ X0 ) )
      | ( m1_subset_1 @ ( sk_D @ sk_B @ X0 @ sk_A ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( sk_B
      = ( k7_setfam_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('29',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_subset_1 @ X8 @ ( k3_subset_1 @ X8 @ X7 ) )
        = X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('30',plain,
    ( ( sk_B
      = ( k7_setfam_1 @ sk_A @ k1_xboole_0 ) )
    | ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) ) )
      = ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k7_setfam_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) )
      | ( X9
       != ( k7_setfam_1 @ X10 @ X11 ) )
      | ( r2_hidden @ X12 @ X9 )
      | ~ ( r2_hidden @ ( k3_subset_1 @ X10 @ X12 ) @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('33',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ X10 @ X12 ) @ X11 )
      | ( r2_hidden @ X12 @ ( k7_setfam_1 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ ( k7_setfam_1 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('36',plain,
    ( ( k7_setfam_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['34','35','36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( r2_hidden @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) @ sk_B )
    | ( sk_B
      = ( k7_setfam_1 @ sk_A @ k1_xboole_0 ) )
    | ~ ( m1_subset_1 @ ( k3_subset_1 @ sk_A @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','40'])).

thf('42',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( sk_B
      = ( k7_setfam_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('43',plain,(
    ! [X5: $i,X6: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X5 @ X6 ) @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('44',plain,
    ( ( sk_B
      = ( k7_setfam_1 @ sk_A @ k1_xboole_0 ) )
    | ( m1_subset_1 @ ( k3_subset_1 @ sk_A @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_B
      = ( k7_setfam_1 @ sk_A @ k1_xboole_0 ) )
    | ~ ( r2_hidden @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['41','44'])).

thf('46',plain,
    ( k1_xboole_0
    = ( k7_setfam_1 @ sk_A @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('47',plain,
    ( ( sk_B = k1_xboole_0 )
    | ~ ( r2_hidden @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ~ ( r2_hidden @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['47','48'])).

thf('50',plain,(
    r2_hidden @ ( k3_subset_1 @ sk_A @ ( sk_D @ sk_B @ k1_xboole_0 @ sk_A ) ) @ k1_xboole_0 ),
    inference(clc,[status(thm)],['23','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('52',plain,(
    $false ),
    inference('sup-',[status(thm)],['50','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dh7URW0Xi1
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:31:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.00/1.20  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.00/1.20  % Solved by: fo/fo7.sh
% 1.00/1.20  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.00/1.20  % done 716 iterations in 0.739s
% 1.00/1.20  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.00/1.20  % SZS output start Refutation
% 1.00/1.20  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.00/1.20  thf(sk_B_type, type, sk_B: $i).
% 1.00/1.20  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.00/1.20  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.00/1.20  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.00/1.20  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.00/1.20  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.00/1.20  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.00/1.20  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 1.00/1.20  thf(sk_A_type, type, sk_A: $i).
% 1.00/1.20  thf(t46_setfam_1, conjecture,
% 1.00/1.20    (![A:$i,B:$i]:
% 1.00/1.20     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.00/1.20       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.00/1.20            ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 1.00/1.20  thf(zf_stmt_0, negated_conjecture,
% 1.00/1.20    (~( ![A:$i,B:$i]:
% 1.00/1.20        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.00/1.20          ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.00/1.20               ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) )),
% 1.00/1.20    inference('cnf.neg', [status(esa)], [t46_setfam_1])).
% 1.00/1.20  thf('0', plain,
% 1.00/1.20      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf(dt_k7_setfam_1, axiom,
% 1.00/1.20    (![A:$i,B:$i]:
% 1.00/1.20     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.00/1.20       ( m1_subset_1 @
% 1.00/1.20         ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 1.00/1.20  thf('1', plain,
% 1.00/1.20      (![X13 : $i, X14 : $i]:
% 1.00/1.20         ((m1_subset_1 @ (k7_setfam_1 @ X13 @ X14) @ 
% 1.00/1.20           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X13)))
% 1.00/1.20          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X13))))),
% 1.00/1.20      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 1.00/1.20  thf('2', plain,
% 1.00/1.20      ((m1_subset_1 @ (k7_setfam_1 @ sk_A @ sk_B) @ 
% 1.00/1.20        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 1.00/1.20      inference('sup-', [status(thm)], ['0', '1'])).
% 1.00/1.20  thf('3', plain, (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf('4', plain,
% 1.00/1.20      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 1.00/1.20      inference('demod', [status(thm)], ['2', '3'])).
% 1.00/1.20  thf('5', plain,
% 1.00/1.20      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf(d8_setfam_1, axiom,
% 1.00/1.20    (![A:$i,B:$i]:
% 1.00/1.20     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.00/1.20       ( ![C:$i]:
% 1.00/1.20         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.00/1.20           ( ( ( C ) = ( k7_setfam_1 @ A @ B ) ) <=>
% 1.00/1.20             ( ![D:$i]:
% 1.00/1.20               ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 1.00/1.20                 ( ( r2_hidden @ D @ C ) <=>
% 1.00/1.20                   ( r2_hidden @ ( k3_subset_1 @ A @ D ) @ B ) ) ) ) ) ) ) ))).
% 1.00/1.20  thf('6', plain,
% 1.00/1.20      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.00/1.20         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X10)))
% 1.00/1.20          | (r2_hidden @ (sk_D @ X9 @ X11 @ X10) @ X9)
% 1.00/1.20          | (r2_hidden @ (k3_subset_1 @ X10 @ (sk_D @ X9 @ X11 @ X10)) @ X11)
% 1.00/1.20          | ((X9) = (k7_setfam_1 @ X10 @ X11))
% 1.00/1.20          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X10))))),
% 1.00/1.20      inference('cnf', [status(esa)], [d8_setfam_1])).
% 1.00/1.20  thf('7', plain,
% 1.00/1.20      (![X0 : $i]:
% 1.00/1.20         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 1.00/1.20          | ((sk_B) = (k7_setfam_1 @ sk_A @ X0))
% 1.00/1.20          | (r2_hidden @ (k3_subset_1 @ sk_A @ (sk_D @ sk_B @ X0 @ sk_A)) @ X0)
% 1.00/1.20          | (r2_hidden @ (sk_D @ sk_B @ X0 @ sk_A) @ sk_B))),
% 1.00/1.20      inference('sup-', [status(thm)], ['5', '6'])).
% 1.00/1.20  thf('8', plain,
% 1.00/1.20      (((r2_hidden @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A) @ sk_B)
% 1.00/1.20        | (r2_hidden @ 
% 1.00/1.20           (k3_subset_1 @ sk_A @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A)) @ 
% 1.00/1.20           k1_xboole_0)
% 1.00/1.20        | ((sk_B) = (k7_setfam_1 @ sk_A @ k1_xboole_0)))),
% 1.00/1.20      inference('sup-', [status(thm)], ['4', '7'])).
% 1.00/1.20  thf('9', plain,
% 1.00/1.20      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 1.00/1.20      inference('demod', [status(thm)], ['2', '3'])).
% 1.00/1.20  thf('10', plain,
% 1.00/1.20      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 1.00/1.20      inference('demod', [status(thm)], ['2', '3'])).
% 1.00/1.20  thf('11', plain,
% 1.00/1.20      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.00/1.20         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X10)))
% 1.00/1.20          | (r2_hidden @ (sk_D @ X9 @ X11 @ X10) @ X9)
% 1.00/1.20          | (r2_hidden @ (k3_subset_1 @ X10 @ (sk_D @ X9 @ X11 @ X10)) @ X11)
% 1.00/1.20          | ((X9) = (k7_setfam_1 @ X10 @ X11))
% 1.00/1.20          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X10))))),
% 1.00/1.20      inference('cnf', [status(esa)], [d8_setfam_1])).
% 1.00/1.20  thf('12', plain,
% 1.00/1.20      (![X0 : $i]:
% 1.00/1.20         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 1.00/1.20          | ((k1_xboole_0) = (k7_setfam_1 @ sk_A @ X0))
% 1.00/1.20          | (r2_hidden @ 
% 1.00/1.20             (k3_subset_1 @ sk_A @ (sk_D @ k1_xboole_0 @ X0 @ sk_A)) @ X0)
% 1.00/1.20          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ sk_A) @ k1_xboole_0))),
% 1.00/1.20      inference('sup-', [status(thm)], ['10', '11'])).
% 1.00/1.20  thf('13', plain,
% 1.00/1.20      (((r2_hidden @ (sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_A) @ k1_xboole_0)
% 1.00/1.20        | (r2_hidden @ 
% 1.00/1.20           (k3_subset_1 @ sk_A @ (sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_A)) @ 
% 1.00/1.20           k1_xboole_0)
% 1.00/1.20        | ((k1_xboole_0) = (k7_setfam_1 @ sk_A @ k1_xboole_0)))),
% 1.00/1.20      inference('sup-', [status(thm)], ['9', '12'])).
% 1.00/1.20  thf(t113_zfmisc_1, axiom,
% 1.00/1.20    (![A:$i,B:$i]:
% 1.00/1.20     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.00/1.20       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.00/1.20  thf('14', plain,
% 1.00/1.20      (![X1 : $i, X2 : $i]:
% 1.00/1.20         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 1.00/1.20      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.00/1.20  thf('15', plain,
% 1.00/1.20      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.00/1.20      inference('simplify', [status(thm)], ['14'])).
% 1.00/1.20  thf(t152_zfmisc_1, axiom,
% 1.00/1.20    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 1.00/1.20  thf('16', plain,
% 1.00/1.20      (![X3 : $i, X4 : $i]: ~ (r2_hidden @ X3 @ (k2_zfmisc_1 @ X3 @ X4))),
% 1.00/1.20      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 1.00/1.20  thf('17', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.00/1.20      inference('sup-', [status(thm)], ['15', '16'])).
% 1.00/1.20  thf('18', plain,
% 1.00/1.20      ((((k1_xboole_0) = (k7_setfam_1 @ sk_A @ k1_xboole_0))
% 1.00/1.20        | (r2_hidden @ 
% 1.00/1.20           (k3_subset_1 @ sk_A @ (sk_D @ k1_xboole_0 @ k1_xboole_0 @ sk_A)) @ 
% 1.00/1.20           k1_xboole_0))),
% 1.00/1.20      inference('clc', [status(thm)], ['13', '17'])).
% 1.00/1.20  thf('19', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.00/1.20      inference('sup-', [status(thm)], ['15', '16'])).
% 1.00/1.20  thf('20', plain, (((k1_xboole_0) = (k7_setfam_1 @ sk_A @ k1_xboole_0))),
% 1.00/1.20      inference('clc', [status(thm)], ['18', '19'])).
% 1.00/1.20  thf('21', plain,
% 1.00/1.20      (((r2_hidden @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A) @ sk_B)
% 1.00/1.20        | (r2_hidden @ 
% 1.00/1.20           (k3_subset_1 @ sk_A @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A)) @ 
% 1.00/1.20           k1_xboole_0)
% 1.00/1.20        | ((sk_B) = (k1_xboole_0)))),
% 1.00/1.20      inference('demod', [status(thm)], ['8', '20'])).
% 1.00/1.20  thf('22', plain, (((sk_B) != (k1_xboole_0))),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf('23', plain,
% 1.00/1.20      (((r2_hidden @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A) @ sk_B)
% 1.00/1.20        | (r2_hidden @ 
% 1.00/1.20           (k3_subset_1 @ sk_A @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A)) @ 
% 1.00/1.20           k1_xboole_0))),
% 1.00/1.20      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 1.00/1.20  thf('24', plain,
% 1.00/1.20      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 1.00/1.20      inference('demod', [status(thm)], ['2', '3'])).
% 1.00/1.20  thf('25', plain,
% 1.00/1.20      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf('26', plain,
% 1.00/1.20      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.00/1.20         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X10)))
% 1.00/1.20          | (m1_subset_1 @ (sk_D @ X9 @ X11 @ X10) @ (k1_zfmisc_1 @ X10))
% 1.00/1.20          | ((X9) = (k7_setfam_1 @ X10 @ X11))
% 1.00/1.20          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X10))))),
% 1.00/1.20      inference('cnf', [status(esa)], [d8_setfam_1])).
% 1.00/1.20  thf('27', plain,
% 1.00/1.20      (![X0 : $i]:
% 1.00/1.20         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 1.00/1.20          | ((sk_B) = (k7_setfam_1 @ sk_A @ X0))
% 1.00/1.20          | (m1_subset_1 @ (sk_D @ sk_B @ X0 @ sk_A) @ (k1_zfmisc_1 @ sk_A)))),
% 1.00/1.20      inference('sup-', [status(thm)], ['25', '26'])).
% 1.00/1.20  thf('28', plain,
% 1.00/1.20      (((m1_subset_1 @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A) @ 
% 1.00/1.20         (k1_zfmisc_1 @ sk_A))
% 1.00/1.20        | ((sk_B) = (k7_setfam_1 @ sk_A @ k1_xboole_0)))),
% 1.00/1.20      inference('sup-', [status(thm)], ['24', '27'])).
% 1.00/1.20  thf(involutiveness_k3_subset_1, axiom,
% 1.00/1.20    (![A:$i,B:$i]:
% 1.00/1.20     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.00/1.20       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 1.00/1.20  thf('29', plain,
% 1.00/1.20      (![X7 : $i, X8 : $i]:
% 1.00/1.20         (((k3_subset_1 @ X8 @ (k3_subset_1 @ X8 @ X7)) = (X7))
% 1.00/1.20          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 1.00/1.20      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.00/1.20  thf('30', plain,
% 1.00/1.20      ((((sk_B) = (k7_setfam_1 @ sk_A @ k1_xboole_0))
% 1.00/1.20        | ((k3_subset_1 @ sk_A @ 
% 1.00/1.20            (k3_subset_1 @ sk_A @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A)))
% 1.00/1.20            = (sk_D @ sk_B @ k1_xboole_0 @ sk_A)))),
% 1.00/1.20      inference('sup-', [status(thm)], ['28', '29'])).
% 1.00/1.20  thf('31', plain, (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf('32', plain,
% 1.00/1.20      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 1.00/1.20         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X10)))
% 1.00/1.20          | ((X9) != (k7_setfam_1 @ X10 @ X11))
% 1.00/1.20          | (r2_hidden @ X12 @ X9)
% 1.00/1.20          | ~ (r2_hidden @ (k3_subset_1 @ X10 @ X12) @ X11)
% 1.00/1.20          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X10))
% 1.00/1.20          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X10))))),
% 1.00/1.20      inference('cnf', [status(esa)], [d8_setfam_1])).
% 1.00/1.20  thf('33', plain,
% 1.00/1.20      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.00/1.20         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X10)))
% 1.00/1.20          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X10))
% 1.00/1.20          | ~ (r2_hidden @ (k3_subset_1 @ X10 @ X12) @ X11)
% 1.00/1.20          | (r2_hidden @ X12 @ (k7_setfam_1 @ X10 @ X11))
% 1.00/1.20          | ~ (m1_subset_1 @ (k7_setfam_1 @ X10 @ X11) @ 
% 1.00/1.20               (k1_zfmisc_1 @ (k1_zfmisc_1 @ X10))))),
% 1.00/1.20      inference('simplify', [status(thm)], ['32'])).
% 1.00/1.20  thf('34', plain,
% 1.00/1.20      (![X0 : $i]:
% 1.00/1.20         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 1.00/1.20          | (r2_hidden @ X0 @ (k7_setfam_1 @ sk_A @ sk_B))
% 1.00/1.20          | ~ (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ sk_B)
% 1.00/1.20          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 1.00/1.20          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 1.00/1.20      inference('sup-', [status(thm)], ['31', '33'])).
% 1.00/1.20  thf('35', plain,
% 1.00/1.20      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 1.00/1.20      inference('demod', [status(thm)], ['2', '3'])).
% 1.00/1.20  thf('36', plain, (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf('37', plain,
% 1.00/1.20      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf('38', plain,
% 1.00/1.20      (![X0 : $i]:
% 1.00/1.20         ((r2_hidden @ X0 @ k1_xboole_0)
% 1.00/1.20          | ~ (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ sk_B)
% 1.00/1.20          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 1.00/1.20      inference('demod', [status(thm)], ['34', '35', '36', '37'])).
% 1.00/1.20  thf('39', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.00/1.20      inference('sup-', [status(thm)], ['15', '16'])).
% 1.00/1.20  thf('40', plain,
% 1.00/1.20      (![X0 : $i]:
% 1.00/1.20         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 1.00/1.20          | ~ (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ sk_B))),
% 1.00/1.20      inference('clc', [status(thm)], ['38', '39'])).
% 1.00/1.20  thf('41', plain,
% 1.00/1.20      ((~ (r2_hidden @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A) @ sk_B)
% 1.00/1.20        | ((sk_B) = (k7_setfam_1 @ sk_A @ k1_xboole_0))
% 1.00/1.20        | ~ (m1_subset_1 @ 
% 1.00/1.20             (k3_subset_1 @ sk_A @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A)) @ 
% 1.00/1.20             (k1_zfmisc_1 @ sk_A)))),
% 1.00/1.20      inference('sup-', [status(thm)], ['30', '40'])).
% 1.00/1.20  thf('42', plain,
% 1.00/1.20      (((m1_subset_1 @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A) @ 
% 1.00/1.20         (k1_zfmisc_1 @ sk_A))
% 1.00/1.20        | ((sk_B) = (k7_setfam_1 @ sk_A @ k1_xboole_0)))),
% 1.00/1.20      inference('sup-', [status(thm)], ['24', '27'])).
% 1.00/1.20  thf(dt_k3_subset_1, axiom,
% 1.00/1.20    (![A:$i,B:$i]:
% 1.00/1.20     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.00/1.20       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.00/1.20  thf('43', plain,
% 1.00/1.20      (![X5 : $i, X6 : $i]:
% 1.00/1.20         ((m1_subset_1 @ (k3_subset_1 @ X5 @ X6) @ (k1_zfmisc_1 @ X5))
% 1.00/1.20          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 1.00/1.20      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 1.00/1.20  thf('44', plain,
% 1.00/1.20      ((((sk_B) = (k7_setfam_1 @ sk_A @ k1_xboole_0))
% 1.00/1.20        | (m1_subset_1 @ 
% 1.00/1.20           (k3_subset_1 @ sk_A @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A)) @ 
% 1.00/1.20           (k1_zfmisc_1 @ sk_A)))),
% 1.00/1.20      inference('sup-', [status(thm)], ['42', '43'])).
% 1.00/1.20  thf('45', plain,
% 1.00/1.20      ((((sk_B) = (k7_setfam_1 @ sk_A @ k1_xboole_0))
% 1.00/1.20        | ~ (r2_hidden @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A) @ sk_B))),
% 1.00/1.20      inference('clc', [status(thm)], ['41', '44'])).
% 1.00/1.20  thf('46', plain, (((k1_xboole_0) = (k7_setfam_1 @ sk_A @ k1_xboole_0))),
% 1.00/1.20      inference('clc', [status(thm)], ['18', '19'])).
% 1.00/1.20  thf('47', plain,
% 1.00/1.20      ((((sk_B) = (k1_xboole_0))
% 1.00/1.20        | ~ (r2_hidden @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A) @ sk_B))),
% 1.00/1.20      inference('demod', [status(thm)], ['45', '46'])).
% 1.00/1.20  thf('48', plain, (((sk_B) != (k1_xboole_0))),
% 1.00/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.20  thf('49', plain, (~ (r2_hidden @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A) @ sk_B)),
% 1.00/1.20      inference('simplify_reflect-', [status(thm)], ['47', '48'])).
% 1.00/1.20  thf('50', plain,
% 1.00/1.20      ((r2_hidden @ 
% 1.00/1.20        (k3_subset_1 @ sk_A @ (sk_D @ sk_B @ k1_xboole_0 @ sk_A)) @ k1_xboole_0)),
% 1.00/1.20      inference('clc', [status(thm)], ['23', '49'])).
% 1.00/1.20  thf('51', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.00/1.20      inference('sup-', [status(thm)], ['15', '16'])).
% 1.00/1.20  thf('52', plain, ($false), inference('sup-', [status(thm)], ['50', '51'])).
% 1.00/1.20  
% 1.00/1.20  % SZS output end Refutation
% 1.00/1.20  
% 1.00/1.21  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
