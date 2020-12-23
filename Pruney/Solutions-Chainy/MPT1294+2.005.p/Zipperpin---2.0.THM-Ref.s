%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9XabDzD1bg

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:10 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 148 expanded)
%              Number of leaves         :   23 (  53 expanded)
%              Depth                    :   14
%              Number of atoms          :  546 (1321 expanded)
%              Number of equality atoms :   68 ( 168 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t10_tops_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ~ ( ( B != k1_xboole_0 )
            & ( ( k7_setfam_1 @ A @ B )
              = k1_xboole_0 ) )
        & ~ ( ( ( k7_setfam_1 @ A @ B )
             != k1_xboole_0 )
            & ( B = k1_xboole_0 ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ( ~ ( ( B != k1_xboole_0 )
              & ( ( k7_setfam_1 @ A @ B )
                = k1_xboole_0 ) )
          & ~ ( ( ( k7_setfam_1 @ A @ B )
               != k1_xboole_0 )
              & ( B = k1_xboole_0 ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t10_tops_2])).

thf('0',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( ( k7_setfam_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( ( k7_setfam_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k7_setfam_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k7_setfam_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k7_setfam_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t46_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ~ ( ( B != k1_xboole_0 )
          & ( ( k7_setfam_1 @ A @ B )
            = k1_xboole_0 ) ) ) )).

thf('5',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k7_setfam_1 @ X16 @ X17 )
       != k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[t46_setfam_1])).

thf('6',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k7_setfam_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ( ( k7_setfam_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ( k7_setfam_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != k1_xboole_0 )
      & ( ( k7_setfam_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k7_setfam_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k7_setfam_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('13',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('14',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('15',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

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

thf('16',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) )
      | ( r2_hidden @ ( sk_D @ X12 @ X14 @ X13 ) @ X12 )
      | ( r2_hidden @ ( k3_subset_1 @ X13 @ ( sk_D @ X12 @ X14 @ X13 ) ) @ X14 )
      | ( X12
        = ( k7_setfam_1 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) )
      | ( k1_xboole_0
        = ( k7_setfam_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X0 @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) ) @ X1 )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ( r2_hidden @ ( k3_subset_1 @ X0 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k7_setfam_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k4_xboole_0 @ X5 @ X6 ) )
      = ( k3_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('20',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('22',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('24',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('25',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t43_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_xboole_0 @ B @ C )
          <=> ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('26',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X10 @ ( k3_subset_1 @ X9 @ X8 ) )
      | ( r1_xboole_0 @ X10 @ X8 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t43_subset_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r1_xboole_0 @ X1 @ k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('30',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['30','35'])).

thf('37',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k7_setfam_1 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X0 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['18','37'])).

thf('39',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','36'])).

thf('40',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k7_setfam_1 @ X0 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,
    ( ! [X0: $i] :
        ( k1_xboole_0
        = ( k7_setfam_1 @ X0 @ sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['13','40'])).

thf('42',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('43',plain,
    ( ! [X0: $i] :
        ( sk_B
        = ( k7_setfam_1 @ X0 @ sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( k7_setfam_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k7_setfam_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('45',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( ( ( k7_setfam_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('47',plain,
    ( ( sk_B != sk_B )
   <= ( ( ( k7_setfam_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_B = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( ( k7_setfam_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','11','12','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9XabDzD1bg
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:39:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 0.19/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.52  % Solved by: fo/fo7.sh
% 0.19/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.52  % done 130 iterations in 0.076s
% 0.19/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.52  % SZS output start Refutation
% 0.19/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.52  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.19/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.52  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.19/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.52  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.19/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.52  thf(t10_tops_2, conjecture,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.19/0.52       ( ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.19/0.52              ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) & 
% 0.19/0.52         ( ~( ( ( k7_setfam_1 @ A @ B ) != ( k1_xboole_0 ) ) & 
% 0.19/0.52              ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.19/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.52    (~( ![A:$i,B:$i]:
% 0.19/0.52        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.19/0.52          ( ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.19/0.52                 ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) & 
% 0.19/0.52            ( ~( ( ( k7_setfam_1 @ A @ B ) != ( k1_xboole_0 ) ) & 
% 0.19/0.52                 ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.19/0.52    inference('cnf.neg', [status(esa)], [t10_tops_2])).
% 0.19/0.52  thf('0', plain,
% 0.19/0.52      ((((sk_B) != (k1_xboole_0))
% 0.19/0.52        | ((k7_setfam_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('1', plain,
% 0.19/0.52      (~ (((sk_B) = (k1_xboole_0))) | 
% 0.19/0.52       ~ (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.19/0.52      inference('split', [status(esa)], ['0'])).
% 0.19/0.52  thf('2', plain,
% 0.19/0.52      ((((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.19/0.52        | ((sk_B) = (k1_xboole_0)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('3', plain,
% 0.19/0.52      ((((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.19/0.52         <= ((((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.19/0.52      inference('split', [status(esa)], ['2'])).
% 0.19/0.52  thf('4', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(t46_setfam_1, axiom,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.19/0.52       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.19/0.52            ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.19/0.52  thf('5', plain,
% 0.19/0.52      (![X16 : $i, X17 : $i]:
% 0.19/0.52         (((k7_setfam_1 @ X16 @ X17) != (k1_xboole_0))
% 0.19/0.52          | ((X17) = (k1_xboole_0))
% 0.19/0.52          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16))))),
% 0.19/0.52      inference('cnf', [status(esa)], [t46_setfam_1])).
% 0.19/0.52  thf('6', plain,
% 0.19/0.52      ((((sk_B) = (k1_xboole_0))
% 0.19/0.52        | ((k7_setfam_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.52  thf('7', plain,
% 0.19/0.52      (((((k1_xboole_0) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0))))
% 0.19/0.52         <= ((((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.19/0.52      inference('sup-', [status(thm)], ['3', '6'])).
% 0.19/0.52  thf('8', plain,
% 0.19/0.52      ((((sk_B) = (k1_xboole_0)))
% 0.19/0.52         <= ((((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.19/0.52      inference('simplify', [status(thm)], ['7'])).
% 0.19/0.52  thf('9', plain,
% 0.19/0.52      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.19/0.52      inference('split', [status(esa)], ['0'])).
% 0.19/0.52  thf('10', plain,
% 0.19/0.52      ((((sk_B) != (sk_B)))
% 0.19/0.52         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 0.19/0.52             (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.19/0.52      inference('sup-', [status(thm)], ['8', '9'])).
% 0.19/0.52  thf('11', plain,
% 0.19/0.52      ((((sk_B) = (k1_xboole_0))) | 
% 0.19/0.52       ~ (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.19/0.52      inference('simplify', [status(thm)], ['10'])).
% 0.19/0.52  thf('12', plain,
% 0.19/0.52      ((((sk_B) = (k1_xboole_0))) | 
% 0.19/0.52       (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.19/0.52      inference('split', [status(esa)], ['2'])).
% 0.19/0.52  thf('13', plain,
% 0.19/0.52      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.19/0.52      inference('split', [status(esa)], ['2'])).
% 0.19/0.52  thf(t4_subset_1, axiom,
% 0.19/0.52    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.19/0.52  thf('14', plain,
% 0.19/0.52      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.19/0.52      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.19/0.52  thf('15', plain,
% 0.19/0.52      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.19/0.52      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.19/0.52  thf(d8_setfam_1, axiom,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.19/0.52       ( ![C:$i]:
% 0.19/0.52         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.19/0.52           ( ( ( C ) = ( k7_setfam_1 @ A @ B ) ) <=>
% 0.19/0.52             ( ![D:$i]:
% 0.19/0.52               ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.52                 ( ( r2_hidden @ D @ C ) <=>
% 0.19/0.52                   ( r2_hidden @ ( k3_subset_1 @ A @ D ) @ B ) ) ) ) ) ) ) ))).
% 0.19/0.52  thf('16', plain,
% 0.19/0.52      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.52         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X13)))
% 0.19/0.52          | (r2_hidden @ (sk_D @ X12 @ X14 @ X13) @ X12)
% 0.19/0.52          | (r2_hidden @ (k3_subset_1 @ X13 @ (sk_D @ X12 @ X14 @ X13)) @ X14)
% 0.19/0.52          | ((X12) = (k7_setfam_1 @ X13 @ X14))
% 0.19/0.52          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X13))))),
% 0.19/0.52      inference('cnf', [status(esa)], [d8_setfam_1])).
% 0.19/0.52  thf('17', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))
% 0.19/0.52          | ((k1_xboole_0) = (k7_setfam_1 @ X0 @ X1))
% 0.19/0.52          | (r2_hidden @ (k3_subset_1 @ X0 @ (sk_D @ k1_xboole_0 @ X1 @ X0)) @ 
% 0.19/0.52             X1)
% 0.19/0.52          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 0.19/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.19/0.52  thf('18', plain,
% 0.19/0.52      (![X0 : $i]:
% 0.19/0.52         ((r2_hidden @ (sk_D @ k1_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.19/0.52          | (r2_hidden @ 
% 0.19/0.52             (k3_subset_1 @ X0 @ (sk_D @ k1_xboole_0 @ k1_xboole_0 @ X0)) @ 
% 0.19/0.52             k1_xboole_0)
% 0.19/0.52          | ((k1_xboole_0) = (k7_setfam_1 @ X0 @ k1_xboole_0)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['14', '17'])).
% 0.19/0.52  thf(t48_xboole_1, axiom,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.19/0.52  thf('19', plain,
% 0.19/0.52      (![X5 : $i, X6 : $i]:
% 0.19/0.52         ((k4_xboole_0 @ X5 @ (k4_xboole_0 @ X5 @ X6))
% 0.19/0.52           = (k3_xboole_0 @ X5 @ X6))),
% 0.19/0.52      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.19/0.52  thf(t4_boole, axiom,
% 0.19/0.52    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.19/0.52  thf('20', plain,
% 0.19/0.52      (![X7 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 0.19/0.52      inference('cnf', [status(esa)], [t4_boole])).
% 0.19/0.52  thf('21', plain,
% 0.19/0.52      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.19/0.52      inference('sup+', [status(thm)], ['19', '20'])).
% 0.19/0.52  thf(t4_xboole_0, axiom,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.19/0.52            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.19/0.52       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.19/0.52            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.19/0.52  thf('22', plain,
% 0.19/0.52      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.19/0.52         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.19/0.52          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.19/0.52      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.19/0.52  thf('23', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.19/0.52      inference('sup-', [status(thm)], ['21', '22'])).
% 0.19/0.52  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.19/0.52  thf('24', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.19/0.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.19/0.52  thf('25', plain,
% 0.19/0.52      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.19/0.52      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.19/0.52  thf(t43_subset_1, axiom,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.52       ( ![C:$i]:
% 0.19/0.52         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.52           ( ( r1_xboole_0 @ B @ C ) <=>
% 0.19/0.52             ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.19/0.52  thf('26', plain,
% 0.19/0.52      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.19/0.52         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.19/0.52          | ~ (r1_tarski @ X10 @ (k3_subset_1 @ X9 @ X8))
% 0.19/0.52          | (r1_xboole_0 @ X10 @ X8)
% 0.19/0.52          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.19/0.52      inference('cnf', [status(esa)], [t43_subset_1])).
% 0.19/0.52  thf('27', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.19/0.52          | (r1_xboole_0 @ X1 @ k1_xboole_0)
% 0.19/0.52          | ~ (r1_tarski @ X1 @ (k3_subset_1 @ X0 @ k1_xboole_0)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['25', '26'])).
% 0.19/0.52  thf('28', plain,
% 0.19/0.52      (![X0 : $i]:
% 0.19/0.52         ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.19/0.52          | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['24', '27'])).
% 0.19/0.52  thf('29', plain,
% 0.19/0.52      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.19/0.52      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.19/0.52  thf('30', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.19/0.52      inference('demod', [status(thm)], ['28', '29'])).
% 0.19/0.52  thf('31', plain,
% 0.19/0.52      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.19/0.52      inference('sup+', [status(thm)], ['19', '20'])).
% 0.19/0.52  thf('32', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         ((r1_xboole_0 @ X0 @ X1)
% 0.19/0.52          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.19/0.52      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.19/0.52  thf('33', plain,
% 0.19/0.52      (![X0 : $i]:
% 0.19/0.52         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.19/0.52          | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.19/0.52      inference('sup+', [status(thm)], ['31', '32'])).
% 0.19/0.52  thf('34', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.19/0.52      inference('sup-', [status(thm)], ['21', '22'])).
% 0.19/0.52  thf('35', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         ((r1_xboole_0 @ k1_xboole_0 @ X0) | ~ (r1_xboole_0 @ k1_xboole_0 @ X1))),
% 0.19/0.52      inference('sup-', [status(thm)], ['33', '34'])).
% 0.19/0.52  thf('36', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.19/0.52      inference('sup-', [status(thm)], ['30', '35'])).
% 0.19/0.52  thf('37', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.19/0.52      inference('demod', [status(thm)], ['23', '36'])).
% 0.19/0.52  thf('38', plain,
% 0.19/0.52      (![X0 : $i]:
% 0.19/0.52         (((k1_xboole_0) = (k7_setfam_1 @ X0 @ k1_xboole_0))
% 0.19/0.52          | (r2_hidden @ 
% 0.19/0.52             (k3_subset_1 @ X0 @ (sk_D @ k1_xboole_0 @ k1_xboole_0 @ X0)) @ 
% 0.19/0.52             k1_xboole_0))),
% 0.19/0.52      inference('clc', [status(thm)], ['18', '37'])).
% 0.19/0.52  thf('39', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.19/0.52      inference('demod', [status(thm)], ['23', '36'])).
% 0.19/0.52  thf('40', plain,
% 0.19/0.52      (![X0 : $i]: ((k1_xboole_0) = (k7_setfam_1 @ X0 @ k1_xboole_0))),
% 0.19/0.52      inference('clc', [status(thm)], ['38', '39'])).
% 0.19/0.52  thf('41', plain,
% 0.19/0.52      ((![X0 : $i]: ((k1_xboole_0) = (k7_setfam_1 @ X0 @ sk_B)))
% 0.19/0.52         <= ((((sk_B) = (k1_xboole_0))))),
% 0.19/0.52      inference('sup+', [status(thm)], ['13', '40'])).
% 0.19/0.52  thf('42', plain,
% 0.19/0.52      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.19/0.52      inference('split', [status(esa)], ['2'])).
% 0.19/0.52  thf('43', plain,
% 0.19/0.52      ((![X0 : $i]: ((sk_B) = (k7_setfam_1 @ X0 @ sk_B)))
% 0.19/0.52         <= ((((sk_B) = (k1_xboole_0))))),
% 0.19/0.52      inference('demod', [status(thm)], ['41', '42'])).
% 0.19/0.52  thf('44', plain,
% 0.19/0.52      ((((k7_setfam_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 0.19/0.52         <= (~ (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.19/0.52      inference('split', [status(esa)], ['0'])).
% 0.19/0.52  thf('45', plain,
% 0.19/0.52      ((((sk_B) != (k1_xboole_0)))
% 0.19/0.52         <= (~ (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.19/0.52             (((sk_B) = (k1_xboole_0))))),
% 0.19/0.52      inference('sup-', [status(thm)], ['43', '44'])).
% 0.19/0.52  thf('46', plain,
% 0.19/0.52      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.19/0.52      inference('split', [status(esa)], ['2'])).
% 0.19/0.52  thf('47', plain,
% 0.19/0.52      ((((sk_B) != (sk_B)))
% 0.19/0.52         <= (~ (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.19/0.52             (((sk_B) = (k1_xboole_0))))),
% 0.19/0.52      inference('demod', [status(thm)], ['45', '46'])).
% 0.19/0.52  thf('48', plain,
% 0.19/0.52      (~ (((sk_B) = (k1_xboole_0))) | 
% 0.19/0.52       (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.19/0.52      inference('simplify', [status(thm)], ['47'])).
% 0.19/0.52  thf('49', plain, ($false),
% 0.19/0.52      inference('sat_resolution*', [status(thm)], ['1', '11', '12', '48'])).
% 0.19/0.52  
% 0.19/0.52  % SZS output end Refutation
% 0.19/0.52  
% 0.19/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
