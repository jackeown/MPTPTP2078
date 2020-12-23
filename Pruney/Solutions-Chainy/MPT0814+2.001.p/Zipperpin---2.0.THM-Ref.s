%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DVBLCIb2Zz

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:38 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 121 expanded)
%              Number of leaves         :   24 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :  440 (1010 expanded)
%              Number of equality atoms :   25 (  52 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t6_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
     => ~ ( ( r2_hidden @ A @ D )
          & ! [E: $i,F: $i] :
              ~ ( ( A
                  = ( k4_tarski @ E @ F ) )
                & ( r2_hidden @ E @ B )
                & ( r2_hidden @ F @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
       => ~ ( ( r2_hidden @ A @ D )
            & ! [E: $i,F: $i] :
                ~ ( ( A
                    = ( k4_tarski @ E @ F ) )
                  & ( r2_hidden @ E @ B )
                  & ( r2_hidden @ F @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t6_relset_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('3',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_B_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t65_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r2_hidden @ D @ C )
        & ( r1_tarski @ C @ ( k2_zfmisc_1 @ A @ B ) )
        & ! [E: $i] :
            ( ( m1_subset_1 @ E @ A )
           => ! [F: $i] :
                ( ( m1_subset_1 @ F @ B )
               => ( D
                 != ( k4_tarski @ E @ F ) ) ) ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X12 @ ( k2_zfmisc_1 @ X13 @ X14 ) )
      | ( X15
        = ( k4_tarski @ ( sk_E @ X15 @ X14 @ X13 ) @ ( sk_F @ X15 @ X14 @ X13 ) ) )
      | ~ ( r2_hidden @ X15 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t65_subset_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_D )
      | ( X0
        = ( k4_tarski @ ( sk_E @ X0 @ sk_C_1 @ sk_B_2 ) @ ( sk_F @ X0 @ sk_C_1 @ sk_B_2 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( sk_A
    = ( k4_tarski @ ( sk_E @ sk_A @ sk_C_1 @ sk_B_2 ) @ ( sk_F @ sk_A @ sk_C_1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    r2_hidden @ sk_A @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_B_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('9',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X12 @ ( k2_zfmisc_1 @ X13 @ X14 ) )
      | ( m1_subset_1 @ ( sk_E @ X15 @ X14 @ X13 ) @ X13 )
      | ~ ( r2_hidden @ X15 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t65_subset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_D )
      | ( m1_subset_1 @ ( sk_E @ X0 @ sk_C_1 @ sk_B_2 ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ ( sk_E @ sk_A @ sk_C_1 @ sk_B_2 ) @ sk_B_2 ),
    inference('sup-',[status(thm)],['7','10'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r2_hidden @ X18 @ X19 )
      | ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('13',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( r2_hidden @ ( sk_E @ sk_A @ sk_C_1 @ sk_B_2 ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('14',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('17',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_zfmisc_1 @ X10 @ X11 )
        = k1_xboole_0 )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('18',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X11 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('21',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( v1_xboole_0 @ X16 )
      | ~ ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('22',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_C_1 ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r2_hidden @ sk_A @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('25',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['22','25'])).

thf('27',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['19','26'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('28',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('29',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    r2_hidden @ ( sk_E @ sk_A @ sk_C_1 @ sk_B_2 ) @ sk_B_2 ),
    inference(clc,[status(thm)],['13','29'])).

thf('31',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X32 @ sk_B_2 )
      | ~ ( r2_hidden @ X33 @ sk_C_1 )
      | ( sk_A
       != ( k4_tarski @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k4_tarski @ ( sk_E @ sk_A @ sk_C_1 @ sk_B_2 ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_A != sk_A )
    | ~ ( r2_hidden @ ( sk_F @ sk_A @ sk_C_1 @ sk_B_2 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['6','32'])).

thf('34',plain,(
    r2_hidden @ sk_A @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_B_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('36',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X12 @ ( k2_zfmisc_1 @ X13 @ X14 ) )
      | ( m1_subset_1 @ ( sk_F @ X15 @ X14 @ X13 ) @ X14 )
      | ~ ( r2_hidden @ X15 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t65_subset_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_D )
      | ( m1_subset_1 @ ( sk_F @ X0 @ sk_C_1 @ sk_B_2 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ ( sk_F @ sk_A @ sk_C_1 @ sk_B_2 ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r2_hidden @ X18 @ X19 )
      | ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('40',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( r2_hidden @ ( sk_F @ sk_A @ sk_C_1 @ sk_B_2 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('42',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_zfmisc_1 @ X10 @ X11 )
        = k1_xboole_0 )
      | ( X11 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('43',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','43'])).

thf('45',plain,(
    ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['22','25'])).

thf('46',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('48',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    r2_hidden @ ( sk_F @ sk_A @ sk_C_1 @ sk_B_2 ) @ sk_C_1 ),
    inference(clc,[status(thm)],['40','48'])).

thf('50',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['33','49'])).

thf('51',plain,(
    $false ),
    inference(simplify,[status(thm)],['50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DVBLCIb2Zz
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:51:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.54  % Solved by: fo/fo7.sh
% 0.36/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.54  % done 171 iterations in 0.078s
% 0.36/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.54  % SZS output start Refutation
% 0.36/0.54  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.36/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.54  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.36/0.54  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.36/0.54  thf(sk_D_type, type, sk_D: $i).
% 0.36/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.54  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.36/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.54  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.36/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.54  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.36/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.54  thf(t6_relset_1, conjecture,
% 0.36/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.54     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 0.36/0.54       ( ~( ( r2_hidden @ A @ D ) & 
% 0.36/0.54            ( ![E:$i,F:$i]:
% 0.36/0.54              ( ~( ( ( A ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ E @ B ) & 
% 0.36/0.54                   ( r2_hidden @ F @ C ) ) ) ) ) ) ))).
% 0.36/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.54    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.54        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 0.36/0.54          ( ~( ( r2_hidden @ A @ D ) & 
% 0.36/0.54               ( ![E:$i,F:$i]:
% 0.36/0.54                 ( ~( ( ( A ) = ( k4_tarski @ E @ F ) ) & 
% 0.36/0.54                      ( r2_hidden @ E @ B ) & ( r2_hidden @ F @ C ) ) ) ) ) ) ) )),
% 0.36/0.54    inference('cnf.neg', [status(esa)], [t6_relset_1])).
% 0.36/0.54  thf('0', plain, ((r2_hidden @ sk_A @ sk_D)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('1', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_C_1)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(t3_subset, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.54  thf('2', plain,
% 0.36/0.54      (![X20 : $i, X21 : $i]:
% 0.36/0.54         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 0.36/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.54  thf('3', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_B_2 @ sk_C_1))),
% 0.36/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.36/0.54  thf(t65_subset_1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.54     ( ~( ( r2_hidden @ D @ C ) & 
% 0.36/0.54          ( r1_tarski @ C @ ( k2_zfmisc_1 @ A @ B ) ) & 
% 0.36/0.54          ( ![E:$i]:
% 0.36/0.54            ( ( m1_subset_1 @ E @ A ) =>
% 0.36/0.54              ( ![F:$i]:
% 0.36/0.54                ( ( m1_subset_1 @ F @ B ) => ( ( D ) != ( k4_tarski @ E @ F ) ) ) ) ) ) ) ))).
% 0.36/0.54  thf('4', plain,
% 0.36/0.54      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.36/0.54         (~ (r1_tarski @ X12 @ (k2_zfmisc_1 @ X13 @ X14))
% 0.36/0.54          | ((X15)
% 0.36/0.54              = (k4_tarski @ (sk_E @ X15 @ X14 @ X13) @ 
% 0.36/0.54                 (sk_F @ X15 @ X14 @ X13)))
% 0.36/0.54          | ~ (r2_hidden @ X15 @ X12))),
% 0.36/0.54      inference('cnf', [status(esa)], [t65_subset_1])).
% 0.36/0.54  thf('5', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (~ (r2_hidden @ X0 @ sk_D)
% 0.36/0.54          | ((X0)
% 0.36/0.54              = (k4_tarski @ (sk_E @ X0 @ sk_C_1 @ sk_B_2) @ 
% 0.36/0.54                 (sk_F @ X0 @ sk_C_1 @ sk_B_2))))),
% 0.36/0.54      inference('sup-', [status(thm)], ['3', '4'])).
% 0.36/0.54  thf('6', plain,
% 0.36/0.54      (((sk_A)
% 0.36/0.54         = (k4_tarski @ (sk_E @ sk_A @ sk_C_1 @ sk_B_2) @ 
% 0.36/0.54            (sk_F @ sk_A @ sk_C_1 @ sk_B_2)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['0', '5'])).
% 0.36/0.54  thf('7', plain, ((r2_hidden @ sk_A @ sk_D)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('8', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_B_2 @ sk_C_1))),
% 0.36/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.36/0.54  thf('9', plain,
% 0.36/0.54      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.36/0.54         (~ (r1_tarski @ X12 @ (k2_zfmisc_1 @ X13 @ X14))
% 0.36/0.54          | (m1_subset_1 @ (sk_E @ X15 @ X14 @ X13) @ X13)
% 0.36/0.54          | ~ (r2_hidden @ X15 @ X12))),
% 0.36/0.54      inference('cnf', [status(esa)], [t65_subset_1])).
% 0.36/0.54  thf('10', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (~ (r2_hidden @ X0 @ sk_D)
% 0.36/0.54          | (m1_subset_1 @ (sk_E @ X0 @ sk_C_1 @ sk_B_2) @ sk_B_2))),
% 0.36/0.54      inference('sup-', [status(thm)], ['8', '9'])).
% 0.36/0.54  thf('11', plain, ((m1_subset_1 @ (sk_E @ sk_A @ sk_C_1 @ sk_B_2) @ sk_B_2)),
% 0.36/0.54      inference('sup-', [status(thm)], ['7', '10'])).
% 0.36/0.54  thf(t2_subset, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( m1_subset_1 @ A @ B ) =>
% 0.36/0.54       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.36/0.54  thf('12', plain,
% 0.36/0.54      (![X18 : $i, X19 : $i]:
% 0.36/0.54         ((r2_hidden @ X18 @ X19)
% 0.36/0.54          | (v1_xboole_0 @ X19)
% 0.36/0.54          | ~ (m1_subset_1 @ X18 @ X19))),
% 0.36/0.54      inference('cnf', [status(esa)], [t2_subset])).
% 0.36/0.54  thf('13', plain,
% 0.36/0.54      (((v1_xboole_0 @ sk_B_2)
% 0.36/0.54        | (r2_hidden @ (sk_E @ sk_A @ sk_C_1 @ sk_B_2) @ sk_B_2))),
% 0.36/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.36/0.54  thf(t7_xboole_0, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.36/0.54          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.36/0.54  thf('14', plain,
% 0.36/0.54      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X8) @ X8))),
% 0.36/0.54      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.36/0.54  thf(d1_xboole_0, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.36/0.54  thf('15', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.36/0.54      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.36/0.54  thf('16', plain,
% 0.36/0.54      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['14', '15'])).
% 0.36/0.54  thf(t113_zfmisc_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.36/0.54       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.36/0.54  thf('17', plain,
% 0.36/0.54      (![X10 : $i, X11 : $i]:
% 0.36/0.54         (((k2_zfmisc_1 @ X10 @ X11) = (k1_xboole_0))
% 0.36/0.54          | ((X10) != (k1_xboole_0)))),
% 0.36/0.54      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.36/0.54  thf('18', plain,
% 0.36/0.54      (![X11 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X11) = (k1_xboole_0))),
% 0.36/0.54      inference('simplify', [status(thm)], ['17'])).
% 0.36/0.54  thf('19', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.36/0.54      inference('sup+', [status(thm)], ['16', '18'])).
% 0.36/0.54  thf('20', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_C_1)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(cc1_subset_1, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( v1_xboole_0 @ A ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.36/0.54  thf('21', plain,
% 0.36/0.54      (![X16 : $i, X17 : $i]:
% 0.36/0.54         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.36/0.54          | (v1_xboole_0 @ X16)
% 0.36/0.54          | ~ (v1_xboole_0 @ X17))),
% 0.36/0.54      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.36/0.54  thf('22', plain,
% 0.36/0.54      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_B_2 @ sk_C_1))
% 0.36/0.54        | (v1_xboole_0 @ sk_D))),
% 0.36/0.54      inference('sup-', [status(thm)], ['20', '21'])).
% 0.36/0.54  thf('23', plain, ((r2_hidden @ sk_A @ sk_D)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('24', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.36/0.54      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.36/0.54  thf('25', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.36/0.54      inference('sup-', [status(thm)], ['23', '24'])).
% 0.36/0.54  thf('26', plain, (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_B_2 @ sk_C_1))),
% 0.36/0.54      inference('clc', [status(thm)], ['22', '25'])).
% 0.36/0.54  thf('27', plain,
% 0.36/0.54      ((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ sk_B_2))),
% 0.36/0.54      inference('sup-', [status(thm)], ['19', '26'])).
% 0.36/0.54  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.36/0.54  thf('28', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.54  thf('29', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.36/0.54      inference('demod', [status(thm)], ['27', '28'])).
% 0.36/0.54  thf('30', plain, ((r2_hidden @ (sk_E @ sk_A @ sk_C_1 @ sk_B_2) @ sk_B_2)),
% 0.36/0.54      inference('clc', [status(thm)], ['13', '29'])).
% 0.36/0.54  thf('31', plain,
% 0.36/0.54      (![X32 : $i, X33 : $i]:
% 0.36/0.54         (~ (r2_hidden @ X32 @ sk_B_2)
% 0.36/0.54          | ~ (r2_hidden @ X33 @ sk_C_1)
% 0.36/0.54          | ((sk_A) != (k4_tarski @ X32 @ X33)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('32', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (((sk_A) != (k4_tarski @ (sk_E @ sk_A @ sk_C_1 @ sk_B_2) @ X0))
% 0.36/0.54          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.36/0.54      inference('sup-', [status(thm)], ['30', '31'])).
% 0.36/0.54  thf('33', plain,
% 0.36/0.54      ((((sk_A) != (sk_A))
% 0.36/0.54        | ~ (r2_hidden @ (sk_F @ sk_A @ sk_C_1 @ sk_B_2) @ sk_C_1))),
% 0.36/0.54      inference('sup-', [status(thm)], ['6', '32'])).
% 0.36/0.54  thf('34', plain, ((r2_hidden @ sk_A @ sk_D)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('35', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_B_2 @ sk_C_1))),
% 0.36/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.36/0.54  thf('36', plain,
% 0.36/0.54      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.36/0.54         (~ (r1_tarski @ X12 @ (k2_zfmisc_1 @ X13 @ X14))
% 0.36/0.54          | (m1_subset_1 @ (sk_F @ X15 @ X14 @ X13) @ X14)
% 0.36/0.54          | ~ (r2_hidden @ X15 @ X12))),
% 0.36/0.54      inference('cnf', [status(esa)], [t65_subset_1])).
% 0.36/0.54  thf('37', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (~ (r2_hidden @ X0 @ sk_D)
% 0.36/0.54          | (m1_subset_1 @ (sk_F @ X0 @ sk_C_1 @ sk_B_2) @ sk_C_1))),
% 0.36/0.54      inference('sup-', [status(thm)], ['35', '36'])).
% 0.36/0.54  thf('38', plain, ((m1_subset_1 @ (sk_F @ sk_A @ sk_C_1 @ sk_B_2) @ sk_C_1)),
% 0.36/0.54      inference('sup-', [status(thm)], ['34', '37'])).
% 0.36/0.54  thf('39', plain,
% 0.36/0.54      (![X18 : $i, X19 : $i]:
% 0.36/0.54         ((r2_hidden @ X18 @ X19)
% 0.36/0.54          | (v1_xboole_0 @ X19)
% 0.36/0.54          | ~ (m1_subset_1 @ X18 @ X19))),
% 0.36/0.54      inference('cnf', [status(esa)], [t2_subset])).
% 0.36/0.54  thf('40', plain,
% 0.36/0.54      (((v1_xboole_0 @ sk_C_1)
% 0.36/0.54        | (r2_hidden @ (sk_F @ sk_A @ sk_C_1 @ sk_B_2) @ sk_C_1))),
% 0.36/0.54      inference('sup-', [status(thm)], ['38', '39'])).
% 0.36/0.54  thf('41', plain,
% 0.36/0.54      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['14', '15'])).
% 0.36/0.54  thf('42', plain,
% 0.36/0.54      (![X10 : $i, X11 : $i]:
% 0.36/0.54         (((k2_zfmisc_1 @ X10 @ X11) = (k1_xboole_0))
% 0.36/0.54          | ((X11) != (k1_xboole_0)))),
% 0.36/0.54      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.36/0.54  thf('43', plain,
% 0.36/0.54      (![X10 : $i]: ((k2_zfmisc_1 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.54      inference('simplify', [status(thm)], ['42'])).
% 0.36/0.54  thf('44', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.36/0.54      inference('sup+', [status(thm)], ['41', '43'])).
% 0.36/0.54  thf('45', plain, (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_B_2 @ sk_C_1))),
% 0.36/0.54      inference('clc', [status(thm)], ['22', '25'])).
% 0.36/0.54  thf('46', plain,
% 0.36/0.54      ((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ sk_C_1))),
% 0.36/0.54      inference('sup-', [status(thm)], ['44', '45'])).
% 0.36/0.54  thf('47', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.54  thf('48', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.36/0.54      inference('demod', [status(thm)], ['46', '47'])).
% 0.36/0.54  thf('49', plain, ((r2_hidden @ (sk_F @ sk_A @ sk_C_1 @ sk_B_2) @ sk_C_1)),
% 0.36/0.54      inference('clc', [status(thm)], ['40', '48'])).
% 0.36/0.54  thf('50', plain, (((sk_A) != (sk_A))),
% 0.36/0.54      inference('demod', [status(thm)], ['33', '49'])).
% 0.36/0.54  thf('51', plain, ($false), inference('simplify', [status(thm)], ['50'])).
% 0.36/0.54  
% 0.36/0.54  % SZS output end Refutation
% 0.36/0.54  
% 0.36/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
