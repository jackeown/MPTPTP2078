%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RToCD3LzBW

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:15 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 118 expanded)
%              Number of leaves         :   26 (  45 expanded)
%              Depth                    :   12
%              Number of atoms          :  501 (1141 expanded)
%              Number of equality atoms :   65 ( 163 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t26_mcart_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) )
             => ( ( C
                 != ( k1_mcart_1 @ C ) )
                & ( C
                 != ( k2_mcart_1 @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( A != k1_xboole_0 )
          & ( B != k1_xboole_0 )
          & ~ ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) )
               => ( ( C
                   != ( k1_mcart_1 @ C ) )
                  & ( C
                   != ( k2_mcart_1 @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t26_mcart_1])).

thf('0',plain,
    ( ( sk_C
      = ( k1_mcart_1 @ sk_C ) )
    | ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_C
      = ( k2_mcart_1 @ sk_C ) )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r2_hidden @ X20 @ X21 )
      | ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
    | ( r2_hidden @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t23_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( A
          = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X27: $i,X28: $i] :
      ( ( X27
        = ( k4_tarski @ ( k1_mcart_1 @ X27 ) @ ( k2_mcart_1 @ X27 ) ) )
      | ~ ( v1_relat_1 @ X28 )
      | ~ ( r2_hidden @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('6',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
    | ( sk_C
      = ( k4_tarski @ ( k1_mcart_1 @ sk_C ) @ ( k2_mcart_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('7',plain,(
    ! [X22: $i,X23: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
    | ( sk_C
      = ( k4_tarski @ ( k1_mcart_1 @ sk_C ) @ ( k2_mcart_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('9',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('10',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d2_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( ( r2_hidden @ E @ A )
              & ( r2_hidden @ F @ B )
              & ( D
                = ( k4_tarski @ E @ F ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [F: $i,E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ D @ B @ A )
    <=> ( ( D
          = ( k4_tarski @ E @ F ) )
        & ( r2_hidden @ F @ B )
        & ( r2_hidden @ E @ A ) ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X9: $i] :
      ( ( zip_tseitin_0 @ X5 @ X4 @ X6 @ X7 @ X9 )
      | ~ ( r2_hidden @ X4 @ X9 )
      | ~ ( r2_hidden @ X5 @ X7 )
      | ( X6
       != ( k4_tarski @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('12',plain,(
    ! [X4: $i,X5: $i,X7: $i,X9: $i] :
      ( ~ ( r2_hidden @ X5 @ X7 )
      | ~ ( r2_hidden @ X4 @ X9 )
      | ( zip_tseitin_0 @ X5 @ X4 @ ( k4_tarski @ X4 @ X5 ) @ X7 @ X9 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_B_1 @ X0 ) @ X2 @ ( k4_tarski @ X2 @ ( sk_B_1 @ X0 ) ) @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_B_1 @ X1 ) @ ( sk_B_1 @ X0 ) @ ( k4_tarski @ ( sk_B_1 @ X0 ) @ ( sk_B_1 @ X1 ) ) @ X1 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X13 @ X14 )
      | ( r2_hidden @ X12 @ X15 )
      | ( X15
       != ( k2_zfmisc_1 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('16',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X12 @ ( k2_zfmisc_1 @ X14 @ X13 ) )
      | ~ ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X13 @ X14 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ X0 ) @ ( sk_B_1 @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( sk_C
      = ( k4_tarski @ ( k1_mcart_1 @ sk_C ) @ ( k2_mcart_1 @ sk_C ) ) )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','19'])).

thf('21',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( sk_C
    = ( k4_tarski @ ( k1_mcart_1 @ sk_C ) @ ( k2_mcart_1 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ( sk_C
      = ( k4_tarski @ ( k1_mcart_1 @ sk_C ) @ sk_C ) )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['1','23'])).

thf(t20_mcart_1,axiom,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ B @ C ) )
     => ( ( A
         != ( k1_mcart_1 @ A ) )
        & ( A
         != ( k2_mcart_1 @ A ) ) ) ) )).

thf('25',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( X24
       != ( k2_mcart_1 @ X24 ) )
      | ( X24
       != ( k4_tarski @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('26',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_tarski @ X25 @ X26 )
     != ( k2_mcart_1 @ ( k4_tarski @ X25 @ X26 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('27',plain,(
    ! [X29: $i,X31: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X29 @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('28',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_tarski @ X25 @ X26 )
     != X26 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( $false
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['24','28'])).

thf('30',plain,
    ( ( sk_C
      = ( k1_mcart_1 @ sk_C ) )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,
    ( sk_C
    = ( k4_tarski @ ( k1_mcart_1 @ sk_C ) @ ( k2_mcart_1 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['20','21','22'])).

thf('32',plain,
    ( ( sk_C
      = ( k4_tarski @ sk_C @ ( k2_mcart_1 @ sk_C ) ) )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( X24
       != ( k1_mcart_1 @ X24 ) )
      | ( X24
       != ( k4_tarski @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('34',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_tarski @ X25 @ X26 )
     != ( k1_mcart_1 @ ( k4_tarski @ X25 @ X26 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X29 @ X30 ) )
      = X29 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('36',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_tarski @ X25 @ X26 )
     != X25 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    sk_C
 != ( k1_mcart_1 @ sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['32','36'])).

thf('38',plain,
    ( ( sk_C
      = ( k2_mcart_1 @ sk_C ) )
    | ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('39',plain,
    ( sk_C
    = ( k2_mcart_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['37','38'])).

thf('40',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['29','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RToCD3LzBW
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:23:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.56  % Solved by: fo/fo7.sh
% 0.20/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.56  % done 135 iterations in 0.108s
% 0.20/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.56  % SZS output start Refutation
% 0.20/0.56  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.56  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.56  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.20/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.56  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.56  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.20/0.56  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.20/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.56  thf(t26_mcart_1, conjecture,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.56          ( ~( ![C:$i]:
% 0.20/0.56               ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) ) =>
% 0.20/0.56                 ( ( ( C ) != ( k1_mcart_1 @ C ) ) & 
% 0.20/0.56                   ( ( C ) != ( k2_mcart_1 @ C ) ) ) ) ) ) ) ))).
% 0.20/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.56    (~( ![A:$i,B:$i]:
% 0.20/0.56        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.56             ( ~( ![C:$i]:
% 0.20/0.56                  ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) ) =>
% 0.20/0.56                    ( ( ( C ) != ( k1_mcart_1 @ C ) ) & 
% 0.20/0.56                      ( ( C ) != ( k2_mcart_1 @ C ) ) ) ) ) ) ) ) )),
% 0.20/0.56    inference('cnf.neg', [status(esa)], [t26_mcart_1])).
% 0.20/0.56  thf('0', plain,
% 0.20/0.56      ((((sk_C) = (k1_mcart_1 @ sk_C)) | ((sk_C) = (k2_mcart_1 @ sk_C)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('1', plain,
% 0.20/0.56      ((((sk_C) = (k2_mcart_1 @ sk_C))) <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.20/0.56      inference('split', [status(esa)], ['0'])).
% 0.20/0.56  thf('2', plain, ((m1_subset_1 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B_2))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(t2_subset, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ A @ B ) =>
% 0.20/0.56       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.56  thf('3', plain,
% 0.20/0.56      (![X20 : $i, X21 : $i]:
% 0.20/0.56         ((r2_hidden @ X20 @ X21)
% 0.20/0.56          | (v1_xboole_0 @ X21)
% 0.20/0.56          | ~ (m1_subset_1 @ X20 @ X21))),
% 0.20/0.56      inference('cnf', [status(esa)], [t2_subset])).
% 0.20/0.56  thf('4', plain,
% 0.20/0.56      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))
% 0.20/0.56        | (r2_hidden @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.56  thf(t23_mcart_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( v1_relat_1 @ B ) =>
% 0.20/0.56       ( ( r2_hidden @ A @ B ) =>
% 0.20/0.56         ( ( A ) = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ))).
% 0.20/0.56  thf('5', plain,
% 0.20/0.56      (![X27 : $i, X28 : $i]:
% 0.20/0.56         (((X27) = (k4_tarski @ (k1_mcart_1 @ X27) @ (k2_mcart_1 @ X27)))
% 0.20/0.56          | ~ (v1_relat_1 @ X28)
% 0.20/0.56          | ~ (r2_hidden @ X27 @ X28))),
% 0.20/0.56      inference('cnf', [status(esa)], [t23_mcart_1])).
% 0.20/0.56  thf('6', plain,
% 0.20/0.56      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))
% 0.20/0.56        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))
% 0.20/0.56        | ((sk_C) = (k4_tarski @ (k1_mcart_1 @ sk_C) @ (k2_mcart_1 @ sk_C))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.56  thf(fc6_relat_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.56  thf('7', plain,
% 0.20/0.56      (![X22 : $i, X23 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X22 @ X23))),
% 0.20/0.56      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.56  thf('8', plain,
% 0.20/0.56      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))
% 0.20/0.56        | ((sk_C) = (k4_tarski @ (k1_mcart_1 @ sk_C) @ (k2_mcart_1 @ sk_C))))),
% 0.20/0.56      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.56  thf(t7_xboole_0, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.56          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.20/0.56  thf('9', plain,
% 0.20/0.56      (![X3 : $i]: (((X3) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X3) @ X3))),
% 0.20/0.56      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.56  thf('10', plain,
% 0.20/0.56      (![X3 : $i]: (((X3) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X3) @ X3))),
% 0.20/0.56      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.56  thf(d2_zfmisc_1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.20/0.56       ( ![D:$i]:
% 0.20/0.56         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.56           ( ?[E:$i,F:$i]:
% 0.20/0.56             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.20/0.56               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.20/0.56  thf(zf_stmt_1, axiom,
% 0.20/0.56    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.20/0.56     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.20/0.56       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.20/0.56         ( r2_hidden @ E @ A ) ) ))).
% 0.20/0.56  thf('11', plain,
% 0.20/0.56      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X9 : $i]:
% 0.20/0.56         ((zip_tseitin_0 @ X5 @ X4 @ X6 @ X7 @ X9)
% 0.20/0.56          | ~ (r2_hidden @ X4 @ X9)
% 0.20/0.56          | ~ (r2_hidden @ X5 @ X7)
% 0.20/0.56          | ((X6) != (k4_tarski @ X4 @ X5)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.56  thf('12', plain,
% 0.20/0.56      (![X4 : $i, X5 : $i, X7 : $i, X9 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X5 @ X7)
% 0.20/0.56          | ~ (r2_hidden @ X4 @ X9)
% 0.20/0.56          | (zip_tseitin_0 @ X5 @ X4 @ (k4_tarski @ X4 @ X5) @ X7 @ X9))),
% 0.20/0.56      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.56  thf('13', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.56         (((X0) = (k1_xboole_0))
% 0.20/0.56          | (zip_tseitin_0 @ (sk_B_1 @ X0) @ X2 @ 
% 0.20/0.56             (k4_tarski @ X2 @ (sk_B_1 @ X0)) @ X0 @ X1)
% 0.20/0.56          | ~ (r2_hidden @ X2 @ X1))),
% 0.20/0.56      inference('sup-', [status(thm)], ['10', '12'])).
% 0.20/0.56  thf('14', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         (((X0) = (k1_xboole_0))
% 0.20/0.56          | (zip_tseitin_0 @ (sk_B_1 @ X1) @ (sk_B_1 @ X0) @ 
% 0.20/0.56             (k4_tarski @ (sk_B_1 @ X0) @ (sk_B_1 @ X1)) @ X1 @ X0)
% 0.20/0.56          | ((X1) = (k1_xboole_0)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['9', '13'])).
% 0.20/0.56  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.20/0.56  thf(zf_stmt_3, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.20/0.56       ( ![D:$i]:
% 0.20/0.56         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.56           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.20/0.56  thf('15', plain,
% 0.20/0.56      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.56         (~ (zip_tseitin_0 @ X10 @ X11 @ X12 @ X13 @ X14)
% 0.20/0.56          | (r2_hidden @ X12 @ X15)
% 0.20/0.56          | ((X15) != (k2_zfmisc_1 @ X14 @ X13)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.56  thf('16', plain,
% 0.20/0.56      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.56         ((r2_hidden @ X12 @ (k2_zfmisc_1 @ X14 @ X13))
% 0.20/0.56          | ~ (zip_tseitin_0 @ X10 @ X11 @ X12 @ X13 @ X14))),
% 0.20/0.56      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.56  thf('17', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         (((X1) = (k1_xboole_0))
% 0.20/0.56          | ((X0) = (k1_xboole_0))
% 0.20/0.56          | (r2_hidden @ (k4_tarski @ (sk_B_1 @ X0) @ (sk_B_1 @ X1)) @ 
% 0.20/0.56             (k2_zfmisc_1 @ X0 @ X1)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['14', '16'])).
% 0.20/0.56  thf(d1_xboole_0, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.56  thf('18', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.56  thf('19', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         (((X1) = (k1_xboole_0))
% 0.20/0.56          | ((X0) = (k1_xboole_0))
% 0.20/0.56          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.56  thf('20', plain,
% 0.20/0.56      ((((sk_C) = (k4_tarski @ (k1_mcart_1 @ sk_C) @ (k2_mcart_1 @ sk_C)))
% 0.20/0.56        | ((sk_B_2) = (k1_xboole_0))
% 0.20/0.56        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['8', '19'])).
% 0.20/0.56  thf('21', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('22', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('23', plain,
% 0.20/0.56      (((sk_C) = (k4_tarski @ (k1_mcart_1 @ sk_C) @ (k2_mcart_1 @ sk_C)))),
% 0.20/0.56      inference('simplify_reflect-', [status(thm)], ['20', '21', '22'])).
% 0.20/0.56  thf('24', plain,
% 0.20/0.56      ((((sk_C) = (k4_tarski @ (k1_mcart_1 @ sk_C) @ sk_C)))
% 0.20/0.56         <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.20/0.56      inference('sup+', [status(thm)], ['1', '23'])).
% 0.20/0.56  thf(t20_mcart_1, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.20/0.56       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.20/0.56  thf('25', plain,
% 0.20/0.56      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.56         (((X24) != (k2_mcart_1 @ X24)) | ((X24) != (k4_tarski @ X25 @ X26)))),
% 0.20/0.56      inference('cnf', [status(esa)], [t20_mcart_1])).
% 0.20/0.56  thf('26', plain,
% 0.20/0.56      (![X25 : $i, X26 : $i]:
% 0.20/0.56         ((k4_tarski @ X25 @ X26) != (k2_mcart_1 @ (k4_tarski @ X25 @ X26)))),
% 0.20/0.56      inference('simplify', [status(thm)], ['25'])).
% 0.20/0.56  thf(t7_mcart_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.20/0.56       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.20/0.56  thf('27', plain,
% 0.20/0.56      (![X29 : $i, X31 : $i]: ((k2_mcart_1 @ (k4_tarski @ X29 @ X31)) = (X31))),
% 0.20/0.56      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.56  thf('28', plain, (![X25 : $i, X26 : $i]: ((k4_tarski @ X25 @ X26) != (X26))),
% 0.20/0.56      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.56  thf('29', plain, (($false) <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.20/0.56      inference('simplify_reflect-', [status(thm)], ['24', '28'])).
% 0.20/0.56  thf('30', plain,
% 0.20/0.56      ((((sk_C) = (k1_mcart_1 @ sk_C))) <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.20/0.56      inference('split', [status(esa)], ['0'])).
% 0.20/0.56  thf('31', plain,
% 0.20/0.56      (((sk_C) = (k4_tarski @ (k1_mcart_1 @ sk_C) @ (k2_mcart_1 @ sk_C)))),
% 0.20/0.56      inference('simplify_reflect-', [status(thm)], ['20', '21', '22'])).
% 0.20/0.56  thf('32', plain,
% 0.20/0.56      ((((sk_C) = (k4_tarski @ sk_C @ (k2_mcart_1 @ sk_C))))
% 0.20/0.56         <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.20/0.56      inference('sup+', [status(thm)], ['30', '31'])).
% 0.20/0.56  thf('33', plain,
% 0.20/0.56      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.56         (((X24) != (k1_mcart_1 @ X24)) | ((X24) != (k4_tarski @ X25 @ X26)))),
% 0.20/0.56      inference('cnf', [status(esa)], [t20_mcart_1])).
% 0.20/0.56  thf('34', plain,
% 0.20/0.56      (![X25 : $i, X26 : $i]:
% 0.20/0.56         ((k4_tarski @ X25 @ X26) != (k1_mcart_1 @ (k4_tarski @ X25 @ X26)))),
% 0.20/0.56      inference('simplify', [status(thm)], ['33'])).
% 0.20/0.56  thf('35', plain,
% 0.20/0.56      (![X29 : $i, X30 : $i]: ((k1_mcart_1 @ (k4_tarski @ X29 @ X30)) = (X29))),
% 0.20/0.56      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.56  thf('36', plain, (![X25 : $i, X26 : $i]: ((k4_tarski @ X25 @ X26) != (X25))),
% 0.20/0.56      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.56  thf('37', plain, (~ (((sk_C) = (k1_mcart_1 @ sk_C)))),
% 0.20/0.56      inference('simplify_reflect-', [status(thm)], ['32', '36'])).
% 0.20/0.56  thf('38', plain,
% 0.20/0.56      ((((sk_C) = (k2_mcart_1 @ sk_C))) | (((sk_C) = (k1_mcart_1 @ sk_C)))),
% 0.20/0.56      inference('split', [status(esa)], ['0'])).
% 0.20/0.56  thf('39', plain, ((((sk_C) = (k2_mcart_1 @ sk_C)))),
% 0.20/0.56      inference('sat_resolution*', [status(thm)], ['37', '38'])).
% 0.20/0.56  thf('40', plain, ($false),
% 0.20/0.56      inference('simpl_trail', [status(thm)], ['29', '39'])).
% 0.20/0.56  
% 0.20/0.56  % SZS output end Refutation
% 0.20/0.56  
% 0.20/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
