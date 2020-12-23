%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UI6GqniRAB

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:27 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   52 (  62 expanded)
%              Number of leaves         :   24 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :  257 ( 314 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v5_funct_1_type,type,(
    v5_funct_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('0',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(cc1_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_funct_1 @ A ) ) )).

thf('2',plain,(
    ! [X6: $i] :
      ( ( v1_funct_1 @ X6 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('3',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(d20_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( v5_funct_1 @ B @ A )
          <=> ! [C: $i] :
                ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
               => ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ ( k1_funct_1 @ A @ C ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X8 ) @ ( k1_relat_1 @ X7 ) )
      | ( v5_funct_1 @ X7 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d20_funct_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v5_funct_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v5_funct_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v5_funct_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v5_funct_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('10',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v5_funct_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('13',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( sk_B_1 @ X1 ) @ X1 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('14',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( sk_B_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( sk_B_1 @ ( k1_zfmisc_1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( sk_B_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v5_funct_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','19'])).

thf(t174_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( v5_funct_1 @ k1_xboole_0 @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( v5_funct_1 @ k1_xboole_0 @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t174_funct_1])).

thf('21',plain,(
    ~ ( v5_funct_1 @ k1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UI6GqniRAB
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:54:44 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 23 iterations in 0.016s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.46  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.46  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.46  thf(v5_funct_1_type, type, v5_funct_1: $i > $i > $o).
% 0.20/0.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.46  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.46  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.46  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.46  thf('0', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.46      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.46  thf(cc1_relat_1, axiom,
% 0.20/0.46    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.20/0.46  thf('1', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 0.20/0.46      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.20/0.46  thf(cc1_funct_1, axiom,
% 0.20/0.46    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_funct_1 @ A ) ))).
% 0.20/0.46  thf('2', plain, (![X6 : $i]: ((v1_funct_1 @ X6) | ~ (v1_xboole_0 @ X6))),
% 0.20/0.46      inference('cnf', [status(esa)], [cc1_funct_1])).
% 0.20/0.46  thf(t60_relat_1, axiom,
% 0.20/0.46    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.20/0.46     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.46  thf('3', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.46  thf(d20_funct_1, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.46       ( ![B:$i]:
% 0.20/0.46         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.46           ( ( v5_funct_1 @ B @ A ) <=>
% 0.20/0.46             ( ![C:$i]:
% 0.20/0.46               ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.46                 ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ ( k1_funct_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.20/0.46  thf('4', plain,
% 0.20/0.46      (![X7 : $i, X8 : $i]:
% 0.20/0.46         (~ (v1_relat_1 @ X7)
% 0.20/0.46          | ~ (v1_funct_1 @ X7)
% 0.20/0.46          | (r2_hidden @ (sk_C @ X7 @ X8) @ (k1_relat_1 @ X7))
% 0.20/0.46          | (v5_funct_1 @ X7 @ X8)
% 0.20/0.46          | ~ (v1_funct_1 @ X8)
% 0.20/0.46          | ~ (v1_relat_1 @ X8))),
% 0.20/0.46      inference('cnf', [status(esa)], [d20_funct_1])).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         ((r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.20/0.46          | ~ (v1_relat_1 @ X0)
% 0.20/0.46          | ~ (v1_funct_1 @ X0)
% 0.20/0.46          | (v5_funct_1 @ k1_xboole_0 @ X0)
% 0.20/0.46          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.20/0.46          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.20/0.46      inference('sup+', [status(thm)], ['3', '4'])).
% 0.20/0.46  thf('6', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.20/0.46          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.46          | (v5_funct_1 @ k1_xboole_0 @ X0)
% 0.20/0.46          | ~ (v1_funct_1 @ X0)
% 0.20/0.46          | ~ (v1_relat_1 @ X0)
% 0.20/0.46          | (r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['2', '5'])).
% 0.20/0.46  thf('7', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.46      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.46  thf('8', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.46          | (v5_funct_1 @ k1_xboole_0 @ X0)
% 0.20/0.46          | ~ (v1_funct_1 @ X0)
% 0.20/0.46          | ~ (v1_relat_1 @ X0)
% 0.20/0.46          | (r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.20/0.46      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.46  thf('9', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.20/0.46          | (r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.20/0.46          | ~ (v1_relat_1 @ X0)
% 0.20/0.46          | ~ (v1_funct_1 @ X0)
% 0.20/0.46          | (v5_funct_1 @ k1_xboole_0 @ X0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['1', '8'])).
% 0.20/0.46  thf('10', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.46      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.46  thf('11', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         ((r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.20/0.46          | ~ (v1_relat_1 @ X0)
% 0.20/0.46          | ~ (v1_funct_1 @ X0)
% 0.20/0.46          | (v5_funct_1 @ k1_xboole_0 @ X0))),
% 0.20/0.46      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.46  thf(t7_xboole_0, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.46          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.20/0.46  thf('12', plain,
% 0.20/0.46      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.20/0.46      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.46  thf(existence_m1_subset_1, axiom,
% 0.20/0.46    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.20/0.46  thf('13', plain, (![X1 : $i]: (m1_subset_1 @ (sk_B_1 @ X1) @ X1)),
% 0.20/0.46      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.20/0.46  thf(t5_subset, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.20/0.46          ( v1_xboole_0 @ C ) ) ))).
% 0.20/0.46  thf('14', plain,
% 0.20/0.46      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.46         (~ (r2_hidden @ X2 @ X3)
% 0.20/0.46          | ~ (v1_xboole_0 @ X4)
% 0.20/0.46          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t5_subset])).
% 0.20/0.46  thf('15', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         (~ (v1_xboole_0 @ X0)
% 0.20/0.46          | ~ (r2_hidden @ X1 @ (sk_B_1 @ (k1_zfmisc_1 @ X0))))),
% 0.20/0.46      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.46  thf('16', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (((sk_B_1 @ (k1_zfmisc_1 @ X0)) = (k1_xboole_0))
% 0.20/0.46          | ~ (v1_xboole_0 @ X0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['12', '15'])).
% 0.20/0.46  thf('17', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         (~ (v1_xboole_0 @ X0)
% 0.20/0.46          | ~ (r2_hidden @ X1 @ (sk_B_1 @ (k1_zfmisc_1 @ X0))))),
% 0.20/0.46      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.46  thf('18', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         (~ (r2_hidden @ X1 @ k1_xboole_0)
% 0.20/0.46          | ~ (v1_xboole_0 @ X0)
% 0.20/0.46          | ~ (v1_xboole_0 @ X0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.46  thf('19', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.20/0.46      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.46  thf('20', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         ((v5_funct_1 @ k1_xboole_0 @ X0)
% 0.20/0.46          | ~ (v1_funct_1 @ X0)
% 0.20/0.46          | ~ (v1_relat_1 @ X0)
% 0.20/0.46          | ~ (v1_xboole_0 @ X1))),
% 0.20/0.46      inference('sup-', [status(thm)], ['11', '19'])).
% 0.20/0.46  thf(t174_funct_1, conjecture,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.46       ( v5_funct_1 @ k1_xboole_0 @ A ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i]:
% 0.20/0.46        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.46          ( v5_funct_1 @ k1_xboole_0 @ A ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t174_funct_1])).
% 0.20/0.46  thf('21', plain, (~ (v5_funct_1 @ k1_xboole_0 @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('22', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (~ (v1_xboole_0 @ X0) | ~ (v1_relat_1 @ sk_A) | ~ (v1_funct_1 @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.46  thf('23', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('24', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('25', plain, (![X0 : $i]: ~ (v1_xboole_0 @ X0)),
% 0.20/0.46      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.20/0.46  thf('26', plain, ($false), inference('sup-', [status(thm)], ['0', '25'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
