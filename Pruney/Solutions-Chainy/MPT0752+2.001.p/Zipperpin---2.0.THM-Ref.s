%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.D4pYq7F9Gi

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   47 (  62 expanded)
%              Number of leaves         :   18 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :  172 ( 293 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_ordinal1_type,type,(
    v5_ordinal1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(t45_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v5_ordinal1 @ k1_xboole_0 )
      & ( v1_funct_1 @ k1_xboole_0 )
      & ( v5_relat_1 @ k1_xboole_0 @ A )
      & ( v1_relat_1 @ k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v5_ordinal1 @ k1_xboole_0 )
        & ( v1_funct_1 @ k1_xboole_0 )
        & ( v5_relat_1 @ k1_xboole_0 @ A )
        & ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t45_ordinal1])).

thf('0',plain,
    ( ~ ( v5_ordinal1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v5_relat_1 @ k1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v5_relat_1 @ k1_xboole_0 @ sk_A )
   <= ~ ( v5_relat_1 @ k1_xboole_0 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('2',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(cc4_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v5_ordinal1 @ A ) ) )).

thf('3',plain,(
    ! [X9: $i] :
      ( ( v5_ordinal1 @ X9 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc4_ordinal1])).

thf('4',plain,(
    v5_ordinal1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ~ ( v5_ordinal1 @ k1_xboole_0 )
   <= ~ ( v5_ordinal1 @ k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('6',plain,(
    v5_ordinal1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(cc1_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_funct_1 @ A ) ) )).

thf('8',plain,(
    ! [X8: $i] :
      ( ( v1_funct_1 @ X8 )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_1])).

thf('9',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ~ ( v1_funct_1 @ k1_xboole_0 )
   <= ~ ( v1_funct_1 @ k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('11',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['9','10'])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('12',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
   <= ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('16',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( v5_relat_1 @ k1_xboole_0 @ sk_A )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v5_ordinal1 @ k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('18',plain,(
    ~ ( v5_relat_1 @ k1_xboole_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['6','11','16','17'])).

thf('19',plain,(
    ~ ( v5_relat_1 @ k1_xboole_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','18'])).

thf(rc3_ordinal1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ( v5_ordinal1 @ B )
      & ( v1_funct_1 @ B )
      & ( v5_relat_1 @ B @ A )
      & ( v1_relat_1 @ B ) ) )).

thf('20',plain,(
    ! [X10: $i] :
      ( v5_relat_1 @ ( sk_B @ X10 ) @ X10 ) ),
    inference(cnf,[status(esa)],[rc3_ordinal1])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('21',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ B ) )
         => ( v5_relat_1 @ C @ A ) ) ) )).

thf('22',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v5_relat_1 @ X5 @ X7 )
      | ~ ( v5_relat_1 @ X6 @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc6_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v5_relat_1 @ X0 @ X1 )
      | ( v5_relat_1 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v5_relat_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X10: $i] :
      ( v1_relat_1 @ ( sk_B @ X10 ) ) ),
    inference(cnf,[status(esa)],[rc3_ordinal1])).

thf('26',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    $false ),
    inference(demod,[status(thm)],['19','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.D4pYq7F9Gi
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:35:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 23 iterations in 0.013s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.47  thf(v5_ordinal1_type, type, v5_ordinal1: $i > $o).
% 0.21/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.47  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.47  thf(t45_ordinal1, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v5_ordinal1 @ k1_xboole_0 ) & ( v1_funct_1 @ k1_xboole_0 ) & 
% 0.21/0.47       ( v5_relat_1 @ k1_xboole_0 @ A ) & ( v1_relat_1 @ k1_xboole_0 ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]:
% 0.21/0.47        ( ( v5_ordinal1 @ k1_xboole_0 ) & ( v1_funct_1 @ k1_xboole_0 ) & 
% 0.21/0.47          ( v5_relat_1 @ k1_xboole_0 @ A ) & ( v1_relat_1 @ k1_xboole_0 ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t45_ordinal1])).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      ((~ (v5_ordinal1 @ k1_xboole_0)
% 0.21/0.47        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.21/0.47        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.47        | ~ (v5_relat_1 @ k1_xboole_0 @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      ((~ (v5_relat_1 @ k1_xboole_0 @ sk_A))
% 0.21/0.47         <= (~ ((v5_relat_1 @ k1_xboole_0 @ sk_A)))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.47  thf('2', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.47      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.47  thf(cc4_ordinal1, axiom,
% 0.21/0.47    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v5_ordinal1 @ A ) ))).
% 0.21/0.47  thf('3', plain, (![X9 : $i]: ((v5_ordinal1 @ X9) | ~ (v1_xboole_0 @ X9))),
% 0.21/0.47      inference('cnf', [status(esa)], [cc4_ordinal1])).
% 0.21/0.47  thf('4', plain, ((v5_ordinal1 @ k1_xboole_0)),
% 0.21/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      ((~ (v5_ordinal1 @ k1_xboole_0)) <= (~ ((v5_ordinal1 @ k1_xboole_0)))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('6', plain, (((v5_ordinal1 @ k1_xboole_0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.47  thf('7', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.47      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.47  thf(cc1_funct_1, axiom,
% 0.21/0.47    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_funct_1 @ A ) ))).
% 0.21/0.47  thf('8', plain, (![X8 : $i]: ((v1_funct_1 @ X8) | ~ (v1_xboole_0 @ X8))),
% 0.21/0.47      inference('cnf', [status(esa)], [cc1_funct_1])).
% 0.21/0.47  thf('9', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.21/0.47      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      ((~ (v1_funct_1 @ k1_xboole_0)) <= (~ ((v1_funct_1 @ k1_xboole_0)))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('11', plain, (((v1_funct_1 @ k1_xboole_0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.47  thf(cc1_relat_1, axiom,
% 0.21/0.47    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.21/0.47  thf('12', plain, (![X4 : $i]: ((v1_relat_1 @ X4) | ~ (v1_xboole_0 @ X4))),
% 0.21/0.47      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      ((~ (v1_relat_1 @ k1_xboole_0)) <= (~ ((v1_relat_1 @ k1_xboole_0)))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      ((~ (v1_xboole_0 @ k1_xboole_0)) <= (~ ((v1_relat_1 @ k1_xboole_0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.47  thf('15', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.47      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.47  thf('16', plain, (((v1_relat_1 @ k1_xboole_0))),
% 0.21/0.47      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      (~ ((v5_relat_1 @ k1_xboole_0 @ sk_A)) | 
% 0.21/0.47       ~ ((v1_relat_1 @ k1_xboole_0)) | ~ ((v1_funct_1 @ k1_xboole_0)) | 
% 0.21/0.47       ~ ((v5_ordinal1 @ k1_xboole_0))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('18', plain, (~ ((v5_relat_1 @ k1_xboole_0 @ sk_A))),
% 0.21/0.47      inference('sat_resolution*', [status(thm)], ['6', '11', '16', '17'])).
% 0.21/0.47  thf('19', plain, (~ (v5_relat_1 @ k1_xboole_0 @ sk_A)),
% 0.21/0.47      inference('simpl_trail', [status(thm)], ['1', '18'])).
% 0.21/0.47  thf(rc3_ordinal1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ?[B:$i]:
% 0.21/0.47       ( ( v5_ordinal1 @ B ) & ( v1_funct_1 @ B ) & ( v5_relat_1 @ B @ A ) & 
% 0.21/0.47         ( v1_relat_1 @ B ) ) ))).
% 0.21/0.47  thf('20', plain, (![X10 : $i]: (v5_relat_1 @ (sk_B @ X10) @ X10)),
% 0.21/0.47      inference('cnf', [status(esa)], [rc3_ordinal1])).
% 0.21/0.47  thf(t4_subset_1, axiom,
% 0.21/0.47    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.47  thf('21', plain,
% 0.21/0.47      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.47  thf(cc6_relat_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.21/0.47       ( ![C:$i]:
% 0.21/0.47         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ B ) ) => ( v5_relat_1 @ C @ A ) ) ) ))).
% 0.21/0.47  thf('22', plain,
% 0.21/0.47      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.21/0.47          | (v5_relat_1 @ X5 @ X7)
% 0.21/0.47          | ~ (v5_relat_1 @ X6 @ X7)
% 0.21/0.47          | ~ (v1_relat_1 @ X6))),
% 0.21/0.47      inference('cnf', [status(esa)], [cc6_relat_1])).
% 0.21/0.47  thf('23', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ X0)
% 0.21/0.47          | ~ (v5_relat_1 @ X0 @ X1)
% 0.21/0.47          | (v5_relat_1 @ k1_xboole_0 @ X1))),
% 0.21/0.47      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.47  thf('24', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((v5_relat_1 @ k1_xboole_0 @ X0) | ~ (v1_relat_1 @ (sk_B @ X0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['20', '23'])).
% 0.21/0.47  thf('25', plain, (![X10 : $i]: (v1_relat_1 @ (sk_B @ X10))),
% 0.21/0.47      inference('cnf', [status(esa)], [rc3_ordinal1])).
% 0.21/0.47  thf('26', plain, (![X0 : $i]: (v5_relat_1 @ k1_xboole_0 @ X0)),
% 0.21/0.47      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.47  thf('27', plain, ($false), inference('demod', [status(thm)], ['19', '26'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
