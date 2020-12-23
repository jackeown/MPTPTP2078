%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2rJ2X96N62

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:04 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   53 (  59 expanded)
%              Number of leaves         :   23 (  28 expanded)
%              Depth                    :   11
%              Number of atoms          :  254 ( 313 expanded)
%              Number of equality atoms :   28 (  33 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t59_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ k1_xboole_0 @ A )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) )
     => ( ( k7_relset_1 @ k1_xboole_0 @ A @ C @ B )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ k1_xboole_0 @ A )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) )
       => ( ( k7_relset_1 @ k1_xboole_0 @ A @ C @ B )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t59_funct_2])).

thf('0',plain,(
    ( k7_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ sk_B_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(rc2_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ( v1_xboole_0 @ B )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X32: $i] :
      ( v1_xboole_0 @ ( sk_B @ X32 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf('2',plain,(
    ! [X32: $i] :
      ( v1_xboole_0 @ ( sk_B @ X32 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( sk_B @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t1_zfmisc_1,axiom,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) )).

thf('7',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k1_zfmisc_1 @ X0 )
        = ( k1_tarski @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('10',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k2_zfmisc_1 @ X30 @ X31 )
        = k1_xboole_0 )
      | ( X30 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('11',plain,(
    ! [X31: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X31 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_tarski @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','13'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('15',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) )
      | ( v1_xboole_0 @ X34 )
      | ~ ( v1_xboole_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( sk_C = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','19'])).

thf('21',plain,(
    ( k7_relset_1 @ k1_xboole_0 @ sk_A @ k1_xboole_0 @ sk_B_1 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','20'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('22',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('23',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( ( k7_relset_1 @ X41 @ X42 @ X40 @ X43 )
        = ( k9_relat_1 @ X40 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
      = ( k9_relat_1 @ k1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t150_relat_1,axiom,(
    ! [A: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('25',plain,(
    ! [X39: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X39 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t150_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['21','26'])).

thf('28',plain,(
    $false ),
    inference(simplify,[status(thm)],['27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2rJ2X96N62
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:26:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.54  % Solved by: fo/fo7.sh
% 0.36/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.54  % done 140 iterations in 0.092s
% 0.36/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.54  % SZS output start Refutation
% 0.36/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.54  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.36/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.36/0.54  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.36/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.36/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.36/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.54  thf(t59_funct_2, conjecture,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ k1_xboole_0 @ A ) & 
% 0.36/0.54         ( m1_subset_1 @
% 0.36/0.54           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) ) =>
% 0.36/0.54       ( ( k7_relset_1 @ k1_xboole_0 @ A @ C @ B ) = ( k1_xboole_0 ) ) ))).
% 0.36/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.54    (~( ![A:$i,B:$i,C:$i]:
% 0.36/0.54        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ k1_xboole_0 @ A ) & 
% 0.36/0.54            ( m1_subset_1 @
% 0.36/0.54              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) ) =>
% 0.36/0.54          ( ( k7_relset_1 @ k1_xboole_0 @ A @ C @ B ) = ( k1_xboole_0 ) ) ) )),
% 0.36/0.54    inference('cnf.neg', [status(esa)], [t59_funct_2])).
% 0.36/0.54  thf('0', plain,
% 0.36/0.54      (((k7_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ sk_B_1) != (k1_xboole_0))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(rc2_subset_1, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ?[B:$i]:
% 0.36/0.54       ( ( v1_xboole_0 @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.36/0.54  thf('1', plain, (![X32 : $i]: (v1_xboole_0 @ (sk_B @ X32))),
% 0.36/0.54      inference('cnf', [status(esa)], [rc2_subset_1])).
% 0.36/0.54  thf('2', plain, (![X32 : $i]: (v1_xboole_0 @ (sk_B @ X32))),
% 0.36/0.55      inference('cnf', [status(esa)], [rc2_subset_1])).
% 0.36/0.55  thf(l13_xboole_0, axiom,
% 0.36/0.55    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.36/0.55  thf('3', plain,
% 0.36/0.55      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.36/0.55      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.36/0.55  thf('4', plain, (![X0 : $i]: ((sk_B @ X0) = (k1_xboole_0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.36/0.55  thf('5', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.55      inference('demod', [status(thm)], ['1', '4'])).
% 0.36/0.55  thf('6', plain,
% 0.36/0.55      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.36/0.55      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.36/0.55  thf(t1_zfmisc_1, axiom,
% 0.36/0.55    (( k1_zfmisc_1 @ k1_xboole_0 ) = ( k1_tarski @ k1_xboole_0 ))).
% 0.36/0.55  thf('7', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.36/0.55      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.36/0.55  thf('8', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (((k1_zfmisc_1 @ X0) = (k1_tarski @ k1_xboole_0))
% 0.36/0.55          | ~ (v1_xboole_0 @ X0))),
% 0.36/0.55      inference('sup+', [status(thm)], ['6', '7'])).
% 0.36/0.55  thf('9', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_A)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(t113_zfmisc_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.36/0.55       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.36/0.55  thf('10', plain,
% 0.36/0.55      (![X30 : $i, X31 : $i]:
% 0.36/0.55         (((k2_zfmisc_1 @ X30 @ X31) = (k1_xboole_0))
% 0.36/0.55          | ((X30) != (k1_xboole_0)))),
% 0.36/0.55      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.36/0.55  thf('11', plain,
% 0.36/0.55      (![X31 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X31) = (k1_xboole_0))),
% 0.36/0.55      inference('simplify', [status(thm)], ['10'])).
% 0.36/0.55  thf('12', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 0.36/0.55      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 0.36/0.55  thf('13', plain, ((m1_subset_1 @ sk_C @ (k1_tarski @ k1_xboole_0))),
% 0.36/0.55      inference('demod', [status(thm)], ['9', '11', '12'])).
% 0.36/0.55  thf('14', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.36/0.55      inference('sup+', [status(thm)], ['8', '13'])).
% 0.36/0.55  thf(cc1_subset_1, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( v1_xboole_0 @ A ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.36/0.55  thf('15', plain,
% 0.36/0.55      (![X34 : $i, X35 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35))
% 0.36/0.55          | (v1_xboole_0 @ X34)
% 0.36/0.55          | ~ (v1_xboole_0 @ X35))),
% 0.36/0.55      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.36/0.55  thf('16', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ sk_C))),
% 0.36/0.55      inference('sup-', [status(thm)], ['14', '15'])).
% 0.36/0.55  thf('17', plain, (![X0 : $i]: ((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ X0))),
% 0.36/0.55      inference('simplify', [status(thm)], ['16'])).
% 0.36/0.55  thf('18', plain,
% 0.36/0.55      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.36/0.55      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.36/0.55  thf('19', plain,
% 0.36/0.55      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((sk_C) = (k1_xboole_0)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['17', '18'])).
% 0.36/0.55  thf('20', plain, (((sk_C) = (k1_xboole_0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['5', '19'])).
% 0.36/0.55  thf('21', plain,
% 0.36/0.55      (((k7_relset_1 @ k1_xboole_0 @ sk_A @ k1_xboole_0 @ sk_B_1)
% 0.36/0.55         != (k1_xboole_0))),
% 0.36/0.55      inference('demod', [status(thm)], ['0', '20'])).
% 0.36/0.55  thf(t4_subset_1, axiom,
% 0.36/0.55    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.36/0.55  thf('22', plain,
% 0.36/0.55      (![X33 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X33))),
% 0.36/0.55      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.36/0.55  thf(redefinition_k7_relset_1, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.55       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.36/0.55  thf('23', plain,
% 0.36/0.55      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.36/0.55          | ((k7_relset_1 @ X41 @ X42 @ X40 @ X43) = (k9_relat_1 @ X40 @ X43)))),
% 0.36/0.55      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.36/0.55  thf('24', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.55         ((k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 0.36/0.55           = (k9_relat_1 @ k1_xboole_0 @ X2))),
% 0.36/0.55      inference('sup-', [status(thm)], ['22', '23'])).
% 0.36/0.55  thf(t150_relat_1, axiom,
% 0.36/0.55    (![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.36/0.55  thf('25', plain,
% 0.36/0.55      (![X39 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X39) = (k1_xboole_0))),
% 0.36/0.55      inference('cnf', [status(esa)], [t150_relat_1])).
% 0.36/0.55  thf('26', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.55         ((k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.36/0.55      inference('demod', [status(thm)], ['24', '25'])).
% 0.36/0.55  thf('27', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.36/0.55      inference('demod', [status(thm)], ['21', '26'])).
% 0.36/0.55  thf('28', plain, ($false), inference('simplify', [status(thm)], ['27'])).
% 0.36/0.55  
% 0.36/0.55  % SZS output end Refutation
% 0.36/0.55  
% 0.39/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
