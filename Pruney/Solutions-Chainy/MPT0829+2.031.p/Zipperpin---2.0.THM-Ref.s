%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kbDXbxVhRH

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:13 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   48 (  66 expanded)
%              Number of leaves         :   17 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :  347 ( 709 expanded)
%              Number of equality atoms :   17 (  34 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(t32_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( r1_tarski @ ( k6_relat_1 @ B ) @ C )
       => ( ( r1_tarski @ B @ ( k1_relset_1 @ A @ B @ C ) )
          & ( B
            = ( k2_relset_1 @ A @ B @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
       => ( ( r1_tarski @ ( k6_relat_1 @ B ) @ C )
         => ( ( r1_tarski @ B @ ( k1_relset_1 @ A @ B @ C ) )
            & ( B
              = ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t32_relset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X7 @ X8 @ X9 ) @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('2',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('4',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('6',plain,
    ( ( k2_xboole_0 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['4','5'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('8',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
    = sk_B ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ ( k6_relat_1 @ sk_B ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t30_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( r1_tarski @ ( k6_relat_1 @ C ) @ D )
       => ( ( r1_tarski @ C @ ( k1_relset_1 @ A @ B @ D ) )
          & ( r1_tarski @ C @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )).

thf('11',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k6_relat_1 @ X10 ) @ X11 )
      | ( r1_tarski @ X10 @ ( k2_relset_1 @ X12 @ X13 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[t30_relset_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( r1_tarski @ ( k6_relat_1 @ X0 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r1_tarski @ sk_B @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('15',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
    = ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( sk_B
    = ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['8','15'])).

thf('17',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) )
    | ( sk_B
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( sk_B
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
   <= ( sk_B
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,(
    r1_tarski @ ( k6_relat_1 @ sk_B ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k6_relat_1 @ X10 ) @ X11 )
      | ( r1_tarski @ X10 @ ( k1_relset_1 @ X12 @ X13 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[t30_relset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) )
      | ~ ( r1_tarski @ ( k6_relat_1 @ X0 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r1_tarski @ sk_B @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) )
   <= ~ ( r1_tarski @ sk_B @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['17'])).

thf('25',plain,(
    r1_tarski @ sk_B @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_B
     != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) )
    | ~ ( r1_tarski @ sk_B @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['17'])).

thf('27',plain,(
    sk_B
 != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['25','26'])).

thf('28',plain,(
    sk_B
 != ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['18','27'])).

thf('29',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['16','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kbDXbxVhRH
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:35:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.48  % Solved by: fo/fo7.sh
% 0.22/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.48  % done 33 iterations in 0.018s
% 0.22/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.48  % SZS output start Refutation
% 0.22/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.48  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.22/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.48  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.22/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.48  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.22/0.48  thf(t32_relset_1, conjecture,
% 0.22/0.48    (![A:$i,B:$i,C:$i]:
% 0.22/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.48       ( ( r1_tarski @ ( k6_relat_1 @ B ) @ C ) =>
% 0.22/0.48         ( ( r1_tarski @ B @ ( k1_relset_1 @ A @ B @ C ) ) & 
% 0.22/0.48           ( ( B ) = ( k2_relset_1 @ A @ B @ C ) ) ) ) ))).
% 0.22/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.48        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.48          ( ( r1_tarski @ ( k6_relat_1 @ B ) @ C ) =>
% 0.22/0.48            ( ( r1_tarski @ B @ ( k1_relset_1 @ A @ B @ C ) ) & 
% 0.22/0.48              ( ( B ) = ( k2_relset_1 @ A @ B @ C ) ) ) ) ) )),
% 0.22/0.48    inference('cnf.neg', [status(esa)], [t32_relset_1])).
% 0.22/0.48  thf('0', plain,
% 0.22/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(dt_k2_relset_1, axiom,
% 0.22/0.48    (![A:$i,B:$i,C:$i]:
% 0.22/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.48       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.22/0.48  thf('1', plain,
% 0.22/0.48      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.48         ((m1_subset_1 @ (k2_relset_1 @ X7 @ X8 @ X9) @ (k1_zfmisc_1 @ X8))
% 0.22/0.48          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.22/0.48      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.22/0.48  thf('2', plain,
% 0.22/0.48      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_B))),
% 0.22/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.48  thf(t3_subset, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.48  thf('3', plain,
% 0.22/0.48      (![X4 : $i, X5 : $i]:
% 0.22/0.48         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.22/0.48      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.48  thf('4', plain, ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B @ sk_C) @ sk_B)),
% 0.22/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.48  thf(t12_xboole_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.22/0.48  thf('5', plain,
% 0.22/0.48      (![X2 : $i, X3 : $i]:
% 0.22/0.48         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.22/0.48      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.22/0.48  thf('6', plain,
% 0.22/0.48      (((k2_xboole_0 @ (k2_relset_1 @ sk_A @ sk_B @ sk_C) @ sk_B) = (sk_B))),
% 0.22/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.48  thf(commutativity_k2_xboole_0, axiom,
% 0.22/0.48    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.22/0.48  thf('7', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.48      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.22/0.48  thf('8', plain,
% 0.22/0.48      (((k2_xboole_0 @ sk_B @ (k2_relset_1 @ sk_A @ sk_B @ sk_C)) = (sk_B))),
% 0.22/0.48      inference('demod', [status(thm)], ['6', '7'])).
% 0.22/0.48  thf('9', plain, ((r1_tarski @ (k6_relat_1 @ sk_B) @ sk_C)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('10', plain,
% 0.22/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(t30_relset_1, axiom,
% 0.22/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.48     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.48       ( ( r1_tarski @ ( k6_relat_1 @ C ) @ D ) =>
% 0.22/0.48         ( ( r1_tarski @ C @ ( k1_relset_1 @ A @ B @ D ) ) & 
% 0.22/0.48           ( r1_tarski @ C @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.22/0.48  thf('11', plain,
% 0.22/0.48      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.48         (~ (r1_tarski @ (k6_relat_1 @ X10) @ X11)
% 0.22/0.48          | (r1_tarski @ X10 @ (k2_relset_1 @ X12 @ X13 @ X11))
% 0.22/0.48          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.22/0.48      inference('cnf', [status(esa)], [t30_relset_1])).
% 0.22/0.48  thf('12', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         ((r1_tarski @ X0 @ (k2_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.22/0.48          | ~ (r1_tarski @ (k6_relat_1 @ X0) @ sk_C))),
% 0.22/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.48  thf('13', plain, ((r1_tarski @ sk_B @ (k2_relset_1 @ sk_A @ sk_B @ sk_C))),
% 0.22/0.48      inference('sup-', [status(thm)], ['9', '12'])).
% 0.22/0.48  thf('14', plain,
% 0.22/0.48      (![X2 : $i, X3 : $i]:
% 0.22/0.48         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.22/0.48      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.22/0.48  thf('15', plain,
% 0.22/0.48      (((k2_xboole_0 @ sk_B @ (k2_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.22/0.48         = (k2_relset_1 @ sk_A @ sk_B @ sk_C))),
% 0.22/0.48      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.48  thf('16', plain, (((sk_B) = (k2_relset_1 @ sk_A @ sk_B @ sk_C))),
% 0.22/0.48      inference('sup+', [status(thm)], ['8', '15'])).
% 0.22/0.48  thf('17', plain,
% 0.22/0.48      ((~ (r1_tarski @ sk_B @ (k1_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.22/0.48        | ((sk_B) != (k2_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('18', plain,
% 0.22/0.48      ((((sk_B) != (k2_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.22/0.48         <= (~ (((sk_B) = (k2_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.22/0.48      inference('split', [status(esa)], ['17'])).
% 0.22/0.48  thf('19', plain, ((r1_tarski @ (k6_relat_1 @ sk_B) @ sk_C)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('20', plain,
% 0.22/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('21', plain,
% 0.22/0.48      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.48         (~ (r1_tarski @ (k6_relat_1 @ X10) @ X11)
% 0.22/0.48          | (r1_tarski @ X10 @ (k1_relset_1 @ X12 @ X13 @ X11))
% 0.22/0.48          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.22/0.48      inference('cnf', [status(esa)], [t30_relset_1])).
% 0.22/0.48  thf('22', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         ((r1_tarski @ X0 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.22/0.48          | ~ (r1_tarski @ (k6_relat_1 @ X0) @ sk_C))),
% 0.22/0.48      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.48  thf('23', plain, ((r1_tarski @ sk_B @ (k1_relset_1 @ sk_A @ sk_B @ sk_C))),
% 0.22/0.48      inference('sup-', [status(thm)], ['19', '22'])).
% 0.22/0.48  thf('24', plain,
% 0.22/0.48      ((~ (r1_tarski @ sk_B @ (k1_relset_1 @ sk_A @ sk_B @ sk_C)))
% 0.22/0.48         <= (~ ((r1_tarski @ sk_B @ (k1_relset_1 @ sk_A @ sk_B @ sk_C))))),
% 0.22/0.48      inference('split', [status(esa)], ['17'])).
% 0.22/0.48  thf('25', plain, (((r1_tarski @ sk_B @ (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.48  thf('26', plain,
% 0.22/0.48      (~ (((sk_B) = (k2_relset_1 @ sk_A @ sk_B @ sk_C))) | 
% 0.22/0.48       ~ ((r1_tarski @ sk_B @ (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.22/0.48      inference('split', [status(esa)], ['17'])).
% 0.22/0.48  thf('27', plain, (~ (((sk_B) = (k2_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.22/0.48      inference('sat_resolution*', [status(thm)], ['25', '26'])).
% 0.22/0.48  thf('28', plain, (((sk_B) != (k2_relset_1 @ sk_A @ sk_B @ sk_C))),
% 0.22/0.48      inference('simpl_trail', [status(thm)], ['18', '27'])).
% 0.22/0.48  thf('29', plain, ($false),
% 0.22/0.48      inference('simplify_reflect-', [status(thm)], ['16', '28'])).
% 0.22/0.48  
% 0.22/0.48  % SZS output end Refutation
% 0.22/0.48  
% 0.22/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
