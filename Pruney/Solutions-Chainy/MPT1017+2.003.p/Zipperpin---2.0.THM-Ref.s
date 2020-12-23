%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QRR3k67fTQ

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 103 expanded)
%              Number of leaves         :   22 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :  397 (1658 expanded)
%              Number of equality atoms :   10 (  46 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(t83_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( ( v2_funct_1 @ B )
          & ( ( k2_relset_1 @ A @ A @ B )
            = A ) )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( v3_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ( ( ( v2_funct_1 @ B )
            & ( ( k2_relset_1 @ A @ A @ B )
              = A ) )
         => ( ( v1_funct_1 @ B )
            & ( v1_funct_2 @ B @ A @ A )
            & ( v3_funct_2 @ B @ A @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t83_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
   <= ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
   <= ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('4',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ sk_B )
   <= ~ ( v1_funct_1 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('7',plain,(
    v1_funct_1 @ sk_B ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,(
    ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['4','7','10','11'])).

thf('13',plain,(
    ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc3_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v2_funct_1 @ C )
          & ( v2_funct_2 @ C @ B ) )
       => ( ( v1_funct_1 @ C )
          & ( v3_funct_2 @ C @ A @ B ) ) ) ) )).

thf('15',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_funct_1 @ X10 )
      | ~ ( v2_funct_1 @ X10 )
      | ~ ( v2_funct_2 @ X10 @ X11 )
      | ( v3_funct_2 @ X10 @ X12 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc3_funct_2])).

thf('16',plain,
    ( ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v2_funct_2 @ sk_B @ sk_A )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('18',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k2_relset_1 @ X8 @ X9 @ X7 )
        = ( k2_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('19',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['19','20'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('22',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_relat_1 @ X14 )
       != X13 )
      | ( v2_funct_2 @ X14 @ X13 )
      | ~ ( v5_relat_1 @ X14 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('23',plain,(
    ! [X14: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v5_relat_1 @ X14 @ ( k2_relat_1 @ X14 ) )
      | ( v2_funct_2 @ X14 @ ( k2_relat_1 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ~ ( v5_relat_1 @ sk_B @ sk_A )
    | ( v2_funct_2 @ sk_B @ ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('26',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v5_relat_1 @ X4 @ X6 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('27',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['19','20'])).

thf('29',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('32',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('33',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    v2_funct_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['24','27','28','33'])).

thf('35',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['16','34','35','36'])).

thf('38',plain,(
    $false ),
    inference(demod,[status(thm)],['13','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QRR3k67fTQ
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:29:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.45  % Solved by: fo/fo7.sh
% 0.22/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.45  % done 29 iterations in 0.015s
% 0.22/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.45  % SZS output start Refutation
% 0.22/0.45  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.22/0.45  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.45  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.45  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.45  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.22/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.45  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.45  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.22/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.45  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.22/0.45  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.22/0.45  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.22/0.45  thf(t83_funct_2, conjecture,
% 0.22/0.45    (![A:$i,B:$i]:
% 0.22/0.45     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.22/0.45         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.22/0.45       ( ( ( v2_funct_1 @ B ) & ( ( k2_relset_1 @ A @ A @ B ) = ( A ) ) ) =>
% 0.22/0.45         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.22/0.45           ( v3_funct_2 @ B @ A @ A ) & 
% 0.22/0.45           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ) ))).
% 0.22/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.45    (~( ![A:$i,B:$i]:
% 0.22/0.45        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.22/0.45            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.22/0.45          ( ( ( v2_funct_1 @ B ) & ( ( k2_relset_1 @ A @ A @ B ) = ( A ) ) ) =>
% 0.22/0.45            ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.22/0.45              ( v3_funct_2 @ B @ A @ A ) & 
% 0.22/0.45              ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ) ) )),
% 0.22/0.45    inference('cnf.neg', [status(esa)], [t83_funct_2])).
% 0.22/0.45  thf('0', plain,
% 0.22/0.45      ((~ (v1_funct_1 @ sk_B)
% 0.22/0.45        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.22/0.45        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.22/0.45        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.22/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.45  thf('1', plain,
% 0.22/0.45      ((~ (v3_funct_2 @ sk_B @ sk_A @ sk_A))
% 0.22/0.45         <= (~ ((v3_funct_2 @ sk_B @ sk_A @ sk_A)))),
% 0.22/0.45      inference('split', [status(esa)], ['0'])).
% 0.22/0.45  thf('2', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.22/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.45  thf('3', plain,
% 0.22/0.45      ((~ (v1_funct_2 @ sk_B @ sk_A @ sk_A))
% 0.22/0.45         <= (~ ((v1_funct_2 @ sk_B @ sk_A @ sk_A)))),
% 0.22/0.45      inference('split', [status(esa)], ['0'])).
% 0.22/0.45  thf('4', plain, (((v1_funct_2 @ sk_B @ sk_A @ sk_A))),
% 0.22/0.45      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.45  thf('5', plain, ((v1_funct_1 @ sk_B)),
% 0.22/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.45  thf('6', plain, ((~ (v1_funct_1 @ sk_B)) <= (~ ((v1_funct_1 @ sk_B)))),
% 0.22/0.45      inference('split', [status(esa)], ['0'])).
% 0.22/0.45  thf('7', plain, (((v1_funct_1 @ sk_B))),
% 0.22/0.45      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.45  thf('8', plain,
% 0.22/0.45      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))
% 0.22/0.45         <= (~
% 0.22/0.45             ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))))),
% 0.22/0.45      inference('split', [status(esa)], ['0'])).
% 0.22/0.45  thf('9', plain,
% 0.22/0.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.45  thf('10', plain,
% 0.22/0.45      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.22/0.45      inference('demod', [status(thm)], ['8', '9'])).
% 0.22/0.45  thf('11', plain,
% 0.22/0.45      (~ ((v3_funct_2 @ sk_B @ sk_A @ sk_A)) | 
% 0.22/0.45       ~ ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))) | 
% 0.22/0.45       ~ ((v1_funct_1 @ sk_B)) | ~ ((v1_funct_2 @ sk_B @ sk_A @ sk_A))),
% 0.22/0.45      inference('split', [status(esa)], ['0'])).
% 0.22/0.45  thf('12', plain, (~ ((v3_funct_2 @ sk_B @ sk_A @ sk_A))),
% 0.22/0.45      inference('sat_resolution*', [status(thm)], ['4', '7', '10', '11'])).
% 0.22/0.45  thf('13', plain, (~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.22/0.45      inference('simpl_trail', [status(thm)], ['1', '12'])).
% 0.22/0.45  thf('14', plain,
% 0.22/0.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.45  thf(cc3_funct_2, axiom,
% 0.22/0.45    (![A:$i,B:$i,C:$i]:
% 0.22/0.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.45       ( ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) =>
% 0.22/0.45         ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) ) ))).
% 0.22/0.45  thf('15', plain,
% 0.22/0.45      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.45         (~ (v1_funct_1 @ X10)
% 0.22/0.45          | ~ (v2_funct_1 @ X10)
% 0.22/0.45          | ~ (v2_funct_2 @ X10 @ X11)
% 0.22/0.45          | (v3_funct_2 @ X10 @ X12 @ X11)
% 0.22/0.45          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X11))))),
% 0.22/0.45      inference('cnf', [status(esa)], [cc3_funct_2])).
% 0.22/0.45  thf('16', plain,
% 0.22/0.45      (((v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.22/0.45        | ~ (v2_funct_2 @ sk_B @ sk_A)
% 0.22/0.45        | ~ (v2_funct_1 @ sk_B)
% 0.22/0.45        | ~ (v1_funct_1 @ sk_B))),
% 0.22/0.45      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.45  thf('17', plain,
% 0.22/0.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.45  thf(redefinition_k2_relset_1, axiom,
% 0.22/0.45    (![A:$i,B:$i,C:$i]:
% 0.22/0.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.45       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.22/0.45  thf('18', plain,
% 0.22/0.45      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.45         (((k2_relset_1 @ X8 @ X9 @ X7) = (k2_relat_1 @ X7))
% 0.22/0.45          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.22/0.45      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.22/0.45  thf('19', plain,
% 0.22/0.45      (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (k2_relat_1 @ sk_B))),
% 0.22/0.45      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.45  thf('20', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 0.22/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.45  thf('21', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.22/0.45      inference('sup+', [status(thm)], ['19', '20'])).
% 0.22/0.45  thf(d3_funct_2, axiom,
% 0.22/0.45    (![A:$i,B:$i]:
% 0.22/0.45     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.22/0.45       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.22/0.45  thf('22', plain,
% 0.22/0.45      (![X13 : $i, X14 : $i]:
% 0.22/0.45         (((k2_relat_1 @ X14) != (X13))
% 0.22/0.45          | (v2_funct_2 @ X14 @ X13)
% 0.22/0.45          | ~ (v5_relat_1 @ X14 @ X13)
% 0.22/0.45          | ~ (v1_relat_1 @ X14))),
% 0.22/0.45      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.22/0.45  thf('23', plain,
% 0.22/0.45      (![X14 : $i]:
% 0.22/0.45         (~ (v1_relat_1 @ X14)
% 0.22/0.45          | ~ (v5_relat_1 @ X14 @ (k2_relat_1 @ X14))
% 0.22/0.45          | (v2_funct_2 @ X14 @ (k2_relat_1 @ X14)))),
% 0.22/0.45      inference('simplify', [status(thm)], ['22'])).
% 0.22/0.45  thf('24', plain,
% 0.22/0.45      ((~ (v5_relat_1 @ sk_B @ sk_A)
% 0.22/0.45        | (v2_funct_2 @ sk_B @ (k2_relat_1 @ sk_B))
% 0.22/0.45        | ~ (v1_relat_1 @ sk_B))),
% 0.22/0.45      inference('sup-', [status(thm)], ['21', '23'])).
% 0.22/0.45  thf('25', plain,
% 0.22/0.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.45  thf(cc2_relset_1, axiom,
% 0.22/0.45    (![A:$i,B:$i,C:$i]:
% 0.22/0.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.45       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.22/0.45  thf('26', plain,
% 0.22/0.45      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.45         ((v5_relat_1 @ X4 @ X6)
% 0.22/0.45          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.22/0.45      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.45  thf('27', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 0.22/0.45      inference('sup-', [status(thm)], ['25', '26'])).
% 0.22/0.45  thf('28', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.22/0.45      inference('sup+', [status(thm)], ['19', '20'])).
% 0.22/0.45  thf('29', plain,
% 0.22/0.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.45  thf(cc2_relat_1, axiom,
% 0.22/0.45    (![A:$i]:
% 0.22/0.45     ( ( v1_relat_1 @ A ) =>
% 0.22/0.45       ( ![B:$i]:
% 0.22/0.45         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.22/0.45  thf('30', plain,
% 0.22/0.45      (![X0 : $i, X1 : $i]:
% 0.22/0.45         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.22/0.45          | (v1_relat_1 @ X0)
% 0.22/0.45          | ~ (v1_relat_1 @ X1))),
% 0.22/0.45      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.22/0.45  thf('31', plain,
% 0.22/0.45      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 0.22/0.45      inference('sup-', [status(thm)], ['29', '30'])).
% 0.22/0.45  thf(fc6_relat_1, axiom,
% 0.22/0.45    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.22/0.45  thf('32', plain,
% 0.22/0.45      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.22/0.45      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.22/0.45  thf('33', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.45      inference('demod', [status(thm)], ['31', '32'])).
% 0.22/0.45  thf('34', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 0.22/0.45      inference('demod', [status(thm)], ['24', '27', '28', '33'])).
% 0.22/0.45  thf('35', plain, ((v2_funct_1 @ sk_B)),
% 0.22/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.45  thf('36', plain, ((v1_funct_1 @ sk_B)),
% 0.22/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.45  thf('37', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.22/0.45      inference('demod', [status(thm)], ['16', '34', '35', '36'])).
% 0.22/0.45  thf('38', plain, ($false), inference('demod', [status(thm)], ['13', '37'])).
% 0.22/0.45  
% 0.22/0.45  % SZS output end Refutation
% 0.22/0.45  
% 0.22/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
