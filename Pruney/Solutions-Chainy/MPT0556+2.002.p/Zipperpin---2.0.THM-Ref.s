%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vvQGFkbUwi

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:33 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 102 expanded)
%              Number of leaves         :   19 (  38 expanded)
%              Depth                    :   17
%              Number of atoms          :  388 ( 949 expanded)
%              Number of equality atoms :    3 (   4 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(t158_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ! [D: $i] :
          ( ( v1_relat_1 @ D )
         => ( ( ( r1_tarski @ C @ D )
              & ( r1_tarski @ A @ B ) )
           => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ D @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ! [D: $i] :
            ( ( v1_relat_1 @ D )
           => ( ( ( r1_tarski @ C @ D )
                & ( r1_tarski @ A @ B ) )
             => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ D @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t158_relat_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) )
        = ( k9_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) )
        = ( k9_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X13 @ X14 ) @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X0: $i,X2: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    r1_tarski @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t106_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ! [D: $i] :
          ( ( v1_relat_1 @ D )
         => ( ( ( r1_tarski @ C @ D )
              & ( r1_tarski @ A @ B ) )
           => ( r1_tarski @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ D @ B ) ) ) ) ) )).

thf('11',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( r1_tarski @ ( k7_relat_1 @ X6 @ X7 ) @ ( k7_relat_1 @ X5 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X5 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t106_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ ( k7_relat_1 @ sk_C @ X1 ) @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_relat_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ ( k7_relat_1 @ sk_C @ X1 ) @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    r1_tarski @ ( k7_relat_1 @ sk_C @ sk_A ) @ ( k7_relat_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['9','15'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('17',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( r1_tarski @ ( k2_relat_1 @ X12 ) @ ( k2_relat_1 @ X11 ) )
      | ~ ( r1_tarski @ X12 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) )
    | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('20',plain,(
    r1_tarski @ ( k7_relat_1 @ sk_C @ sk_A ) @ ( k7_relat_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['9','15'])).

thf('21',plain,(
    ! [X0: $i,X2: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('22',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( k7_relat_1 @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_B ) )
    | ( v1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( v1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','27'])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['8','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['2','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_D @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['1','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    $false ),
    inference(demod,[status(thm)],['0','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vvQGFkbUwi
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:29:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.57  % Solved by: fo/fo7.sh
% 0.22/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.57  % done 121 iterations in 0.080s
% 0.22/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.57  % SZS output start Refutation
% 0.22/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.57  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.57  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.22/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.57  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.22/0.57  thf(t158_relat_1, conjecture,
% 0.22/0.57    (![A:$i,B:$i,C:$i]:
% 0.22/0.57     ( ( v1_relat_1 @ C ) =>
% 0.22/0.57       ( ![D:$i]:
% 0.22/0.57         ( ( v1_relat_1 @ D ) =>
% 0.22/0.57           ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 0.22/0.57             ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ D @ B ) ) ) ) ) ))).
% 0.22/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.57    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.57        ( ( v1_relat_1 @ C ) =>
% 0.22/0.57          ( ![D:$i]:
% 0.22/0.57            ( ( v1_relat_1 @ D ) =>
% 0.22/0.57              ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 0.22/0.57                ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ D @ B ) ) ) ) ) ) )),
% 0.22/0.57    inference('cnf.neg', [status(esa)], [t158_relat_1])).
% 0.22/0.57  thf('0', plain,
% 0.22/0.57      (~ (r1_tarski @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_D @ sk_B))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(t148_relat_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( v1_relat_1 @ B ) =>
% 0.22/0.57       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.22/0.57  thf('1', plain,
% 0.22/0.57      (![X9 : $i, X10 : $i]:
% 0.22/0.57         (((k2_relat_1 @ (k7_relat_1 @ X9 @ X10)) = (k9_relat_1 @ X9 @ X10))
% 0.22/0.57          | ~ (v1_relat_1 @ X9))),
% 0.22/0.57      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.22/0.57  thf('2', plain,
% 0.22/0.57      (![X9 : $i, X10 : $i]:
% 0.22/0.57         (((k2_relat_1 @ (k7_relat_1 @ X9 @ X10)) = (k9_relat_1 @ X9 @ X10))
% 0.22/0.57          | ~ (v1_relat_1 @ X9))),
% 0.22/0.57      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.22/0.57  thf(t88_relat_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 0.22/0.57  thf('3', plain,
% 0.22/0.57      (![X13 : $i, X14 : $i]:
% 0.22/0.57         ((r1_tarski @ (k7_relat_1 @ X13 @ X14) @ X13) | ~ (v1_relat_1 @ X13))),
% 0.22/0.57      inference('cnf', [status(esa)], [t88_relat_1])).
% 0.22/0.57  thf(t3_subset, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.57  thf('4', plain,
% 0.22/0.57      (![X0 : $i, X2 : $i]:
% 0.22/0.57         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.22/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.57  thf('5', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         (~ (v1_relat_1 @ X0)
% 0.22/0.57          | (m1_subset_1 @ (k7_relat_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.57  thf(cc2_relat_1, axiom,
% 0.22/0.57    (![A:$i]:
% 0.22/0.57     ( ( v1_relat_1 @ A ) =>
% 0.22/0.57       ( ![B:$i]:
% 0.22/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.22/0.57  thf('6', plain,
% 0.22/0.57      (![X3 : $i, X4 : $i]:
% 0.22/0.57         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.22/0.57          | (v1_relat_1 @ X3)
% 0.22/0.57          | ~ (v1_relat_1 @ X4))),
% 0.22/0.57      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.22/0.57  thf('7', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         (~ (v1_relat_1 @ X0)
% 0.22/0.57          | ~ (v1_relat_1 @ X0)
% 0.22/0.57          | (v1_relat_1 @ (k7_relat_1 @ X0 @ X1)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.57  thf('8', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         ((v1_relat_1 @ (k7_relat_1 @ X0 @ X1)) | ~ (v1_relat_1 @ X0))),
% 0.22/0.57      inference('simplify', [status(thm)], ['7'])).
% 0.22/0.57  thf('9', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('10', plain, ((r1_tarski @ sk_C @ sk_D)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(t106_relat_1, axiom,
% 0.22/0.57    (![A:$i,B:$i,C:$i]:
% 0.22/0.57     ( ( v1_relat_1 @ C ) =>
% 0.22/0.57       ( ![D:$i]:
% 0.22/0.57         ( ( v1_relat_1 @ D ) =>
% 0.22/0.57           ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 0.22/0.57             ( r1_tarski @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ D @ B ) ) ) ) ) ))).
% 0.22/0.57  thf('11', plain,
% 0.22/0.57      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.22/0.57         (~ (v1_relat_1 @ X5)
% 0.22/0.57          | (r1_tarski @ (k7_relat_1 @ X6 @ X7) @ (k7_relat_1 @ X5 @ X8))
% 0.22/0.57          | ~ (r1_tarski @ X6 @ X5)
% 0.22/0.57          | ~ (r1_tarski @ X7 @ X8)
% 0.22/0.57          | ~ (v1_relat_1 @ X6))),
% 0.22/0.57      inference('cnf', [status(esa)], [t106_relat_1])).
% 0.22/0.57  thf('12', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         (~ (v1_relat_1 @ sk_C)
% 0.22/0.57          | ~ (r1_tarski @ X1 @ X0)
% 0.22/0.57          | (r1_tarski @ (k7_relat_1 @ sk_C @ X1) @ (k7_relat_1 @ sk_D @ X0))
% 0.22/0.57          | ~ (v1_relat_1 @ sk_D))),
% 0.22/0.57      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.57  thf('13', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('14', plain, ((v1_relat_1 @ sk_D)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('15', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         (~ (r1_tarski @ X1 @ X0)
% 0.22/0.57          | (r1_tarski @ (k7_relat_1 @ sk_C @ X1) @ (k7_relat_1 @ sk_D @ X0)))),
% 0.22/0.57      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.22/0.57  thf('16', plain,
% 0.22/0.57      ((r1_tarski @ (k7_relat_1 @ sk_C @ sk_A) @ (k7_relat_1 @ sk_D @ sk_B))),
% 0.22/0.57      inference('sup-', [status(thm)], ['9', '15'])).
% 0.22/0.57  thf(t25_relat_1, axiom,
% 0.22/0.57    (![A:$i]:
% 0.22/0.57     ( ( v1_relat_1 @ A ) =>
% 0.22/0.57       ( ![B:$i]:
% 0.22/0.57         ( ( v1_relat_1 @ B ) =>
% 0.22/0.57           ( ( r1_tarski @ A @ B ) =>
% 0.22/0.57             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.22/0.57               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.22/0.57  thf('17', plain,
% 0.22/0.57      (![X11 : $i, X12 : $i]:
% 0.22/0.57         (~ (v1_relat_1 @ X11)
% 0.22/0.57          | (r1_tarski @ (k2_relat_1 @ X12) @ (k2_relat_1 @ X11))
% 0.22/0.57          | ~ (r1_tarski @ X12 @ X11)
% 0.22/0.57          | ~ (v1_relat_1 @ X12))),
% 0.22/0.57      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.22/0.57  thf('18', plain,
% 0.22/0.57      ((~ (v1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A))
% 0.22/0.57        | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_C @ sk_A)) @ 
% 0.22/0.57           (k2_relat_1 @ (k7_relat_1 @ sk_D @ sk_B)))
% 0.22/0.57        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ sk_B)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.57  thf('19', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         ((v1_relat_1 @ (k7_relat_1 @ X0 @ X1)) | ~ (v1_relat_1 @ X0))),
% 0.22/0.57      inference('simplify', [status(thm)], ['7'])).
% 0.22/0.57  thf('20', plain,
% 0.22/0.57      ((r1_tarski @ (k7_relat_1 @ sk_C @ sk_A) @ (k7_relat_1 @ sk_D @ sk_B))),
% 0.22/0.57      inference('sup-', [status(thm)], ['9', '15'])).
% 0.22/0.57  thf('21', plain,
% 0.22/0.57      (![X0 : $i, X2 : $i]:
% 0.22/0.57         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.22/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.57  thf('22', plain,
% 0.22/0.57      ((m1_subset_1 @ (k7_relat_1 @ sk_C @ sk_A) @ 
% 0.22/0.57        (k1_zfmisc_1 @ (k7_relat_1 @ sk_D @ sk_B)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.57  thf('23', plain,
% 0.22/0.57      (![X3 : $i, X4 : $i]:
% 0.22/0.57         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.22/0.57          | (v1_relat_1 @ X3)
% 0.22/0.57          | ~ (v1_relat_1 @ X4))),
% 0.22/0.57      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.22/0.57  thf('24', plain,
% 0.22/0.57      ((~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ sk_B))
% 0.22/0.57        | (v1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.57  thf('25', plain,
% 0.22/0.57      ((~ (v1_relat_1 @ sk_D) | (v1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['19', '24'])).
% 0.22/0.57  thf('26', plain, ((v1_relat_1 @ sk_D)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('27', plain, ((v1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A))),
% 0.22/0.57      inference('demod', [status(thm)], ['25', '26'])).
% 0.22/0.57  thf('28', plain,
% 0.22/0.57      (((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_C @ sk_A)) @ 
% 0.22/0.57         (k2_relat_1 @ (k7_relat_1 @ sk_D @ sk_B)))
% 0.22/0.57        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ sk_B)))),
% 0.22/0.57      inference('demod', [status(thm)], ['18', '27'])).
% 0.22/0.57  thf('29', plain,
% 0.22/0.57      ((~ (v1_relat_1 @ sk_D)
% 0.22/0.57        | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_C @ sk_A)) @ 
% 0.22/0.57           (k2_relat_1 @ (k7_relat_1 @ sk_D @ sk_B))))),
% 0.22/0.57      inference('sup-', [status(thm)], ['8', '28'])).
% 0.22/0.57  thf('30', plain, ((v1_relat_1 @ sk_D)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('31', plain,
% 0.22/0.57      ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_C @ sk_A)) @ 
% 0.22/0.57        (k2_relat_1 @ (k7_relat_1 @ sk_D @ sk_B)))),
% 0.22/0.57      inference('demod', [status(thm)], ['29', '30'])).
% 0.22/0.57  thf('32', plain,
% 0.22/0.57      (((r1_tarski @ (k9_relat_1 @ sk_C @ sk_A) @ 
% 0.22/0.57         (k2_relat_1 @ (k7_relat_1 @ sk_D @ sk_B)))
% 0.22/0.57        | ~ (v1_relat_1 @ sk_C))),
% 0.22/0.57      inference('sup+', [status(thm)], ['2', '31'])).
% 0.22/0.57  thf('33', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('34', plain,
% 0.22/0.57      ((r1_tarski @ (k9_relat_1 @ sk_C @ sk_A) @ 
% 0.22/0.57        (k2_relat_1 @ (k7_relat_1 @ sk_D @ sk_B)))),
% 0.22/0.57      inference('demod', [status(thm)], ['32', '33'])).
% 0.22/0.57  thf('35', plain,
% 0.22/0.57      (((r1_tarski @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_D @ sk_B))
% 0.22/0.57        | ~ (v1_relat_1 @ sk_D))),
% 0.22/0.57      inference('sup+', [status(thm)], ['1', '34'])).
% 0.22/0.57  thf('36', plain, ((v1_relat_1 @ sk_D)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('37', plain,
% 0.22/0.57      ((r1_tarski @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_D @ sk_B))),
% 0.22/0.57      inference('demod', [status(thm)], ['35', '36'])).
% 0.22/0.57  thf('38', plain, ($false), inference('demod', [status(thm)], ['0', '37'])).
% 0.22/0.57  
% 0.22/0.57  % SZS output end Refutation
% 0.22/0.57  
% 0.22/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
