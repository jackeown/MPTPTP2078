%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4a1D6HFw5S

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:01 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   64 (  93 expanded)
%              Number of leaves         :   23 (  41 expanded)
%              Depth                    :   15
%              Number of atoms          :  524 ( 750 expanded)
%              Number of equality atoms :   37 (  54 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(t162_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t162_funct_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('2',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('3',plain,(
    ! [X9: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X12 @ ( k2_relat_1 @ X13 ) )
      | ( ( k9_relat_1 @ X13 @ ( k10_relat_1 @ X13 @ X12 ) )
        = X12 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('6',plain,(
    ! [X4: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X11: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k10_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
        = X1 ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,
    ( ( k9_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k10_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['2','8'])).

thf('10',plain,
    ( ( k9_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k10_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['2','8'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t159_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k9_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k9_relat_1 @ C @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('12',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k9_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) @ X7 )
        = ( k9_relat_1 @ X5 @ ( k9_relat_1 @ X6 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t159_relat_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X15 ) @ ( k6_relat_1 @ X14 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf('15',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X15 ) @ ( k6_relat_1 @ X14 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf('16',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k9_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) @ X7 )
        = ( k9_relat_1 @ X5 @ ( k9_relat_1 @ X6 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t159_relat_1])).

thf('17',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k9_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) @ X7 )
        = ( k9_relat_1 @ X5 @ ( k9_relat_1 @ X6 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t159_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k9_relat_1 @ ( k5_relat_1 @ X1 @ X3 ) @ ( k9_relat_1 @ X2 @ X0 ) )
        = ( k9_relat_1 @ X3 @ ( k9_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k9_relat_1 @ ( k5_relat_1 @ X1 @ X3 ) @ ( k9_relat_1 @ X2 @ X0 ) )
        = ( k9_relat_1 @ X3 @ ( k9_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X3 @ X2 ) )
        = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k9_relat_1 @ ( k5_relat_1 @ X3 @ ( k6_relat_1 @ X0 ) ) @ X2 ) ) )
      | ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['15','19'])).

thf('21',plain,(
    ! [X4: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('22',plain,(
    ! [X4: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k9_relat_1 @ X3 @ X2 ) )
        = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k9_relat_1 @ ( k5_relat_1 @ X3 @ ( k6_relat_1 @ X0 ) ) @ X2 ) ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X3 @ X1 ) ) @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) )
        = ( k9_relat_1 @ ( k6_relat_1 @ X3 ) @ ( k9_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X2 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','23'])).

thf('25',plain,(
    ! [X4: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X3 @ X1 ) ) @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ X3 ) @ ( k9_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X2 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k9_relat_1 @ ( k6_relat_1 @ X2 ) @ X1 ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k9_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['13','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k9_relat_1 @ ( k6_relat_1 @ X2 ) @ X0 ) )
        = ( k9_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X2 ) ) @ ( k6_relat_1 @ X1 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['12','27'])).

thf('29',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X15 ) @ ( k6_relat_1 @ X14 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf('30',plain,(
    ! [X4: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('31',plain,(
    ! [X4: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k9_relat_1 @ ( k6_relat_1 @ X2 ) @ X0 ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29','30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X0 ) ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      = ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k9_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
    = ( k9_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k10_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['10','35'])).

thf('37',plain,
    ( ( k9_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
    = sk_B ),
    inference('sup+',[status(thm)],['9','36'])).

thf('38',plain,(
    ( k9_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4a1D6HFw5S
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:51:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 23 iterations in 0.045s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.49  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.49  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.49  thf(t162_funct_1, conjecture,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.49       ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i]:
% 0.20/0.49        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.49          ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t162_funct_1])).
% 0.20/0.49  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t3_subset, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (![X1 : $i, X2 : $i]:
% 0.20/0.49         ((r1_tarski @ X1 @ X2) | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.49  thf('2', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.20/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.49  thf(t71_relat_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.20/0.49       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.49  thf('3', plain, (![X9 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X9)) = (X9))),
% 0.20/0.49      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.49  thf(t147_funct_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.49       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.20/0.49         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X12 : $i, X13 : $i]:
% 0.20/0.49         (~ (r1_tarski @ X12 @ (k2_relat_1 @ X13))
% 0.20/0.49          | ((k9_relat_1 @ X13 @ (k10_relat_1 @ X13 @ X12)) = (X12))
% 0.20/0.49          | ~ (v1_funct_1 @ X13)
% 0.20/0.49          | ~ (v1_relat_1 @ X13))),
% 0.20/0.49      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (r1_tarski @ X1 @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.20/0.49          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.20/0.49          | ((k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.20/0.49              (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)) = (X1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.49  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.20/0.49  thf('6', plain, (![X4 : $i]: (v1_relat_1 @ (k6_relat_1 @ X4))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.49  thf(fc3_funct_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.20/0.49       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.20/0.49  thf('7', plain, (![X11 : $i]: (v1_funct_1 @ (k6_relat_1 @ X11))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (r1_tarski @ X1 @ X0)
% 0.20/0.49          | ((k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.20/0.49              (k10_relat_1 @ (k6_relat_1 @ X0) @ X1)) = (X1)))),
% 0.20/0.49      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (((k9_relat_1 @ (k6_relat_1 @ sk_A) @ 
% 0.20/0.49         (k10_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)) = (sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['2', '8'])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (((k9_relat_1 @ (k6_relat_1 @ sk_A) @ 
% 0.20/0.49         (k10_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)) = (sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['2', '8'])).
% 0.20/0.49  thf(idempotence_k3_xboole_0, axiom,
% 0.20/0.49    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.20/0.49  thf('11', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.49      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.20/0.49  thf(t159_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ B ) =>
% 0.20/0.49       ( ![C:$i]:
% 0.20/0.49         ( ( v1_relat_1 @ C ) =>
% 0.20/0.49           ( ( k9_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.20/0.49             ( k9_relat_1 @ C @ ( k9_relat_1 @ B @ A ) ) ) ) ) ))).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X5)
% 0.20/0.49          | ((k9_relat_1 @ (k5_relat_1 @ X6 @ X5) @ X7)
% 0.20/0.49              = (k9_relat_1 @ X5 @ (k9_relat_1 @ X6 @ X7)))
% 0.20/0.49          | ~ (v1_relat_1 @ X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [t159_relat_1])).
% 0.20/0.49  thf('13', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.49      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.20/0.49  thf(t43_funct_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.20/0.49       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X14 : $i, X15 : $i]:
% 0.20/0.49         ((k5_relat_1 @ (k6_relat_1 @ X15) @ (k6_relat_1 @ X14))
% 0.20/0.49           = (k6_relat_1 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (![X14 : $i, X15 : $i]:
% 0.20/0.49         ((k5_relat_1 @ (k6_relat_1 @ X15) @ (k6_relat_1 @ X14))
% 0.20/0.49           = (k6_relat_1 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X5)
% 0.20/0.49          | ((k9_relat_1 @ (k5_relat_1 @ X6 @ X5) @ X7)
% 0.20/0.49              = (k9_relat_1 @ X5 @ (k9_relat_1 @ X6 @ X7)))
% 0.20/0.49          | ~ (v1_relat_1 @ X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [t159_relat_1])).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X5)
% 0.20/0.49          | ((k9_relat_1 @ (k5_relat_1 @ X6 @ X5) @ X7)
% 0.20/0.49              = (k9_relat_1 @ X5 @ (k9_relat_1 @ X6 @ X7)))
% 0.20/0.49          | ~ (v1_relat_1 @ X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [t159_relat_1])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         (((k9_relat_1 @ (k5_relat_1 @ X1 @ X3) @ (k9_relat_1 @ X2 @ X0))
% 0.20/0.49            = (k9_relat_1 @ X3 @ (k9_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0)))
% 0.20/0.49          | ~ (v1_relat_1 @ X2)
% 0.20/0.49          | ~ (v1_relat_1 @ X1)
% 0.20/0.49          | ~ (v1_relat_1 @ X1)
% 0.20/0.49          | ~ (v1_relat_1 @ X3))),
% 0.20/0.49      inference('sup+', [status(thm)], ['16', '17'])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X3)
% 0.20/0.49          | ~ (v1_relat_1 @ X1)
% 0.20/0.49          | ~ (v1_relat_1 @ X2)
% 0.20/0.49          | ((k9_relat_1 @ (k5_relat_1 @ X1 @ X3) @ (k9_relat_1 @ X2 @ X0))
% 0.20/0.49              = (k9_relat_1 @ X3 @ (k9_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0))))),
% 0.20/0.49      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         (((k9_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.20/0.49            (k9_relat_1 @ X3 @ X2))
% 0.20/0.49            = (k9_relat_1 @ (k6_relat_1 @ X1) @ 
% 0.20/0.49               (k9_relat_1 @ (k5_relat_1 @ X3 @ (k6_relat_1 @ X0)) @ X2)))
% 0.20/0.49          | ~ (v1_relat_1 @ X3)
% 0.20/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.20/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['15', '19'])).
% 0.20/0.49  thf('21', plain, (![X4 : $i]: (v1_relat_1 @ (k6_relat_1 @ X4))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.49  thf('22', plain, (![X4 : $i]: (v1_relat_1 @ (k6_relat_1 @ X4))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         (((k9_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.20/0.49            (k9_relat_1 @ X3 @ X2))
% 0.20/0.49            = (k9_relat_1 @ (k6_relat_1 @ X1) @ 
% 0.20/0.49               (k9_relat_1 @ (k5_relat_1 @ X3 @ (k6_relat_1 @ X0)) @ X2)))
% 0.20/0.49          | ~ (v1_relat_1 @ X3))),
% 0.20/0.49      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         (((k9_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X3 @ X1)) @ 
% 0.20/0.49            (k9_relat_1 @ (k6_relat_1 @ X0) @ X2))
% 0.20/0.49            = (k9_relat_1 @ (k6_relat_1 @ X3) @ 
% 0.20/0.49               (k9_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ X2)))
% 0.20/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['14', '23'])).
% 0.20/0.49  thf('25', plain, (![X4 : $i]: (v1_relat_1 @ (k6_relat_1 @ X4))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         ((k9_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X3 @ X1)) @ 
% 0.20/0.49           (k9_relat_1 @ (k6_relat_1 @ X0) @ X2))
% 0.20/0.49           = (k9_relat_1 @ (k6_relat_1 @ X3) @ 
% 0.20/0.49              (k9_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ X2)))),
% 0.20/0.49      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         ((k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.20/0.49           (k9_relat_1 @ (k6_relat_1 @ X2) @ X1))
% 0.20/0.49           = (k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.20/0.49              (k9_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X2)) @ X1)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['13', '26'])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (((k9_relat_1 @ (k6_relat_1 @ X1) @ 
% 0.20/0.49            (k9_relat_1 @ (k6_relat_1 @ X2) @ X0))
% 0.20/0.49            = (k9_relat_1 @ 
% 0.20/0.49               (k5_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X2)) @ 
% 0.20/0.49                (k6_relat_1 @ X1)) @ 
% 0.20/0.49               X0))
% 0.20/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X2)))
% 0.20/0.49          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['12', '27'])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      (![X14 : $i, X15 : $i]:
% 0.20/0.49         ((k5_relat_1 @ (k6_relat_1 @ X15) @ (k6_relat_1 @ X14))
% 0.20/0.49           = (k6_relat_1 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.20/0.49  thf('30', plain, (![X4 : $i]: (v1_relat_1 @ (k6_relat_1 @ X4))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.49  thf('31', plain, (![X4 : $i]: (v1_relat_1 @ (k6_relat_1 @ X4))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         ((k9_relat_1 @ (k6_relat_1 @ X1) @ 
% 0.20/0.49           (k9_relat_1 @ (k6_relat_1 @ X2) @ X0))
% 0.20/0.49           = (k9_relat_1 @ 
% 0.20/0.49              (k6_relat_1 @ (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2))) @ X0))),
% 0.20/0.49      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.20/0.49           (k9_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.20/0.49           = (k9_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X0 @ X0)) @ X1))),
% 0.20/0.49      inference('sup+', [status(thm)], ['11', '32'])).
% 0.20/0.49  thf('34', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.20/0.49      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((k9_relat_1 @ (k6_relat_1 @ X0) @ 
% 0.20/0.49           (k9_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.20/0.49           = (k9_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.20/0.49      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      (((k9_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 0.20/0.49         = (k9_relat_1 @ (k6_relat_1 @ sk_A) @ 
% 0.20/0.49            (k10_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['10', '35'])).
% 0.20/0.49  thf('37', plain, (((k9_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (sk_B))),
% 0.20/0.49      inference('sup+', [status(thm)], ['9', '36'])).
% 0.20/0.49  thf('38', plain, (((k9_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) != (sk_B))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('39', plain, ($false),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
