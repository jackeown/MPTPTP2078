%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QNGv9C60Xp

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:01 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   70 (  82 expanded)
%              Number of leaves         :   28 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :  416 ( 507 expanded)
%              Number of equality atoms :   37 (  49 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ( k9_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X35 ) @ ( k6_relat_1 @ X34 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X28 @ X27 ) )
        = ( k9_relat_1 @ X27 @ ( k2_relat_1 @ X28 ) ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('4',plain,(
    ! [X32: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X32 ) )
      = X32 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('5',plain,(
    ! [X32: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X32 ) )
      = X32 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('6',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('7',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k9_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4','5','6','7'])).

thf('9',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != sk_B ),
    inference(demod,[status(thm)],['0','8'])).

thf('10',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X35 ) @ ( k6_relat_1 @ X34 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf(t72_relat_1,axiom,(
    ! [A: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('11',plain,(
    ! [X33: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X33 ) )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('12',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_relat_1 @ X29 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X30 @ X29 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X29 ) @ ( k4_relat_1 @ X30 ) ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ X1 ) @ ( k4_relat_1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X33: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X33 ) )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('18',plain,(
    ! [X33: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X33 ) )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('19',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X35 ) @ ( k6_relat_1 @ X34 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf('20',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['16','17','18','19','20'])).

thf('22',plain,(
    ! [X31: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X31: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('26',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X7 @ X8 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('30',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('31',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('32',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X5 @ X6 )
      | ( r1_xboole_0 @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ~ ( r1_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('35',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_A ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('37',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('38',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    sk_B != sk_B ),
    inference(demod,[status(thm)],['9','25','38'])).

thf('40',plain,(
    $false ),
    inference(simplify,[status(thm)],['39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QNGv9C60Xp
% 0.15/0.38  % Computer   : n007.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 20:07:06 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.39  % Python version: Python 3.6.8
% 0.15/0.39  % Running in FO mode
% 0.24/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.59  % Solved by: fo/fo7.sh
% 0.24/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.59  % done 185 iterations in 0.099s
% 0.24/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.59  % SZS output start Refutation
% 0.24/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.24/0.59  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.24/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.24/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.24/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.59  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.24/0.59  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.24/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.24/0.59  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.24/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.59  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.24/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.24/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.59  thf(t162_funct_1, conjecture,
% 0.24/0.59    (![A:$i,B:$i]:
% 0.24/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.24/0.59       ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ))).
% 0.24/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.59    (~( ![A:$i,B:$i]:
% 0.24/0.59        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.24/0.59          ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) )),
% 0.24/0.59    inference('cnf.neg', [status(esa)], [t162_funct_1])).
% 0.24/0.59  thf('0', plain, (((k9_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) != (sk_B))),
% 0.24/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.59  thf(t43_funct_1, axiom,
% 0.24/0.59    (![A:$i,B:$i]:
% 0.24/0.59     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 0.24/0.59       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.24/0.59  thf('1', plain,
% 0.24/0.59      (![X34 : $i, X35 : $i]:
% 0.24/0.59         ((k5_relat_1 @ (k6_relat_1 @ X35) @ (k6_relat_1 @ X34))
% 0.24/0.59           = (k6_relat_1 @ (k3_xboole_0 @ X34 @ X35)))),
% 0.24/0.59      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.24/0.59  thf(t160_relat_1, axiom,
% 0.24/0.59    (![A:$i]:
% 0.24/0.59     ( ( v1_relat_1 @ A ) =>
% 0.24/0.59       ( ![B:$i]:
% 0.24/0.59         ( ( v1_relat_1 @ B ) =>
% 0.24/0.59           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.24/0.59             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.24/0.59  thf('2', plain,
% 0.24/0.59      (![X27 : $i, X28 : $i]:
% 0.24/0.59         (~ (v1_relat_1 @ X27)
% 0.24/0.59          | ((k2_relat_1 @ (k5_relat_1 @ X28 @ X27))
% 0.24/0.59              = (k9_relat_1 @ X27 @ (k2_relat_1 @ X28)))
% 0.24/0.59          | ~ (v1_relat_1 @ X28))),
% 0.24/0.59      inference('cnf', [status(esa)], [t160_relat_1])).
% 0.24/0.59  thf('3', plain,
% 0.24/0.59      (![X0 : $i, X1 : $i]:
% 0.24/0.59         (((k2_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.24/0.59            = (k9_relat_1 @ (k6_relat_1 @ X1) @ 
% 0.24/0.59               (k2_relat_1 @ (k6_relat_1 @ X0))))
% 0.24/0.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.24/0.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 0.24/0.59      inference('sup+', [status(thm)], ['1', '2'])).
% 0.24/0.59  thf(t71_relat_1, axiom,
% 0.24/0.59    (![A:$i]:
% 0.24/0.59     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.24/0.59       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.24/0.59  thf('4', plain, (![X32 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X32)) = (X32))),
% 0.24/0.59      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.24/0.59  thf('5', plain, (![X32 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X32)) = (X32))),
% 0.24/0.59      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.24/0.59  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.24/0.59  thf('6', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.24/0.59      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.24/0.59  thf('7', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.24/0.59      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.24/0.59  thf('8', plain,
% 0.24/0.59      (![X0 : $i, X1 : $i]:
% 0.24/0.59         ((k3_xboole_0 @ X1 @ X0) = (k9_relat_1 @ (k6_relat_1 @ X1) @ X0))),
% 0.24/0.59      inference('demod', [status(thm)], ['3', '4', '5', '6', '7'])).
% 0.24/0.59  thf('9', plain, (((k3_xboole_0 @ sk_A @ sk_B) != (sk_B))),
% 0.24/0.59      inference('demod', [status(thm)], ['0', '8'])).
% 0.24/0.59  thf('10', plain,
% 0.24/0.59      (![X34 : $i, X35 : $i]:
% 0.24/0.59         ((k5_relat_1 @ (k6_relat_1 @ X35) @ (k6_relat_1 @ X34))
% 0.24/0.59           = (k6_relat_1 @ (k3_xboole_0 @ X34 @ X35)))),
% 0.24/0.59      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.24/0.59  thf(t72_relat_1, axiom,
% 0.24/0.59    (![A:$i]: ( ( k4_relat_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 0.24/0.59  thf('11', plain,
% 0.24/0.59      (![X33 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X33)) = (k6_relat_1 @ X33))),
% 0.24/0.59      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.24/0.59  thf(t54_relat_1, axiom,
% 0.24/0.59    (![A:$i]:
% 0.24/0.59     ( ( v1_relat_1 @ A ) =>
% 0.24/0.59       ( ![B:$i]:
% 0.24/0.59         ( ( v1_relat_1 @ B ) =>
% 0.24/0.59           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.24/0.59             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 0.24/0.59  thf('12', plain,
% 0.24/0.59      (![X29 : $i, X30 : $i]:
% 0.24/0.59         (~ (v1_relat_1 @ X29)
% 0.24/0.59          | ((k4_relat_1 @ (k5_relat_1 @ X30 @ X29))
% 0.24/0.59              = (k5_relat_1 @ (k4_relat_1 @ X29) @ (k4_relat_1 @ X30)))
% 0.24/0.59          | ~ (v1_relat_1 @ X30))),
% 0.24/0.59      inference('cnf', [status(esa)], [t54_relat_1])).
% 0.24/0.59  thf('13', plain,
% 0.24/0.59      (![X0 : $i, X1 : $i]:
% 0.24/0.59         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.24/0.59            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 0.24/0.59          | ~ (v1_relat_1 @ X1)
% 0.24/0.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.24/0.59      inference('sup+', [status(thm)], ['11', '12'])).
% 0.24/0.59  thf('14', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.24/0.59      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.24/0.59  thf('15', plain,
% 0.24/0.59      (![X0 : $i, X1 : $i]:
% 0.24/0.59         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_relat_1 @ X0)))
% 0.24/0.59            = (k5_relat_1 @ (k6_relat_1 @ X0) @ (k4_relat_1 @ X1)))
% 0.24/0.59          | ~ (v1_relat_1 @ X1))),
% 0.24/0.59      inference('demod', [status(thm)], ['13', '14'])).
% 0.24/0.59  thf('16', plain,
% 0.24/0.59      (![X0 : $i, X1 : $i]:
% 0.24/0.59         (((k4_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.24/0.59            = (k5_relat_1 @ (k6_relat_1 @ X1) @ 
% 0.24/0.59               (k4_relat_1 @ (k6_relat_1 @ X0))))
% 0.24/0.59          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.24/0.59      inference('sup+', [status(thm)], ['10', '15'])).
% 0.24/0.59  thf('17', plain,
% 0.24/0.59      (![X33 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X33)) = (k6_relat_1 @ X33))),
% 0.24/0.59      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.24/0.59  thf('18', plain,
% 0.24/0.59      (![X33 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X33)) = (k6_relat_1 @ X33))),
% 0.24/0.59      inference('cnf', [status(esa)], [t72_relat_1])).
% 0.24/0.59  thf('19', plain,
% 0.24/0.59      (![X34 : $i, X35 : $i]:
% 0.24/0.59         ((k5_relat_1 @ (k6_relat_1 @ X35) @ (k6_relat_1 @ X34))
% 0.24/0.59           = (k6_relat_1 @ (k3_xboole_0 @ X34 @ X35)))),
% 0.24/0.59      inference('cnf', [status(esa)], [t43_funct_1])).
% 0.24/0.59  thf('20', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.24/0.59      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.24/0.59  thf('21', plain,
% 0.24/0.59      (![X0 : $i, X1 : $i]:
% 0.24/0.59         ((k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 0.24/0.59           = (k6_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.24/0.59      inference('demod', [status(thm)], ['16', '17', '18', '19', '20'])).
% 0.24/0.59  thf('22', plain, (![X31 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X31)) = (X31))),
% 0.24/0.59      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.24/0.59  thf('23', plain,
% 0.24/0.59      (![X0 : $i, X1 : $i]:
% 0.24/0.59         ((k1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 0.24/0.59           = (k3_xboole_0 @ X0 @ X1))),
% 0.24/0.59      inference('sup+', [status(thm)], ['21', '22'])).
% 0.24/0.59  thf('24', plain, (![X31 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X31)) = (X31))),
% 0.24/0.59      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.24/0.59  thf('25', plain,
% 0.24/0.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.24/0.59      inference('demod', [status(thm)], ['23', '24'])).
% 0.24/0.59  thf(t79_xboole_1, axiom,
% 0.24/0.59    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.24/0.59  thf('26', plain,
% 0.24/0.59      (![X7 : $i, X8 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X7 @ X8) @ X8)),
% 0.24/0.59      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.24/0.59  thf(symmetry_r1_xboole_0, axiom,
% 0.24/0.59    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.24/0.59  thf('27', plain,
% 0.24/0.59      (![X0 : $i, X1 : $i]:
% 0.24/0.59         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.24/0.59      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.24/0.59  thf('28', plain,
% 0.24/0.59      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.24/0.59      inference('sup-', [status(thm)], ['26', '27'])).
% 0.24/0.59  thf('29', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.24/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.59  thf(t3_subset, axiom,
% 0.24/0.59    (![A:$i,B:$i]:
% 0.24/0.59     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.24/0.59  thf('30', plain,
% 0.24/0.59      (![X23 : $i, X24 : $i]:
% 0.24/0.59         ((r1_tarski @ X23 @ X24) | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 0.24/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.24/0.59  thf('31', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.24/0.59      inference('sup-', [status(thm)], ['29', '30'])).
% 0.24/0.59  thf(t63_xboole_1, axiom,
% 0.24/0.59    (![A:$i,B:$i,C:$i]:
% 0.24/0.59     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.24/0.59       ( r1_xboole_0 @ A @ C ) ))).
% 0.24/0.59  thf('32', plain,
% 0.24/0.59      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.24/0.59         (~ (r1_tarski @ X4 @ X5)
% 0.24/0.59          | ~ (r1_xboole_0 @ X5 @ X6)
% 0.24/0.59          | (r1_xboole_0 @ X4 @ X6))),
% 0.24/0.59      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.24/0.59  thf('33', plain,
% 0.24/0.59      (![X0 : $i]: ((r1_xboole_0 @ sk_B @ X0) | ~ (r1_xboole_0 @ sk_A @ X0))),
% 0.24/0.59      inference('sup-', [status(thm)], ['31', '32'])).
% 0.24/0.59  thf('34', plain,
% 0.24/0.59      (![X0 : $i]: (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_A))),
% 0.24/0.59      inference('sup-', [status(thm)], ['28', '33'])).
% 0.24/0.59  thf(t83_xboole_1, axiom,
% 0.24/0.59    (![A:$i,B:$i]:
% 0.24/0.59     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.24/0.59  thf('35', plain,
% 0.24/0.59      (![X9 : $i, X10 : $i]:
% 0.24/0.59         (((k4_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_xboole_0 @ X9 @ X10))),
% 0.24/0.59      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.24/0.59  thf('36', plain,
% 0.24/0.59      (![X0 : $i]: ((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_A)) = (sk_B))),
% 0.24/0.59      inference('sup-', [status(thm)], ['34', '35'])).
% 0.24/0.59  thf(t48_xboole_1, axiom,
% 0.24/0.59    (![A:$i,B:$i]:
% 0.24/0.59     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.24/0.59  thf('37', plain,
% 0.24/0.59      (![X2 : $i, X3 : $i]:
% 0.24/0.59         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ X3))
% 0.24/0.59           = (k3_xboole_0 @ X2 @ X3))),
% 0.24/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.24/0.59  thf('38', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.24/0.59      inference('sup+', [status(thm)], ['36', '37'])).
% 0.24/0.59  thf('39', plain, (((sk_B) != (sk_B))),
% 0.24/0.59      inference('demod', [status(thm)], ['9', '25', '38'])).
% 0.24/0.59  thf('40', plain, ($false), inference('simplify', [status(thm)], ['39'])).
% 0.24/0.59  
% 0.24/0.59  % SZS output end Refutation
% 0.24/0.59  
% 0.42/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
