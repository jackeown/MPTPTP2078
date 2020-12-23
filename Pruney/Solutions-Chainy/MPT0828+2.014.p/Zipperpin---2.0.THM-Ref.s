%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Z8Q65ejMRC

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:06 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 116 expanded)
%              Number of leaves         :   29 (  47 expanded)
%              Depth                    :   13
%              Number of atoms          :  480 (1057 expanded)
%              Number of equality atoms :   30 (  55 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t31_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( ( r1_tarski @ ( k6_relat_1 @ B ) @ C )
       => ( ( B
            = ( k1_relset_1 @ B @ A @ C ) )
          & ( r1_tarski @ B @ ( k2_relset_1 @ B @ A @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
       => ( ( r1_tarski @ ( k6_relat_1 @ B ) @ C )
         => ( ( B
              = ( k1_relset_1 @ B @ A @ C ) )
            & ( r1_tarski @ B @ ( k2_relset_1 @ B @ A @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_relset_1])).

thf('0',plain,
    ( ( sk_B
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) )
    | ~ ( r1_tarski @ sk_B @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ~ ( r1_tarski @ sk_B @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r1_tarski @ ( k6_relat_1 @ sk_B ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( r1_tarski @ ( k1_relat_1 @ X11 ) @ ( k1_relat_1 @ X10 ) )
      | ~ ( r1_tarski @ X11 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ sk_B ) ) @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('6',plain,(
    ! [X12: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('11',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r1_tarski @ sk_B @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['4','5','6','11'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('13',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('14',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('16',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v4_relat_1 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('17',plain,(
    v4_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['15','16'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('18',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v4_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k1_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['9','10'])).

thf('21',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('23',plain,
    ( ( k2_xboole_0 @ ( k1_relat_1 @ sk_C ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['21','22'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('25',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_relat_1 @ sk_C ) )
    = sk_B ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['14','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('28',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('29',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_B
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( sk_B
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,
    ( ( sk_B
     != ( k1_relat_1 @ sk_C ) )
   <= ( sk_B
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_B != sk_B )
   <= ( sk_B
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,
    ( sk_B
    = ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
    | ( sk_B
     != ( k1_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('35',plain,(
    ~ ( r1_tarski @ sk_B @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( r1_tarski @ sk_B @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['1','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('38',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X24 @ X22 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('39',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r1_tarski @ ( k6_relat_1 @ sk_B ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( r1_tarski @ ( k2_relat_1 @ X11 ) @ ( k2_relat_1 @ X10 ) )
      | ~ ( r1_tarski @ X11 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('42',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) )
    | ( r1_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ sk_B ) ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('44',plain,(
    ! [X13: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('45',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['9','10'])).

thf('46',plain,(
    r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['42','43','44','45'])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['36','39','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Z8Q65ejMRC
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:00:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 56 iterations in 0.021s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.47  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.20/0.47  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.47  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.47  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.47  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(t31_relset_1, conjecture,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.20/0.47       ( ( r1_tarski @ ( k6_relat_1 @ B ) @ C ) =>
% 0.20/0.47         ( ( ( B ) = ( k1_relset_1 @ B @ A @ C ) ) & 
% 0.20/0.47           ( r1_tarski @ B @ ( k2_relset_1 @ B @ A @ C ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.47        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.20/0.47          ( ( r1_tarski @ ( k6_relat_1 @ B ) @ C ) =>
% 0.20/0.47            ( ( ( B ) = ( k1_relset_1 @ B @ A @ C ) ) & 
% 0.20/0.47              ( r1_tarski @ B @ ( k2_relset_1 @ B @ A @ C ) ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t31_relset_1])).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      ((((sk_B) != (k1_relset_1 @ sk_B @ sk_A @ sk_C))
% 0.20/0.47        | ~ (r1_tarski @ sk_B @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      ((~ (r1_tarski @ sk_B @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.20/0.47         <= (~ ((r1_tarski @ sk_B @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.20/0.47      inference('split', [status(esa)], ['0'])).
% 0.20/0.47  thf('2', plain, ((r1_tarski @ (k6_relat_1 @ sk_B) @ sk_C)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t25_relat_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ A ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( v1_relat_1 @ B ) =>
% 0.20/0.47           ( ( r1_tarski @ A @ B ) =>
% 0.20/0.47             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.20/0.47               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (![X10 : $i, X11 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ X10)
% 0.20/0.47          | (r1_tarski @ (k1_relat_1 @ X11) @ (k1_relat_1 @ X10))
% 0.20/0.47          | ~ (r1_tarski @ X11 @ X10)
% 0.20/0.47          | ~ (v1_relat_1 @ X11))),
% 0.20/0.47      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      ((~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 0.20/0.47        | (r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ sk_B)) @ (k1_relat_1 @ sk_C))
% 0.20/0.47        | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.47  thf(fc4_funct_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.20/0.47       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.20/0.47  thf('5', plain, (![X14 : $i]: (v1_relat_1 @ (k6_relat_1 @ X14))),
% 0.20/0.47      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.20/0.47  thf(t71_relat_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.20/0.47       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.47  thf('6', plain, (![X12 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X12)) = (X12))),
% 0.20/0.47      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(cc2_relat_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ A ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (![X4 : $i, X5 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.20/0.47          | (v1_relat_1 @ X4)
% 0.20/0.47          | ~ (v1_relat_1 @ X5))),
% 0.20/0.47      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.47  thf(fc6_relat_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.20/0.47      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.47  thf('11', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.47      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.47  thf('12', plain, ((r1_tarski @ sk_B @ (k1_relat_1 @ sk_C))),
% 0.20/0.47      inference('demod', [status(thm)], ['4', '5', '6', '11'])).
% 0.20/0.47  thf(t12_xboole_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (![X2 : $i, X3 : $i]:
% 0.20/0.47         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (((k2_xboole_0 @ sk_B @ (k1_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(cc2_relset_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.47       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.47  thf('16', plain,
% 0.20/0.47      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.47         ((v4_relat_1 @ X16 @ X17)
% 0.20/0.47          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.20/0.47      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.47  thf('17', plain, ((v4_relat_1 @ sk_C @ sk_B)),
% 0.20/0.47      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.47  thf(d18_relat_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ B ) =>
% 0.20/0.47       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      (![X6 : $i, X7 : $i]:
% 0.20/0.47         (~ (v4_relat_1 @ X6 @ X7)
% 0.20/0.47          | (r1_tarski @ (k1_relat_1 @ X6) @ X7)
% 0.20/0.47          | ~ (v1_relat_1 @ X6))),
% 0.20/0.47      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.20/0.47  thf('19', plain,
% 0.20/0.47      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.47  thf('20', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.47      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.47  thf('21', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_B)),
% 0.20/0.47      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.47  thf('22', plain,
% 0.20/0.47      (![X2 : $i, X3 : $i]:
% 0.20/0.47         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.20/0.47      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.20/0.47  thf('23', plain, (((k2_xboole_0 @ (k1_relat_1 @ sk_C) @ sk_B) = (sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.47  thf(commutativity_k2_xboole_0, axiom,
% 0.20/0.47    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.20/0.47  thf('24', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.47      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.47  thf('25', plain, (((k2_xboole_0 @ sk_B @ (k1_relat_1 @ sk_C)) = (sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['23', '24'])).
% 0.20/0.47  thf('26', plain, (((k1_relat_1 @ sk_C) = (sk_B))),
% 0.20/0.47      inference('sup+', [status(thm)], ['14', '25'])).
% 0.20/0.47  thf('27', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.47       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.47  thf('28', plain,
% 0.20/0.47      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.47         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 0.20/0.47          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.20/0.47      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.47  thf('29', plain,
% 0.20/0.47      (((k1_relset_1 @ sk_B @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.47  thf('30', plain,
% 0.20/0.47      ((((sk_B) != (k1_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.20/0.47         <= (~ (((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.20/0.47      inference('split', [status(esa)], ['0'])).
% 0.20/0.47  thf('31', plain,
% 0.20/0.47      ((((sk_B) != (k1_relat_1 @ sk_C)))
% 0.20/0.47         <= (~ (((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.47  thf('32', plain,
% 0.20/0.47      ((((sk_B) != (sk_B)))
% 0.20/0.47         <= (~ (((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['26', '31'])).
% 0.20/0.47  thf('33', plain, ((((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.47  thf('34', plain,
% 0.20/0.47      (~ ((r1_tarski @ sk_B @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))) | 
% 0.20/0.47       ~ (((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.20/0.47      inference('split', [status(esa)], ['0'])).
% 0.20/0.47  thf('35', plain,
% 0.20/0.47      (~ ((r1_tarski @ sk_B @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.20/0.47      inference('sat_resolution*', [status(thm)], ['33', '34'])).
% 0.20/0.47  thf('36', plain, (~ (r1_tarski @ sk_B @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))),
% 0.20/0.47      inference('simpl_trail', [status(thm)], ['1', '35'])).
% 0.20/0.47  thf('37', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.47       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.47  thf('38', plain,
% 0.20/0.47      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.47         (((k2_relset_1 @ X23 @ X24 @ X22) = (k2_relat_1 @ X22))
% 0.20/0.47          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.20/0.47      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.47  thf('39', plain,
% 0.20/0.47      (((k2_relset_1 @ sk_B @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.47  thf('40', plain, ((r1_tarski @ (k6_relat_1 @ sk_B) @ sk_C)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('41', plain,
% 0.20/0.47      (![X10 : $i, X11 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ X10)
% 0.20/0.47          | (r1_tarski @ (k2_relat_1 @ X11) @ (k2_relat_1 @ X10))
% 0.20/0.47          | ~ (r1_tarski @ X11 @ X10)
% 0.20/0.47          | ~ (v1_relat_1 @ X11))),
% 0.20/0.47      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.20/0.47  thf('42', plain,
% 0.20/0.47      ((~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 0.20/0.47        | (r1_tarski @ (k2_relat_1 @ (k6_relat_1 @ sk_B)) @ (k2_relat_1 @ sk_C))
% 0.20/0.47        | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.47  thf('43', plain, (![X14 : $i]: (v1_relat_1 @ (k6_relat_1 @ X14))),
% 0.20/0.47      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.20/0.47  thf('44', plain, (![X13 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X13)) = (X13))),
% 0.20/0.47      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.47  thf('45', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.47      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.47  thf('46', plain, ((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C))),
% 0.20/0.47      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 0.20/0.47  thf('47', plain, ($false),
% 0.20/0.47      inference('demod', [status(thm)], ['36', '39', '46'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
