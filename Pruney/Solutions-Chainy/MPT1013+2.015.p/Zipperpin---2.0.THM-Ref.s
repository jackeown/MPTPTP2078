%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VCh7j0ReWB

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:45 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 103 expanded)
%              Number of leaves         :   24 (  40 expanded)
%              Depth                    :   10
%              Number of atoms          :  631 (1533 expanded)
%              Number of equality atoms :   33 ( 107 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t73_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
         => ( ( ( ( k2_relset_1 @ A @ A @ B )
                = A )
              & ( ( k2_relset_1 @ A @ A @ C )
                = A ) )
           => ( ( k2_relset_1 @ A @ A @ ( k4_relset_1 @ A @ A @ A @ A @ C @ B ) )
              = A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
           => ( ( ( ( k2_relset_1 @ A @ A @ B )
                  = A )
                & ( ( k2_relset_1 @ A @ A @ C )
                  = A ) )
             => ( ( k2_relset_1 @ A @ A @ ( k4_relset_1 @ A @ A @ A @ A @ C @ B ) )
                = A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t73_funct_2])).

thf('0',plain,(
    ( k2_relset_1 @ sk_A @ sk_A @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( m1_subset_1 @ ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( m1_subset_1 @ ( k4_relset_1 @ X13 @ X14 @ X16 @ X17 @ X12 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relset_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('6',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('7',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) )
    = ( k2_relat_1 @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ( k2_relat_1 @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['0','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('11',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( ( k4_relset_1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27 )
        = ( k5_relat_1 @ X24 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relset_1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
    = ( k5_relat_1 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('15',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X9 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('16',plain,(
    m1_subset_1 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('18',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('19',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['16','19'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('22',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('25',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_C )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference('sup+',[status(thm)],['25','26'])).

thf(t47_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
           => ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('28',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X7 @ X8 ) )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X8 ) @ ( k2_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t47_relat_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('31',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('33',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('34',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','34'])).

thf('36',plain,
    ( ( ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) )
      = ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['22','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('39',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('44',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('46',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['36','41','46'])).

thf('48',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['8','13','47'])).

thf('49',plain,(
    $false ),
    inference(simplify,[status(thm)],['48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VCh7j0ReWB
% 0.13/0.38  % Computer   : n022.cluster.edu
% 0.13/0.38  % Model      : x86_64 x86_64
% 0.13/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.38  % Memory     : 8042.1875MB
% 0.13/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.38  % CPULimit   : 60
% 0.13/0.38  % DateTime   : Tue Dec  1 10:37:26 EST 2020
% 0.13/0.38  % CPUTime    : 
% 0.13/0.38  % Running portfolio for 600 s
% 0.13/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.38  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.38/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.60  % Solved by: fo/fo7.sh
% 0.38/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.60  % done 184 iterations in 0.101s
% 0.38/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.60  % SZS output start Refutation
% 0.38/0.60  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 0.38/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.60  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.38/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.60  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.38/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.60  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.38/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.60  thf(t73_funct_2, conjecture,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.38/0.60       ( ![C:$i]:
% 0.38/0.60         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.38/0.60           ( ( ( ( k2_relset_1 @ A @ A @ B ) = ( A ) ) & 
% 0.38/0.60               ( ( k2_relset_1 @ A @ A @ C ) = ( A ) ) ) =>
% 0.38/0.60             ( ( k2_relset_1 @ A @ A @ ( k4_relset_1 @ A @ A @ A @ A @ C @ B ) ) =
% 0.38/0.60               ( A ) ) ) ) ) ))).
% 0.38/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.60    (~( ![A:$i,B:$i]:
% 0.38/0.60        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.38/0.60          ( ![C:$i]:
% 0.38/0.60            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.38/0.60              ( ( ( ( k2_relset_1 @ A @ A @ B ) = ( A ) ) & 
% 0.38/0.60                  ( ( k2_relset_1 @ A @ A @ C ) = ( A ) ) ) =>
% 0.38/0.60                ( ( k2_relset_1 @
% 0.38/0.60                    A @ A @ ( k4_relset_1 @ A @ A @ A @ A @ C @ B ) ) =
% 0.38/0.60                  ( A ) ) ) ) ) ) )),
% 0.38/0.60    inference('cnf.neg', [status(esa)], [t73_funct_2])).
% 0.38/0.60  thf('0', plain,
% 0.38/0.60      (((k2_relset_1 @ sk_A @ sk_A @ 
% 0.38/0.60         (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)) != (sk_A))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('1', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('2', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(dt_k4_relset_1, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.38/0.60     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.38/0.60         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.38/0.60       ( m1_subset_1 @
% 0.38/0.60         ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.38/0.60         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ))).
% 0.38/0.60  thf('3', plain,
% 0.38/0.60      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.38/0.60         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.38/0.60          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.38/0.60          | (m1_subset_1 @ (k4_relset_1 @ X13 @ X14 @ X16 @ X17 @ X12 @ X15) @ 
% 0.38/0.60             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X17))))),
% 0.38/0.60      inference('cnf', [status(esa)], [dt_k4_relset_1])).
% 0.38/0.60  thf('4', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.60         ((m1_subset_1 @ (k4_relset_1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1) @ 
% 0.38/0.60           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.38/0.60          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['2', '3'])).
% 0.38/0.60  thf('5', plain,
% 0.38/0.60      ((m1_subset_1 @ 
% 0.38/0.60        (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) @ 
% 0.38/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['1', '4'])).
% 0.38/0.60  thf(redefinition_k2_relset_1, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.60       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.38/0.60  thf('6', plain,
% 0.38/0.60      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.38/0.60         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 0.38/0.60          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.38/0.60      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.38/0.60  thf('7', plain,
% 0.38/0.60      (((k2_relset_1 @ sk_A @ sk_A @ 
% 0.38/0.60         (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B))
% 0.38/0.60         = (k2_relat_1 @ 
% 0.38/0.60            (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['5', '6'])).
% 0.38/0.60  thf('8', plain,
% 0.38/0.60      (((k2_relat_1 @ (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B))
% 0.38/0.60         != (sk_A))),
% 0.38/0.60      inference('demod', [status(thm)], ['0', '7'])).
% 0.38/0.60  thf('9', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('10', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(redefinition_k4_relset_1, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.38/0.60     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.38/0.60         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.38/0.60       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.38/0.60  thf('11', plain,
% 0.38/0.60      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.38/0.60         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.38/0.60          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.38/0.60          | ((k4_relset_1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27)
% 0.38/0.60              = (k5_relat_1 @ X24 @ X27)))),
% 0.38/0.60      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 0.38/0.60  thf('12', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.60         (((k4_relset_1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0)
% 0.38/0.60            = (k5_relat_1 @ sk_C @ X0))
% 0.38/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['10', '11'])).
% 0.38/0.60  thf('13', plain,
% 0.38/0.60      (((k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)
% 0.38/0.60         = (k5_relat_1 @ sk_C @ sk_B))),
% 0.38/0.60      inference('sup-', [status(thm)], ['9', '12'])).
% 0.38/0.60  thf('14', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(dt_k1_relset_1, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.60       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.38/0.60  thf('15', plain,
% 0.38/0.60      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.38/0.60         ((m1_subset_1 @ (k1_relset_1 @ X9 @ X10 @ X11) @ (k1_zfmisc_1 @ X9))
% 0.38/0.60          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.38/0.60      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 0.38/0.60  thf('16', plain,
% 0.38/0.60      ((m1_subset_1 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.38/0.60      inference('sup-', [status(thm)], ['14', '15'])).
% 0.38/0.60  thf('17', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(redefinition_k1_relset_1, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.60       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.38/0.60  thf('18', plain,
% 0.38/0.60      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.38/0.60         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 0.38/0.60          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.38/0.60      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.38/0.60  thf('19', plain,
% 0.38/0.60      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 0.38/0.60      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.60  thf('20', plain,
% 0.38/0.60      ((m1_subset_1 @ (k1_relat_1 @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.38/0.60      inference('demod', [status(thm)], ['16', '19'])).
% 0.38/0.60  thf(t3_subset, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.60  thf('21', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         ((r1_tarski @ X0 @ X1) | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.38/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.60  thf('22', plain, ((r1_tarski @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.38/0.60      inference('sup-', [status(thm)], ['20', '21'])).
% 0.38/0.60  thf('23', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('24', plain,
% 0.38/0.60      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.38/0.60         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 0.38/0.60          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.38/0.60      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.38/0.60  thf('25', plain,
% 0.38/0.60      (((k2_relset_1 @ sk_A @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.38/0.60      inference('sup-', [status(thm)], ['23', '24'])).
% 0.38/0.60  thf('26', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_C) = (sk_A))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('27', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.38/0.60      inference('sup+', [status(thm)], ['25', '26'])).
% 0.38/0.60  thf(t47_relat_1, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( v1_relat_1 @ A ) =>
% 0.38/0.60       ( ![B:$i]:
% 0.38/0.60         ( ( v1_relat_1 @ B ) =>
% 0.38/0.60           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 0.38/0.60             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.38/0.60  thf('28', plain,
% 0.38/0.60      (![X7 : $i, X8 : $i]:
% 0.38/0.60         (~ (v1_relat_1 @ X7)
% 0.38/0.60          | ((k2_relat_1 @ (k5_relat_1 @ X7 @ X8)) = (k2_relat_1 @ X8))
% 0.38/0.60          | ~ (r1_tarski @ (k1_relat_1 @ X8) @ (k2_relat_1 @ X7))
% 0.38/0.60          | ~ (v1_relat_1 @ X8))),
% 0.38/0.60      inference('cnf', [status(esa)], [t47_relat_1])).
% 0.38/0.60  thf('29', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 0.38/0.60          | ~ (v1_relat_1 @ X0)
% 0.38/0.60          | ((k2_relat_1 @ (k5_relat_1 @ sk_C @ X0)) = (k2_relat_1 @ X0))
% 0.38/0.60          | ~ (v1_relat_1 @ sk_C))),
% 0.38/0.60      inference('sup-', [status(thm)], ['27', '28'])).
% 0.38/0.60  thf('30', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(cc2_relat_1, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( v1_relat_1 @ A ) =>
% 0.38/0.60       ( ![B:$i]:
% 0.38/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.38/0.60  thf('31', plain,
% 0.38/0.60      (![X3 : $i, X4 : $i]:
% 0.38/0.60         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.38/0.60          | (v1_relat_1 @ X3)
% 0.38/0.60          | ~ (v1_relat_1 @ X4))),
% 0.38/0.60      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.38/0.60  thf('32', plain,
% 0.38/0.60      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_C))),
% 0.38/0.60      inference('sup-', [status(thm)], ['30', '31'])).
% 0.38/0.60  thf(fc6_relat_1, axiom,
% 0.38/0.60    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.38/0.60  thf('33', plain,
% 0.38/0.60      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.38/0.60      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.38/0.60  thf('34', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.60      inference('demod', [status(thm)], ['32', '33'])).
% 0.38/0.60  thf('35', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 0.38/0.60          | ~ (v1_relat_1 @ X0)
% 0.38/0.60          | ((k2_relat_1 @ (k5_relat_1 @ sk_C @ X0)) = (k2_relat_1 @ X0)))),
% 0.38/0.60      inference('demod', [status(thm)], ['29', '34'])).
% 0.38/0.60  thf('36', plain,
% 0.38/0.60      ((((k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)) = (k2_relat_1 @ sk_B))
% 0.38/0.60        | ~ (v1_relat_1 @ sk_B))),
% 0.38/0.60      inference('sup-', [status(thm)], ['22', '35'])).
% 0.38/0.60  thf('37', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('38', plain,
% 0.38/0.60      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.38/0.60         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 0.38/0.60          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.38/0.60      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.38/0.60  thf('39', plain,
% 0.38/0.60      (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (k2_relat_1 @ sk_B))),
% 0.38/0.60      inference('sup-', [status(thm)], ['37', '38'])).
% 0.38/0.60  thf('40', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('41', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.38/0.60      inference('sup+', [status(thm)], ['39', '40'])).
% 0.38/0.60  thf('42', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('43', plain,
% 0.38/0.60      (![X3 : $i, X4 : $i]:
% 0.38/0.60         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.38/0.60          | (v1_relat_1 @ X3)
% 0.38/0.60          | ~ (v1_relat_1 @ X4))),
% 0.38/0.60      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.38/0.60  thf('44', plain,
% 0.38/0.60      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 0.38/0.60      inference('sup-', [status(thm)], ['42', '43'])).
% 0.38/0.60  thf('45', plain,
% 0.38/0.60      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.38/0.60      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.38/0.60  thf('46', plain, ((v1_relat_1 @ sk_B)),
% 0.38/0.60      inference('demod', [status(thm)], ['44', '45'])).
% 0.38/0.60  thf('47', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)) = (sk_A))),
% 0.38/0.60      inference('demod', [status(thm)], ['36', '41', '46'])).
% 0.38/0.60  thf('48', plain, (((sk_A) != (sk_A))),
% 0.38/0.60      inference('demod', [status(thm)], ['8', '13', '47'])).
% 0.38/0.60  thf('49', plain, ($false), inference('simplify', [status(thm)], ['48'])).
% 0.38/0.60  
% 0.38/0.60  % SZS output end Refutation
% 0.38/0.60  
% 0.38/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
