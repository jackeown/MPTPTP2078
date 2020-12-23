%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.o1c4BuLwzP

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 103 expanded)
%              Number of leaves         :   31 (  43 expanded)
%              Depth                    :   10
%              Number of atoms          :  473 ( 996 expanded)
%              Number of equality atoms :   33 (  55 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t50_relset_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
             => ~ ( ( ( k2_relset_1 @ B @ A @ C )
                   != k1_xboole_0 )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ B )
                     => ~ ( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
               => ~ ( ( ( k2_relset_1 @ B @ A @ C )
                     != k1_xboole_0 )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ B )
                       => ~ ( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_relset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X17 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('2',plain,(
    m1_subset_1 @ ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('4',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('5',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['2','5'])).

thf(t10_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ~ ( ( B != k1_xboole_0 )
          & ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ~ ( r2_hidden @ C @ B ) ) ) ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ ( sk_C @ X8 @ X9 ) @ X8 )
      | ( X8 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t10_subset_1])).

thf('8',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C @ ( k1_relat_1 @ sk_C_1 ) @ sk_B ) @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X26: $i] :
      ( ~ ( r2_hidden @ X26 @ ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X26 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('11',plain,(
    ! [X26: $i] :
      ( ~ ( r2_hidden @ X26 @ ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X26 @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ~ ( m1_subset_1 @ ( sk_C @ ( k1_relat_1 @ sk_C_1 ) @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('14',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X8 @ X9 ) @ X9 )
      | ( X8 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t10_subset_1])).

thf('15',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_C @ ( k1_relat_1 @ sk_C_1 ) @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['12','15'])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('17',plain,(
    ! [X13: $i] :
      ( ( ( k7_relat_1 @ X13 @ ( k1_relat_1 @ X13 ) )
        = X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf(fc16_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_xboole_0 @ B ) )
     => ( ( v1_xboole_0 @ ( k7_relat_1 @ A @ B ) )
        & ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) ) )).

thf('18',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_xboole_0 @ X12 )
      | ( v1_xboole_0 @ ( k7_relat_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[fc16_relat_1])).

thf(fc11_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('19',plain,(
    ! [X10: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X10 ) )
      | ~ ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc11_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('20',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['16','24'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('26',plain,(
    ! [X4: $i] :
      ( ( r1_xboole_0 @ X4 @ X4 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('27',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['26'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('29',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( r1_tarski @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('30',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('31',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['29','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('34',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('35',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['25','32','35'])).

thf('37',plain,(
    ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('39',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('40',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['37','40'])).

thf('42',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['36','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.o1c4BuLwzP
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:28:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 78 iterations in 0.038s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.49  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.49  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.49  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.49  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(t50_relset_1, conjecture,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.21/0.49               ( ~( ( ( k2_relset_1 @ B @ A @ C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.49                    ( ![D:$i]:
% 0.21/0.49                      ( ( m1_subset_1 @ D @ B ) =>
% 0.21/0.49                        ( ~( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]:
% 0.21/0.49        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.49          ( ![B:$i]:
% 0.21/0.49            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.49              ( ![C:$i]:
% 0.21/0.49                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.21/0.49                  ( ~( ( ( k2_relset_1 @ B @ A @ C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.49                       ( ![D:$i]:
% 0.21/0.49                         ( ( m1_subset_1 @ D @ B ) =>
% 0.21/0.49                           ( ~( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t50_relset_1])).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(dt_k1_relset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.49       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.49         ((m1_subset_1 @ (k1_relset_1 @ X17 @ X18 @ X19) @ (k1_zfmisc_1 @ X17))
% 0.21/0.49          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      ((m1_subset_1 @ (k1_relset_1 @ sk_B @ sk_A @ sk_C_1) @ 
% 0.21/0.49        (k1_zfmisc_1 @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.49       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.49         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 0.21/0.49          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      ((m1_subset_1 @ (k1_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['2', '5'])).
% 0.21/0.49  thf(t10_subset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.49       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.49            ( ![C:$i]:
% 0.21/0.49              ( ( m1_subset_1 @ C @ A ) => ( ~( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X8 : $i, X9 : $i]:
% 0.21/0.49         ((r2_hidden @ (sk_C @ X8 @ X9) @ X8)
% 0.21/0.49          | ((X8) = (k1_xboole_0))
% 0.21/0.49          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t10_subset_1])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      ((((k1_relat_1 @ sk_C_1) = (k1_xboole_0))
% 0.21/0.49        | (r2_hidden @ (sk_C @ (k1_relat_1 @ sk_C_1) @ sk_B) @ 
% 0.21/0.49           (k1_relat_1 @ sk_C_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X26 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X26 @ (k1_relset_1 @ sk_B @ sk_A @ sk_C_1))
% 0.21/0.49          | ~ (m1_subset_1 @ X26 @ sk_B))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X26 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X26 @ (k1_relat_1 @ sk_C_1))
% 0.21/0.49          | ~ (m1_subset_1 @ X26 @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      ((((k1_relat_1 @ sk_C_1) = (k1_xboole_0))
% 0.21/0.49        | ~ (m1_subset_1 @ (sk_C @ (k1_relat_1 @ sk_C_1) @ sk_B) @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['8', '11'])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      ((m1_subset_1 @ (k1_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['2', '5'])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X8 : $i, X9 : $i]:
% 0.21/0.49         ((m1_subset_1 @ (sk_C @ X8 @ X9) @ X9)
% 0.21/0.49          | ((X8) = (k1_xboole_0))
% 0.21/0.49          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t10_subset_1])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      ((((k1_relat_1 @ sk_C_1) = (k1_xboole_0))
% 0.21/0.49        | (m1_subset_1 @ (sk_C @ (k1_relat_1 @ sk_C_1) @ sk_B) @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.49  thf('16', plain, (((k1_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 0.21/0.49      inference('clc', [status(thm)], ['12', '15'])).
% 0.21/0.49  thf(t98_relat_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ A ) =>
% 0.21/0.49       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (![X13 : $i]:
% 0.21/0.49         (((k7_relat_1 @ X13 @ (k1_relat_1 @ X13)) = (X13))
% 0.21/0.49          | ~ (v1_relat_1 @ X13))),
% 0.21/0.49      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.21/0.49  thf(fc16_relat_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( v1_relat_1 @ A ) & ( v1_xboole_0 @ B ) ) =>
% 0.21/0.49       ( ( v1_xboole_0 @ ( k7_relat_1 @ A @ B ) ) & 
% 0.21/0.49         ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) ))).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      (![X11 : $i, X12 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X11)
% 0.21/0.49          | ~ (v1_xboole_0 @ X12)
% 0.21/0.49          | (v1_xboole_0 @ (k7_relat_1 @ X11 @ X12)))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc16_relat_1])).
% 0.21/0.49  thf(fc11_relat_1, axiom,
% 0.21/0.49    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ))).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (![X10 : $i]:
% 0.21/0.49         ((v1_xboole_0 @ (k2_relat_1 @ X10)) | ~ (v1_xboole_0 @ X10))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc11_relat_1])).
% 0.21/0.49  thf(l13_xboole_0, axiom,
% 0.21/0.49    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.49      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (v1_xboole_0 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X1)
% 0.21/0.49          | ((k2_relat_1 @ (k7_relat_1 @ X1 @ X0)) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['18', '21'])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['17', '22'])).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['23'])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.49        | ((k2_relat_1 @ sk_C_1) = (k1_xboole_0))
% 0.21/0.49        | ~ (v1_relat_1 @ sk_C_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['16', '24'])).
% 0.21/0.49  thf(t66_xboole_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.21/0.49       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      (![X4 : $i]: ((r1_xboole_0 @ X4 @ X4) | ((X4) != (k1_xboole_0)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.21/0.49  thf('27', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.21/0.49      inference('simplify', [status(thm)], ['26'])).
% 0.21/0.49  thf(t69_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.49       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      (![X6 : $i, X7 : $i]:
% 0.21/0.49         (~ (r1_xboole_0 @ X6 @ X7)
% 0.21/0.49          | ~ (r1_tarski @ X6 @ X7)
% 0.21/0.49          | (v1_xboole_0 @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      (((v1_xboole_0 @ k1_xboole_0) | ~ (r1_tarski @ k1_xboole_0 @ k1_xboole_0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.49  thf(d10_xboole_0, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.49  thf('30', plain,
% 0.21/0.49      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 0.21/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.49  thf('31', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.21/0.49      inference('simplify', [status(thm)], ['30'])).
% 0.21/0.49  thf('32', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.49      inference('demod', [status(thm)], ['29', '31'])).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(cc1_relset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.49       ( v1_relat_1 @ C ) ))).
% 0.21/0.49  thf('34', plain,
% 0.21/0.49      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.49         ((v1_relat_1 @ X14)
% 0.21/0.49          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.21/0.49      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.49  thf('35', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.49      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.49  thf('36', plain, (((k2_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 0.21/0.49      inference('demod', [status(thm)], ['25', '32', '35'])).
% 0.21/0.49  thf('37', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_C_1) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('38', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.49       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.49  thf('39', plain,
% 0.21/0.49      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.49         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 0.21/0.49          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.49  thf('40', plain,
% 0.21/0.49      (((k2_relset_1 @ sk_B @ sk_A @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.49  thf('41', plain, (((k2_relat_1 @ sk_C_1) != (k1_xboole_0))),
% 0.21/0.49      inference('demod', [status(thm)], ['37', '40'])).
% 0.21/0.49  thf('42', plain, ($false),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['36', '41'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
