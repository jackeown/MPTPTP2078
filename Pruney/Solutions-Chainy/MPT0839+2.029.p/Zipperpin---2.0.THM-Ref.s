%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1la9Kk0Euz

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:15 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 182 expanded)
%              Number of leaves         :   25 (  65 expanded)
%              Depth                    :   14
%              Number of atoms          :  453 (2212 expanded)
%              Number of equality atoms :   40 ( 130 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X8 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('3',plain,(
    m1_subset_1 @ ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t10_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ~ ( ( B != k1_xboole_0 )
          & ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ~ ( r2_hidden @ C @ B ) ) ) ) )).

thf('4',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X2 ) @ X1 )
      | ( X1 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t10_subset_1])).

thf('5',plain,
    ( ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
      = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C @ ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 ) @ sk_B ) @ ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('8',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('10',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('11',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C @ ( k1_relat_1 @ sk_C_1 ) @ sk_B ) @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['5','8','9','10'])).

thf('12',plain,(
    ! [X17: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X17 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('14',plain,(
    ! [X17: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X17 @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ~ ( m1_subset_1 @ ( sk_C @ ( k1_relat_1 @ sk_C_1 ) @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    m1_subset_1 @ ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('17',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X1 @ X2 ) @ X2 )
      | ( X1 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t10_subset_1])).

thf('18',plain,
    ( ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_C @ ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 ) @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('20',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('21',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_C @ ( k1_relat_1 @ sk_C_1 ) @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['15','21'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('23',plain,(
    ! [X4: $i] :
      ( ( ( k1_relat_1 @ X4 )
       != k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('24',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('26',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('27',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['0','29'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('31',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('32',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ k1_xboole_0 )
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('33',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(fc11_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('34',plain,(
    ! [X3: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X3 ) )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc11_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('35',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['32','37'])).

thf('39',plain,(
    ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['28'])).

thf('41',plain,(
    ( k2_relset_1 @ sk_B @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['38','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1la9Kk0Euz
% 0.13/0.36  % Computer   : n016.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 20:54:04 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.57  % Solved by: fo/fo7.sh
% 0.22/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.57  % done 101 iterations in 0.100s
% 0.22/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.57  % SZS output start Refutation
% 0.22/0.57  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.22/0.57  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.22/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.57  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.57  thf(t50_relset_1, conjecture,
% 0.22/0.57    (![A:$i]:
% 0.22/0.57     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.57       ( ![B:$i]:
% 0.22/0.57         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.22/0.57           ( ![C:$i]:
% 0.22/0.57             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.22/0.57               ( ~( ( ( k2_relset_1 @ B @ A @ C ) != ( k1_xboole_0 ) ) & 
% 0.22/0.57                    ( ![D:$i]:
% 0.22/0.57                      ( ( m1_subset_1 @ D @ B ) =>
% 0.22/0.57                        ( ~( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.57    (~( ![A:$i]:
% 0.22/0.57        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.57          ( ![B:$i]:
% 0.22/0.57            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.22/0.57              ( ![C:$i]:
% 0.22/0.57                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.22/0.57                  ( ~( ( ( k2_relset_1 @ B @ A @ C ) != ( k1_xboole_0 ) ) & 
% 0.22/0.57                       ( ![D:$i]:
% 0.22/0.57                         ( ( m1_subset_1 @ D @ B ) =>
% 0.22/0.57                           ( ~( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.22/0.57    inference('cnf.neg', [status(esa)], [t50_relset_1])).
% 0.22/0.57  thf('0', plain,
% 0.22/0.57      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('1', plain,
% 0.22/0.57      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(dt_k1_relset_1, axiom,
% 0.22/0.57    (![A:$i,B:$i,C:$i]:
% 0.22/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.57       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.57  thf('2', plain,
% 0.22/0.57      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.57         ((m1_subset_1 @ (k1_relset_1 @ X8 @ X9 @ X10) @ (k1_zfmisc_1 @ X8))
% 0.22/0.57          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.22/0.57      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 0.22/0.57  thf('3', plain,
% 0.22/0.57      ((m1_subset_1 @ (k1_relset_1 @ sk_B @ sk_A @ sk_C_1) @ 
% 0.22/0.57        (k1_zfmisc_1 @ sk_B))),
% 0.22/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.57  thf(t10_subset_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.57       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.57            ( ![C:$i]:
% 0.22/0.57              ( ( m1_subset_1 @ C @ A ) => ( ~( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.22/0.57  thf('4', plain,
% 0.22/0.57      (![X1 : $i, X2 : $i]:
% 0.22/0.57         ((r2_hidden @ (sk_C @ X1 @ X2) @ X1)
% 0.22/0.57          | ((X1) = (k1_xboole_0))
% 0.22/0.57          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.22/0.57      inference('cnf', [status(esa)], [t10_subset_1])).
% 0.22/0.57  thf('5', plain,
% 0.22/0.57      ((((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) = (k1_xboole_0))
% 0.22/0.57        | (r2_hidden @ (sk_C @ (k1_relset_1 @ sk_B @ sk_A @ sk_C_1) @ sk_B) @ 
% 0.22/0.57           (k1_relset_1 @ sk_B @ sk_A @ sk_C_1)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.57  thf('6', plain,
% 0.22/0.57      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(redefinition_k1_relset_1, axiom,
% 0.22/0.57    (![A:$i,B:$i,C:$i]:
% 0.22/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.57       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.22/0.57  thf('7', plain,
% 0.22/0.57      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.57         (((k1_relset_1 @ X12 @ X13 @ X11) = (k1_relat_1 @ X11))
% 0.22/0.57          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.22/0.57      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.22/0.57  thf('8', plain,
% 0.22/0.57      (((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.22/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.57  thf('9', plain,
% 0.22/0.57      (((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.22/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.57  thf('10', plain,
% 0.22/0.57      (((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.22/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.57  thf('11', plain,
% 0.22/0.57      ((((k1_relat_1 @ sk_C_1) = (k1_xboole_0))
% 0.22/0.57        | (r2_hidden @ (sk_C @ (k1_relat_1 @ sk_C_1) @ sk_B) @ 
% 0.22/0.57           (k1_relat_1 @ sk_C_1)))),
% 0.22/0.57      inference('demod', [status(thm)], ['5', '8', '9', '10'])).
% 0.22/0.57  thf('12', plain,
% 0.22/0.57      (![X17 : $i]:
% 0.22/0.57         (~ (r2_hidden @ X17 @ (k1_relset_1 @ sk_B @ sk_A @ sk_C_1))
% 0.22/0.57          | ~ (m1_subset_1 @ X17 @ sk_B))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('13', plain,
% 0.22/0.57      (((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.22/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.57  thf('14', plain,
% 0.22/0.57      (![X17 : $i]:
% 0.22/0.57         (~ (r2_hidden @ X17 @ (k1_relat_1 @ sk_C_1))
% 0.22/0.57          | ~ (m1_subset_1 @ X17 @ sk_B))),
% 0.22/0.57      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.57  thf('15', plain,
% 0.22/0.57      ((((k1_relat_1 @ sk_C_1) = (k1_xboole_0))
% 0.22/0.57        | ~ (m1_subset_1 @ (sk_C @ (k1_relat_1 @ sk_C_1) @ sk_B) @ sk_B))),
% 0.22/0.57      inference('sup-', [status(thm)], ['11', '14'])).
% 0.22/0.57  thf('16', plain,
% 0.22/0.57      ((m1_subset_1 @ (k1_relset_1 @ sk_B @ sk_A @ sk_C_1) @ 
% 0.22/0.57        (k1_zfmisc_1 @ sk_B))),
% 0.22/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.57  thf('17', plain,
% 0.22/0.57      (![X1 : $i, X2 : $i]:
% 0.22/0.57         ((m1_subset_1 @ (sk_C @ X1 @ X2) @ X2)
% 0.22/0.57          | ((X1) = (k1_xboole_0))
% 0.22/0.57          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.22/0.57      inference('cnf', [status(esa)], [t10_subset_1])).
% 0.22/0.57  thf('18', plain,
% 0.22/0.57      ((((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) = (k1_xboole_0))
% 0.22/0.57        | (m1_subset_1 @ 
% 0.22/0.57           (sk_C @ (k1_relset_1 @ sk_B @ sk_A @ sk_C_1) @ sk_B) @ sk_B))),
% 0.22/0.57      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.57  thf('19', plain,
% 0.22/0.57      (((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.22/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.57  thf('20', plain,
% 0.22/0.57      (((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.22/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.57  thf('21', plain,
% 0.22/0.57      ((((k1_relat_1 @ sk_C_1) = (k1_xboole_0))
% 0.22/0.57        | (m1_subset_1 @ (sk_C @ (k1_relat_1 @ sk_C_1) @ sk_B) @ sk_B))),
% 0.22/0.57      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.22/0.57  thf('22', plain, (((k1_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 0.22/0.57      inference('clc', [status(thm)], ['15', '21'])).
% 0.22/0.57  thf(t64_relat_1, axiom,
% 0.22/0.57    (![A:$i]:
% 0.22/0.57     ( ( v1_relat_1 @ A ) =>
% 0.22/0.57       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.22/0.57           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.22/0.57         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.22/0.57  thf('23', plain,
% 0.22/0.57      (![X4 : $i]:
% 0.22/0.57         (((k1_relat_1 @ X4) != (k1_xboole_0))
% 0.22/0.57          | ((X4) = (k1_xboole_0))
% 0.22/0.57          | ~ (v1_relat_1 @ X4))),
% 0.22/0.57      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.22/0.57  thf('24', plain,
% 0.22/0.57      ((((k1_xboole_0) != (k1_xboole_0))
% 0.22/0.57        | ~ (v1_relat_1 @ sk_C_1)
% 0.22/0.57        | ((sk_C_1) = (k1_xboole_0)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.57  thf('25', plain,
% 0.22/0.57      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(cc1_relset_1, axiom,
% 0.22/0.57    (![A:$i,B:$i,C:$i]:
% 0.22/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.57       ( v1_relat_1 @ C ) ))).
% 0.22/0.57  thf('26', plain,
% 0.22/0.57      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.57         ((v1_relat_1 @ X5)
% 0.22/0.57          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.22/0.57      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.22/0.57  thf('27', plain, ((v1_relat_1 @ sk_C_1)),
% 0.22/0.57      inference('sup-', [status(thm)], ['25', '26'])).
% 0.22/0.57  thf('28', plain,
% 0.22/0.57      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C_1) = (k1_xboole_0)))),
% 0.22/0.57      inference('demod', [status(thm)], ['24', '27'])).
% 0.22/0.57  thf('29', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.22/0.57      inference('simplify', [status(thm)], ['28'])).
% 0.22/0.57  thf('30', plain,
% 0.22/0.57      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.57      inference('demod', [status(thm)], ['0', '29'])).
% 0.22/0.57  thf(redefinition_k2_relset_1, axiom,
% 0.22/0.57    (![A:$i,B:$i,C:$i]:
% 0.22/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.57       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.22/0.57  thf('31', plain,
% 0.22/0.57      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.57         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 0.22/0.57          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.22/0.57      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.22/0.57  thf('32', plain,
% 0.22/0.57      (((k2_relset_1 @ sk_B @ sk_A @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 0.22/0.57      inference('sup-', [status(thm)], ['30', '31'])).
% 0.22/0.57  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.22/0.57  thf('33', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.57  thf(fc11_relat_1, axiom,
% 0.22/0.57    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ))).
% 0.22/0.57  thf('34', plain,
% 0.22/0.57      (![X3 : $i]: ((v1_xboole_0 @ (k2_relat_1 @ X3)) | ~ (v1_xboole_0 @ X3))),
% 0.22/0.57      inference('cnf', [status(esa)], [fc11_relat_1])).
% 0.22/0.57  thf(l13_xboole_0, axiom,
% 0.22/0.57    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.57  thf('35', plain,
% 0.22/0.57      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.57      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.22/0.57  thf('36', plain,
% 0.22/0.57      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['34', '35'])).
% 0.22/0.57  thf('37', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.57      inference('sup-', [status(thm)], ['33', '36'])).
% 0.22/0.57  thf('38', plain,
% 0.22/0.57      (((k2_relset_1 @ sk_B @ sk_A @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.57      inference('demod', [status(thm)], ['32', '37'])).
% 0.22/0.57  thf('39', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_C_1) != (k1_xboole_0))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('40', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.22/0.57      inference('simplify', [status(thm)], ['28'])).
% 0.22/0.57  thf('41', plain,
% 0.22/0.57      (((k2_relset_1 @ sk_B @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 0.22/0.57      inference('demod', [status(thm)], ['39', '40'])).
% 0.22/0.57  thf('42', plain, ($false),
% 0.22/0.57      inference('simplify_reflect-', [status(thm)], ['38', '41'])).
% 0.22/0.57  
% 0.22/0.57  % SZS output end Refutation
% 0.22/0.57  
% 0.22/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
