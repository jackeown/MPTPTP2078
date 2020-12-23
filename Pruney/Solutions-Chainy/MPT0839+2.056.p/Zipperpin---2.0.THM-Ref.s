%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ddz11gNI2N

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:18 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 105 expanded)
%              Number of leaves         :   28 (  44 expanded)
%              Depth                    :   14
%              Number of atoms          :  391 ( 950 expanded)
%              Number of equality atoms :   26 (  43 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

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

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('1',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k2_relset_1 @ X19 @ X20 @ X18 )
        = ( k2_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('2',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v4_relat_1 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('5',plain,(
    v4_relat_1 @ sk_C_1 @ sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v4_relat_1 @ X7 @ X8 )
      | ( r1_tarski @ ( k1_relat_1 @ X7 ) @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('7',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('9',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('11',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('12',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['7','12'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X2: $i,X4: $i] :
      ( ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('15',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t10_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ~ ( ( B != k1_xboole_0 )
          & ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ~ ( r2_hidden @ C @ B ) ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t10_subset_1])).

thf('17',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C @ ( k1_relat_1 @ sk_C_1 ) @ sk_B ) @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X21: $i] :
      ( ~ ( r2_hidden @ X21 @ ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X21 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('20',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('21',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X21: $i] :
      ( ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X21 @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ~ ( m1_subset_1 @ ( sk_C @ ( k1_relat_1 @ sk_C_1 ) @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( X0 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t10_subset_1])).

thf('26',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_C @ ( k1_relat_1 @ sk_C_1 ) @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['23','26'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('28',plain,(
    ! [X11: $i] :
      ( ( ( k1_relat_1 @ X11 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X11 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('29',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['10','11'])).

thf('31',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['2','32'])).

thf('34',plain,(
    ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['33','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ddz11gNI2N
% 0.13/0.37  % Computer   : n002.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 17:45:52 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.23/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.51  % Solved by: fo/fo7.sh
% 0.23/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.51  % done 45 iterations in 0.021s
% 0.23/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.51  % SZS output start Refutation
% 0.23/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.23/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.23/0.51  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.23/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.23/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.23/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.51  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.23/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.23/0.51  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.23/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.23/0.51  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.23/0.51  thf(t50_relset_1, conjecture,
% 0.23/0.51    (![A:$i]:
% 0.23/0.51     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.23/0.51       ( ![B:$i]:
% 0.23/0.51         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.23/0.51           ( ![C:$i]:
% 0.23/0.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.23/0.51               ( ~( ( ( k2_relset_1 @ B @ A @ C ) != ( k1_xboole_0 ) ) & 
% 0.23/0.51                    ( ![D:$i]:
% 0.23/0.51                      ( ( m1_subset_1 @ D @ B ) =>
% 0.23/0.51                        ( ~( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.23/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.51    (~( ![A:$i]:
% 0.23/0.51        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.23/0.51          ( ![B:$i]:
% 0.23/0.51            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.23/0.51              ( ![C:$i]:
% 0.23/0.51                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.23/0.51                  ( ~( ( ( k2_relset_1 @ B @ A @ C ) != ( k1_xboole_0 ) ) & 
% 0.23/0.51                       ( ![D:$i]:
% 0.23/0.51                         ( ( m1_subset_1 @ D @ B ) =>
% 0.23/0.51                           ( ~( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.23/0.51    inference('cnf.neg', [status(esa)], [t50_relset_1])).
% 0.23/0.51  thf('0', plain,
% 0.23/0.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf(redefinition_k2_relset_1, axiom,
% 0.23/0.51    (![A:$i,B:$i,C:$i]:
% 0.23/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.51       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.23/0.51  thf('1', plain,
% 0.23/0.51      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.23/0.51         (((k2_relset_1 @ X19 @ X20 @ X18) = (k2_relat_1 @ X18))
% 0.23/0.51          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.23/0.51      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.23/0.51  thf('2', plain,
% 0.23/0.51      (((k2_relset_1 @ sk_B @ sk_A @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.23/0.51      inference('sup-', [status(thm)], ['0', '1'])).
% 0.23/0.51  thf('3', plain,
% 0.23/0.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf(cc2_relset_1, axiom,
% 0.23/0.51    (![A:$i,B:$i,C:$i]:
% 0.23/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.51       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.23/0.51  thf('4', plain,
% 0.23/0.51      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.23/0.51         ((v4_relat_1 @ X12 @ X13)
% 0.23/0.51          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.23/0.51      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.23/0.51  thf('5', plain, ((v4_relat_1 @ sk_C_1 @ sk_B)),
% 0.23/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.23/0.51  thf(d18_relat_1, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( v1_relat_1 @ B ) =>
% 0.23/0.51       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.23/0.51  thf('6', plain,
% 0.23/0.51      (![X7 : $i, X8 : $i]:
% 0.23/0.51         (~ (v4_relat_1 @ X7 @ X8)
% 0.23/0.51          | (r1_tarski @ (k1_relat_1 @ X7) @ X8)
% 0.23/0.51          | ~ (v1_relat_1 @ X7))),
% 0.23/0.51      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.23/0.51  thf('7', plain,
% 0.23/0.51      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_B))),
% 0.23/0.51      inference('sup-', [status(thm)], ['5', '6'])).
% 0.23/0.51  thf('8', plain,
% 0.23/0.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf(cc2_relat_1, axiom,
% 0.23/0.51    (![A:$i]:
% 0.23/0.51     ( ( v1_relat_1 @ A ) =>
% 0.23/0.51       ( ![B:$i]:
% 0.23/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.23/0.51  thf('9', plain,
% 0.23/0.51      (![X5 : $i, X6 : $i]:
% 0.23/0.51         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.23/0.51          | (v1_relat_1 @ X5)
% 0.23/0.51          | ~ (v1_relat_1 @ X6))),
% 0.23/0.51      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.23/0.51  thf('10', plain,
% 0.23/0.51      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_C_1))),
% 0.23/0.51      inference('sup-', [status(thm)], ['8', '9'])).
% 0.23/0.51  thf(fc6_relat_1, axiom,
% 0.23/0.51    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.23/0.51  thf('11', plain,
% 0.23/0.51      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 0.23/0.51      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.23/0.51  thf('12', plain, ((v1_relat_1 @ sk_C_1)),
% 0.23/0.51      inference('demod', [status(thm)], ['10', '11'])).
% 0.23/0.51  thf('13', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_B)),
% 0.23/0.51      inference('demod', [status(thm)], ['7', '12'])).
% 0.23/0.51  thf(t3_subset, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.23/0.51  thf('14', plain,
% 0.23/0.51      (![X2 : $i, X4 : $i]:
% 0.23/0.51         ((m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X4)) | ~ (r1_tarski @ X2 @ X4))),
% 0.23/0.51      inference('cnf', [status(esa)], [t3_subset])).
% 0.23/0.51  thf('15', plain,
% 0.23/0.51      ((m1_subset_1 @ (k1_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ sk_B))),
% 0.23/0.51      inference('sup-', [status(thm)], ['13', '14'])).
% 0.23/0.51  thf(t10_subset_1, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.51       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.23/0.51            ( ![C:$i]:
% 0.23/0.51              ( ( m1_subset_1 @ C @ A ) => ( ~( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.23/0.51  thf('16', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i]:
% 0.23/0.51         ((r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 0.23/0.51          | ((X0) = (k1_xboole_0))
% 0.23/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.23/0.51      inference('cnf', [status(esa)], [t10_subset_1])).
% 0.23/0.51  thf('17', plain,
% 0.23/0.51      ((((k1_relat_1 @ sk_C_1) = (k1_xboole_0))
% 0.23/0.51        | (r2_hidden @ (sk_C @ (k1_relat_1 @ sk_C_1) @ sk_B) @ 
% 0.23/0.51           (k1_relat_1 @ sk_C_1)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['15', '16'])).
% 0.23/0.51  thf('18', plain,
% 0.23/0.51      (![X21 : $i]:
% 0.23/0.51         (~ (r2_hidden @ X21 @ (k1_relset_1 @ sk_B @ sk_A @ sk_C_1))
% 0.23/0.51          | ~ (m1_subset_1 @ X21 @ sk_B))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('19', plain,
% 0.23/0.51      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf(redefinition_k1_relset_1, axiom,
% 0.23/0.51    (![A:$i,B:$i,C:$i]:
% 0.23/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.51       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.23/0.51  thf('20', plain,
% 0.23/0.51      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.23/0.51         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 0.23/0.51          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.23/0.51      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.23/0.51  thf('21', plain,
% 0.23/0.51      (((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.23/0.51      inference('sup-', [status(thm)], ['19', '20'])).
% 0.23/0.51  thf('22', plain,
% 0.23/0.51      (![X21 : $i]:
% 0.23/0.51         (~ (r2_hidden @ X21 @ (k1_relat_1 @ sk_C_1))
% 0.23/0.51          | ~ (m1_subset_1 @ X21 @ sk_B))),
% 0.23/0.51      inference('demod', [status(thm)], ['18', '21'])).
% 0.23/0.51  thf('23', plain,
% 0.23/0.51      ((((k1_relat_1 @ sk_C_1) = (k1_xboole_0))
% 0.23/0.51        | ~ (m1_subset_1 @ (sk_C @ (k1_relat_1 @ sk_C_1) @ sk_B) @ sk_B))),
% 0.23/0.51      inference('sup-', [status(thm)], ['17', '22'])).
% 0.23/0.51  thf('24', plain,
% 0.23/0.51      ((m1_subset_1 @ (k1_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ sk_B))),
% 0.23/0.51      inference('sup-', [status(thm)], ['13', '14'])).
% 0.23/0.51  thf('25', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i]:
% 0.23/0.51         ((m1_subset_1 @ (sk_C @ X0 @ X1) @ X1)
% 0.23/0.51          | ((X0) = (k1_xboole_0))
% 0.23/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.23/0.51      inference('cnf', [status(esa)], [t10_subset_1])).
% 0.23/0.51  thf('26', plain,
% 0.23/0.51      ((((k1_relat_1 @ sk_C_1) = (k1_xboole_0))
% 0.23/0.51        | (m1_subset_1 @ (sk_C @ (k1_relat_1 @ sk_C_1) @ sk_B) @ sk_B))),
% 0.23/0.51      inference('sup-', [status(thm)], ['24', '25'])).
% 0.23/0.51  thf('27', plain, (((k1_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 0.23/0.51      inference('clc', [status(thm)], ['23', '26'])).
% 0.23/0.51  thf(t65_relat_1, axiom,
% 0.23/0.51    (![A:$i]:
% 0.23/0.51     ( ( v1_relat_1 @ A ) =>
% 0.23/0.51       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.23/0.51         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.23/0.51  thf('28', plain,
% 0.23/0.51      (![X11 : $i]:
% 0.23/0.51         (((k1_relat_1 @ X11) != (k1_xboole_0))
% 0.23/0.51          | ((k2_relat_1 @ X11) = (k1_xboole_0))
% 0.23/0.51          | ~ (v1_relat_1 @ X11))),
% 0.23/0.51      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.23/0.51  thf('29', plain,
% 0.23/0.51      ((((k1_xboole_0) != (k1_xboole_0))
% 0.23/0.51        | ~ (v1_relat_1 @ sk_C_1)
% 0.23/0.51        | ((k2_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['27', '28'])).
% 0.23/0.51  thf('30', plain, ((v1_relat_1 @ sk_C_1)),
% 0.23/0.51      inference('demod', [status(thm)], ['10', '11'])).
% 0.23/0.51  thf('31', plain,
% 0.23/0.51      ((((k1_xboole_0) != (k1_xboole_0))
% 0.23/0.51        | ((k2_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 0.23/0.51      inference('demod', [status(thm)], ['29', '30'])).
% 0.23/0.51  thf('32', plain, (((k2_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 0.23/0.51      inference('simplify', [status(thm)], ['31'])).
% 0.23/0.51  thf('33', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_C_1) = (k1_xboole_0))),
% 0.23/0.51      inference('demod', [status(thm)], ['2', '32'])).
% 0.23/0.51  thf('34', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_C_1) != (k1_xboole_0))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('35', plain, ($false),
% 0.23/0.51      inference('simplify_reflect-', [status(thm)], ['33', '34'])).
% 0.23/0.51  
% 0.23/0.51  % SZS output end Refutation
% 0.23/0.51  
% 0.23/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
