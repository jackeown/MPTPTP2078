%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tItyOuePTM

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:19 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 106 expanded)
%              Number of leaves         :   31 (  45 expanded)
%              Depth                    :   15
%              Number of atoms          :  459 ( 969 expanded)
%              Number of equality atoms :   36 (  55 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('1',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X26 @ X24 )
        = ( k2_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('2',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('3',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('4',plain,(
    ! [X27: $i] :
      ( ~ ( r2_hidden @ X27 @ ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C ) )
      | ~ ( m1_subset_1 @ X27 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ~ ( m1_subset_1 @ ( sk_B @ ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('7',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('8',plain,
    ( ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('10',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ~ ( m1_subset_1 @ ( sk_B @ ( k1_relat_1 @ sk_C ) ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['5','8','9'])).

thf('11',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v4_relat_1 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('14',plain,(
    v4_relat_1 @ sk_C @ sk_B_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X13
        = ( k7_relat_1 @ X13 @ X14 ) )
      | ~ ( v4_relat_1 @ X13 @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('18',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('20',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('21',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_B_1 ) ),
    inference(demod,[status(thm)],['16','21'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('23',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X16 @ X17 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X16 ) @ X17 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('24',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('25',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C ) )
      | ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['22','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['19','20'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C ) )
      | ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ ( k1_relat_1 @ sk_C ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['11','29'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('31',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ X7 @ X8 )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('32',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_B @ ( k1_relat_1 @ sk_C ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['10','32'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('34',plain,(
    ! [X15: $i] :
      ( ( ( k1_relat_1 @ X15 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X15 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('35',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['19','20'])).

thf('37',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_C )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['2','38'])).

thf('40',plain,(
    ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_C )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['39','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tItyOuePTM
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:14:57 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.35/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.53  % Solved by: fo/fo7.sh
% 0.35/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.53  % done 97 iterations in 0.084s
% 0.35/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.53  % SZS output start Refutation
% 0.35/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.35/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.35/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.35/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.35/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.53  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.35/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.35/0.53  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.35/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.35/0.53  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.35/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.35/0.53  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.35/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.35/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.35/0.53  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.35/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.53  thf(t50_relset_1, conjecture,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.35/0.53       ( ![B:$i]:
% 0.35/0.53         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.35/0.53           ( ![C:$i]:
% 0.35/0.53             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.35/0.53               ( ~( ( ( k2_relset_1 @ B @ A @ C ) != ( k1_xboole_0 ) ) & 
% 0.35/0.53                    ( ![D:$i]:
% 0.35/0.53                      ( ( m1_subset_1 @ D @ B ) =>
% 0.35/0.53                        ( ~( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.35/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.53    (~( ![A:$i]:
% 0.35/0.53        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.35/0.53          ( ![B:$i]:
% 0.35/0.53            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.35/0.53              ( ![C:$i]:
% 0.35/0.53                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.35/0.53                  ( ~( ( ( k2_relset_1 @ B @ A @ C ) != ( k1_xboole_0 ) ) & 
% 0.35/0.53                       ( ![D:$i]:
% 0.35/0.53                         ( ( m1_subset_1 @ D @ B ) =>
% 0.35/0.53                           ( ~( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.35/0.53    inference('cnf.neg', [status(esa)], [t50_relset_1])).
% 0.35/0.53  thf('0', plain,
% 0.35/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(redefinition_k2_relset_1, axiom,
% 0.35/0.53    (![A:$i,B:$i,C:$i]:
% 0.35/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.53       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.35/0.53  thf('1', plain,
% 0.35/0.53      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.35/0.53         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 0.35/0.53          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.35/0.53      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.35/0.53  thf('2', plain,
% 0.35/0.53      (((k2_relset_1 @ sk_B_1 @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.35/0.53      inference('sup-', [status(thm)], ['0', '1'])).
% 0.35/0.53  thf(t7_xboole_0, axiom,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.35/0.53          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.35/0.53  thf('3', plain,
% 0.35/0.53      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.35/0.53      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.35/0.53  thf('4', plain,
% 0.35/0.53      (![X27 : $i]:
% 0.35/0.53         (~ (r2_hidden @ X27 @ (k1_relset_1 @ sk_B_1 @ sk_A @ sk_C))
% 0.35/0.53          | ~ (m1_subset_1 @ X27 @ sk_B_1))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('5', plain,
% 0.35/0.53      ((((k1_relset_1 @ sk_B_1 @ sk_A @ sk_C) = (k1_xboole_0))
% 0.35/0.53        | ~ (m1_subset_1 @ (sk_B @ (k1_relset_1 @ sk_B_1 @ sk_A @ sk_C)) @ 
% 0.35/0.53             sk_B_1))),
% 0.35/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.35/0.53  thf('6', plain,
% 0.35/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(redefinition_k1_relset_1, axiom,
% 0.35/0.53    (![A:$i,B:$i,C:$i]:
% 0.35/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.53       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.35/0.53  thf('7', plain,
% 0.35/0.53      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.35/0.53         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 0.35/0.53          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.35/0.53      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.35/0.53  thf('8', plain,
% 0.35/0.53      (((k1_relset_1 @ sk_B_1 @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.35/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.35/0.53  thf('9', plain,
% 0.35/0.53      (((k1_relset_1 @ sk_B_1 @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.35/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.35/0.53  thf('10', plain,
% 0.35/0.53      ((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 0.35/0.53        | ~ (m1_subset_1 @ (sk_B @ (k1_relat_1 @ sk_C)) @ sk_B_1))),
% 0.35/0.53      inference('demod', [status(thm)], ['5', '8', '9'])).
% 0.35/0.53  thf('11', plain,
% 0.35/0.53      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.35/0.53      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.35/0.53  thf('12', plain,
% 0.35/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(cc2_relset_1, axiom,
% 0.35/0.53    (![A:$i,B:$i,C:$i]:
% 0.35/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.53       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.35/0.53  thf('13', plain,
% 0.35/0.53      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.35/0.53         ((v4_relat_1 @ X18 @ X19)
% 0.35/0.53          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.35/0.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.35/0.53  thf('14', plain, ((v4_relat_1 @ sk_C @ sk_B_1)),
% 0.35/0.53      inference('sup-', [status(thm)], ['12', '13'])).
% 0.35/0.53  thf(t209_relat_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.35/0.53       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.35/0.53  thf('15', plain,
% 0.35/0.53      (![X13 : $i, X14 : $i]:
% 0.35/0.53         (((X13) = (k7_relat_1 @ X13 @ X14))
% 0.35/0.53          | ~ (v4_relat_1 @ X13 @ X14)
% 0.35/0.53          | ~ (v1_relat_1 @ X13))),
% 0.35/0.53      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.35/0.53  thf('16', plain,
% 0.35/0.53      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_B_1)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['14', '15'])).
% 0.35/0.53  thf('17', plain,
% 0.35/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(cc2_relat_1, axiom,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( v1_relat_1 @ A ) =>
% 0.35/0.53       ( ![B:$i]:
% 0.35/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.35/0.53  thf('18', plain,
% 0.35/0.53      (![X9 : $i, X10 : $i]:
% 0.35/0.53         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.35/0.53          | (v1_relat_1 @ X9)
% 0.35/0.53          | ~ (v1_relat_1 @ X10))),
% 0.35/0.53      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.35/0.53  thf('19', plain,
% 0.35/0.53      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)) | (v1_relat_1 @ sk_C))),
% 0.35/0.53      inference('sup-', [status(thm)], ['17', '18'])).
% 0.35/0.53  thf(fc6_relat_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.35/0.53  thf('20', plain,
% 0.35/0.53      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 0.35/0.53      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.35/0.53  thf('21', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.53      inference('demod', [status(thm)], ['19', '20'])).
% 0.35/0.53  thf('22', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_B_1))),
% 0.35/0.53      inference('demod', [status(thm)], ['16', '21'])).
% 0.35/0.53  thf(t90_relat_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( v1_relat_1 @ B ) =>
% 0.35/0.53       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.35/0.53         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.35/0.53  thf('23', plain,
% 0.35/0.53      (![X16 : $i, X17 : $i]:
% 0.35/0.53         (((k1_relat_1 @ (k7_relat_1 @ X16 @ X17))
% 0.35/0.53            = (k3_xboole_0 @ (k1_relat_1 @ X16) @ X17))
% 0.35/0.53          | ~ (v1_relat_1 @ X16))),
% 0.35/0.53      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.35/0.53  thf(d4_xboole_0, axiom,
% 0.35/0.53    (![A:$i,B:$i,C:$i]:
% 0.35/0.53     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.35/0.53       ( ![D:$i]:
% 0.35/0.53         ( ( r2_hidden @ D @ C ) <=>
% 0.35/0.53           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.35/0.53  thf('24', plain,
% 0.35/0.53      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.35/0.53         (~ (r2_hidden @ X4 @ X3)
% 0.35/0.53          | (r2_hidden @ X4 @ X2)
% 0.35/0.53          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.35/0.53      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.35/0.53  thf('25', plain,
% 0.35/0.53      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.35/0.53         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.35/0.53      inference('simplify', [status(thm)], ['24'])).
% 0.35/0.53  thf('26', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.53         (~ (r2_hidden @ X2 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.35/0.53          | ~ (v1_relat_1 @ X1)
% 0.35/0.53          | (r2_hidden @ X2 @ X0))),
% 0.35/0.53      inference('sup-', [status(thm)], ['23', '25'])).
% 0.35/0.53  thf('27', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C))
% 0.35/0.53          | (r2_hidden @ X0 @ sk_B_1)
% 0.35/0.53          | ~ (v1_relat_1 @ sk_C))),
% 0.35/0.53      inference('sup-', [status(thm)], ['22', '26'])).
% 0.35/0.53  thf('28', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.53      inference('demod', [status(thm)], ['19', '20'])).
% 0.35/0.53  thf('29', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C)) | (r2_hidden @ X0 @ sk_B_1))),
% 0.35/0.53      inference('demod', [status(thm)], ['27', '28'])).
% 0.35/0.53  thf('30', plain,
% 0.35/0.53      ((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 0.35/0.53        | (r2_hidden @ (sk_B @ (k1_relat_1 @ sk_C)) @ sk_B_1))),
% 0.35/0.53      inference('sup-', [status(thm)], ['11', '29'])).
% 0.35/0.53  thf(t1_subset, axiom,
% 0.35/0.53    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.35/0.53  thf('31', plain,
% 0.35/0.53      (![X7 : $i, X8 : $i]: ((m1_subset_1 @ X7 @ X8) | ~ (r2_hidden @ X7 @ X8))),
% 0.35/0.53      inference('cnf', [status(esa)], [t1_subset])).
% 0.35/0.53  thf('32', plain,
% 0.35/0.53      ((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 0.35/0.53        | (m1_subset_1 @ (sk_B @ (k1_relat_1 @ sk_C)) @ sk_B_1))),
% 0.35/0.53      inference('sup-', [status(thm)], ['30', '31'])).
% 0.35/0.53  thf('33', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.35/0.53      inference('clc', [status(thm)], ['10', '32'])).
% 0.35/0.53  thf(t65_relat_1, axiom,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( v1_relat_1 @ A ) =>
% 0.35/0.53       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.35/0.53         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.35/0.53  thf('34', plain,
% 0.35/0.53      (![X15 : $i]:
% 0.35/0.53         (((k1_relat_1 @ X15) != (k1_xboole_0))
% 0.35/0.53          | ((k2_relat_1 @ X15) = (k1_xboole_0))
% 0.35/0.53          | ~ (v1_relat_1 @ X15))),
% 0.35/0.53      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.35/0.53  thf('35', plain,
% 0.35/0.53      ((((k1_xboole_0) != (k1_xboole_0))
% 0.35/0.53        | ~ (v1_relat_1 @ sk_C)
% 0.35/0.53        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['33', '34'])).
% 0.35/0.53  thf('36', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.53      inference('demod', [status(thm)], ['19', '20'])).
% 0.35/0.53  thf('37', plain,
% 0.35/0.53      ((((k1_xboole_0) != (k1_xboole_0))
% 0.35/0.53        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.35/0.53      inference('demod', [status(thm)], ['35', '36'])).
% 0.35/0.53  thf('38', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.35/0.53      inference('simplify', [status(thm)], ['37'])).
% 0.35/0.53  thf('39', plain, (((k2_relset_1 @ sk_B_1 @ sk_A @ sk_C) = (k1_xboole_0))),
% 0.35/0.53      inference('demod', [status(thm)], ['2', '38'])).
% 0.35/0.53  thf('40', plain, (((k2_relset_1 @ sk_B_1 @ sk_A @ sk_C) != (k1_xboole_0))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('41', plain, ($false),
% 0.35/0.53      inference('simplify_reflect-', [status(thm)], ['39', '40'])).
% 0.35/0.53  
% 0.35/0.53  % SZS output end Refutation
% 0.35/0.53  
% 0.35/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
