%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.X6efeSVdF2

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:56 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 165 expanded)
%              Number of leaves         :   31 (  63 expanded)
%              Depth                    :   17
%              Number of atoms          :  455 (1929 expanded)
%              Number of equality atoms :   40 ( 109 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t64_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_funct_2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( ( k7_relset_1 @ X25 @ X26 @ X24 @ X27 )
        = ( k9_relat_1 @ X24 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X12 @ X13 ) @ ( k2_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v4_relat_1 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('8',plain,(
    v4_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('9',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v4_relat_1 @ X10 @ X11 )
      | ( r1_tarski @ ( k1_relat_1 @ X10 ) @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('12',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('13',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['10','13'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X8
        = ( k1_tarski @ X7 ) )
      | ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('16',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('17',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k1_relat_1 @ X17 )
       != ( k1_tarski @ X16 ) )
      | ( ( k2_relat_1 @ X17 )
        = ( k1_tarski @ ( k1_funct_1 @ X17 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D ) )
      | ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['18'])).

thf('20',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('22',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('26',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('29',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['27','28'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('30',plain,(
    ! [X15: $i] :
      ( ( ( k1_relat_1 @ X15 )
       != k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('31',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('33',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    sk_D = k1_xboole_0 ),
    inference(simplify,[status(thm)],['33'])).

thf(t150_relat_1,axiom,(
    ! [A: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('35',plain,(
    ! [X14: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X14 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t150_relat_1])).

thf('36',plain,(
    sk_D = k1_xboole_0 ),
    inference(simplify,[status(thm)],['33'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('37',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('38',plain,(
    $false ),
    inference(demod,[status(thm)],['4','34','35','36','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.X6efeSVdF2
% 0.17/0.36  % Computer   : n025.cluster.edu
% 0.17/0.36  % Model      : x86_64 x86_64
% 0.17/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.36  % Memory     : 8042.1875MB
% 0.17/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.37  % CPULimit   : 60
% 0.17/0.37  % DateTime   : Tue Dec  1 11:08:06 EST 2020
% 0.17/0.37  % CPUTime    : 
% 0.17/0.37  % Running portfolio for 600 s
% 0.17/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.37  % Number of cores: 8
% 0.17/0.37  % Python version: Python 3.6.8
% 0.17/0.37  % Running in FO mode
% 0.23/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.50  % Solved by: fo/fo7.sh
% 0.23/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.50  % done 117 iterations in 0.047s
% 0.23/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.50  % SZS output start Refutation
% 0.23/0.50  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.23/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.23/0.50  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.23/0.50  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.23/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.23/0.50  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.23/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.23/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.23/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.50  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.23/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.23/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.23/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.23/0.50  thf(t64_funct_2, conjecture,
% 0.23/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.50     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.23/0.50         ( m1_subset_1 @
% 0.23/0.50           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.23/0.50       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.23/0.50         ( r1_tarski @
% 0.23/0.50           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.23/0.50           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.23/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.50    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.50        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.23/0.50            ( m1_subset_1 @
% 0.23/0.50              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.23/0.50          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.23/0.50            ( r1_tarski @
% 0.23/0.50              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.23/0.50              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.23/0.50    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.23/0.50  thf('0', plain,
% 0.23/0.50      (~ (r1_tarski @ 
% 0.23/0.50          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.23/0.50          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('1', plain,
% 0.23/0.50      ((m1_subset_1 @ sk_D @ 
% 0.23/0.50        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf(redefinition_k7_relset_1, axiom,
% 0.23/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.50       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.23/0.50  thf('2', plain,
% 0.23/0.50      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.23/0.50         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.23/0.50          | ((k7_relset_1 @ X25 @ X26 @ X24 @ X27) = (k9_relat_1 @ X24 @ X27)))),
% 0.23/0.50      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.23/0.50  thf('3', plain,
% 0.23/0.50      (![X0 : $i]:
% 0.23/0.50         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.23/0.50           = (k9_relat_1 @ sk_D @ X0))),
% 0.23/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.23/0.50  thf('4', plain,
% 0.23/0.50      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.23/0.50          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.23/0.50      inference('demod', [status(thm)], ['0', '3'])).
% 0.23/0.50  thf(t144_relat_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( v1_relat_1 @ B ) =>
% 0.23/0.50       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.23/0.50  thf('5', plain,
% 0.23/0.50      (![X12 : $i, X13 : $i]:
% 0.23/0.50         ((r1_tarski @ (k9_relat_1 @ X12 @ X13) @ (k2_relat_1 @ X12))
% 0.23/0.50          | ~ (v1_relat_1 @ X12))),
% 0.23/0.50      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.23/0.50  thf('6', plain,
% 0.23/0.50      ((m1_subset_1 @ sk_D @ 
% 0.23/0.50        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf(cc2_relset_1, axiom,
% 0.23/0.50    (![A:$i,B:$i,C:$i]:
% 0.23/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.50       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.23/0.50  thf('7', plain,
% 0.23/0.50      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.23/0.50         ((v4_relat_1 @ X21 @ X22)
% 0.23/0.50          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.23/0.50      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.23/0.50  thf('8', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 0.23/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.23/0.50  thf(d18_relat_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( v1_relat_1 @ B ) =>
% 0.23/0.50       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.23/0.50  thf('9', plain,
% 0.23/0.50      (![X10 : $i, X11 : $i]:
% 0.23/0.50         (~ (v4_relat_1 @ X10 @ X11)
% 0.23/0.50          | (r1_tarski @ (k1_relat_1 @ X10) @ X11)
% 0.23/0.50          | ~ (v1_relat_1 @ X10))),
% 0.23/0.50      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.23/0.50  thf('10', plain,
% 0.23/0.50      ((~ (v1_relat_1 @ sk_D)
% 0.23/0.50        | (r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A)))),
% 0.23/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.23/0.50  thf('11', plain,
% 0.23/0.50      ((m1_subset_1 @ sk_D @ 
% 0.23/0.50        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf(cc1_relset_1, axiom,
% 0.23/0.50    (![A:$i,B:$i,C:$i]:
% 0.23/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.50       ( v1_relat_1 @ C ) ))).
% 0.23/0.50  thf('12', plain,
% 0.23/0.50      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.23/0.50         ((v1_relat_1 @ X18)
% 0.23/0.50          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.23/0.50      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.23/0.50  thf('13', plain, ((v1_relat_1 @ sk_D)),
% 0.23/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.23/0.50  thf('14', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 0.23/0.50      inference('demod', [status(thm)], ['10', '13'])).
% 0.23/0.50  thf(l3_zfmisc_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.23/0.50       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.23/0.50  thf('15', plain,
% 0.23/0.50      (![X7 : $i, X8 : $i]:
% 0.23/0.50         (((X8) = (k1_tarski @ X7))
% 0.23/0.50          | ((X8) = (k1_xboole_0))
% 0.23/0.50          | ~ (r1_tarski @ X8 @ (k1_tarski @ X7)))),
% 0.23/0.50      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.23/0.50  thf('16', plain,
% 0.23/0.50      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.23/0.50        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 0.23/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.23/0.50  thf(t14_funct_1, axiom,
% 0.23/0.50    (![A:$i,B:$i]:
% 0.23/0.50     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.23/0.50       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.23/0.50         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.23/0.50  thf('17', plain,
% 0.23/0.50      (![X16 : $i, X17 : $i]:
% 0.23/0.50         (((k1_relat_1 @ X17) != (k1_tarski @ X16))
% 0.23/0.50          | ((k2_relat_1 @ X17) = (k1_tarski @ (k1_funct_1 @ X17 @ X16)))
% 0.23/0.50          | ~ (v1_funct_1 @ X17)
% 0.23/0.50          | ~ (v1_relat_1 @ X17))),
% 0.23/0.50      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.23/0.50  thf('18', plain,
% 0.23/0.50      (![X0 : $i]:
% 0.23/0.50         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 0.23/0.50          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.23/0.50          | ~ (v1_relat_1 @ X0)
% 0.23/0.50          | ~ (v1_funct_1 @ X0)
% 0.23/0.50          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.23/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.23/0.50  thf('19', plain,
% 0.23/0.50      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.23/0.50        | ~ (v1_funct_1 @ sk_D)
% 0.23/0.50        | ~ (v1_relat_1 @ sk_D)
% 0.23/0.50        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.23/0.50      inference('eq_res', [status(thm)], ['18'])).
% 0.23/0.50  thf('20', plain, ((v1_funct_1 @ sk_D)),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('21', plain, ((v1_relat_1 @ sk_D)),
% 0.23/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.23/0.50  thf('22', plain,
% 0.23/0.50      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.23/0.50        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.23/0.50      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.23/0.50  thf('23', plain,
% 0.23/0.50      (~ (r1_tarski @ 
% 0.23/0.50          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.23/0.50          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.23/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.50  thf('24', plain,
% 0.23/0.50      ((~ (r1_tarski @ 
% 0.23/0.50           (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.23/0.50           (k2_relat_1 @ sk_D))
% 0.23/0.50        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.23/0.50      inference('sup-', [status(thm)], ['22', '23'])).
% 0.23/0.50  thf('25', plain,
% 0.23/0.50      (![X0 : $i]:
% 0.23/0.50         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.23/0.50           = (k9_relat_1 @ sk_D @ X0))),
% 0.23/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.23/0.50  thf('26', plain,
% 0.23/0.50      ((~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))
% 0.23/0.50        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.23/0.50      inference('demod', [status(thm)], ['24', '25'])).
% 0.23/0.50  thf('27', plain,
% 0.23/0.50      ((~ (v1_relat_1 @ sk_D) | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.23/0.50      inference('sup-', [status(thm)], ['5', '26'])).
% 0.23/0.50  thf('28', plain, ((v1_relat_1 @ sk_D)),
% 0.23/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.23/0.50  thf('29', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.23/0.50      inference('demod', [status(thm)], ['27', '28'])).
% 0.23/0.50  thf(t64_relat_1, axiom,
% 0.23/0.50    (![A:$i]:
% 0.23/0.50     ( ( v1_relat_1 @ A ) =>
% 0.23/0.50       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.23/0.50           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.23/0.50         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.23/0.50  thf('30', plain,
% 0.23/0.50      (![X15 : $i]:
% 0.23/0.50         (((k1_relat_1 @ X15) != (k1_xboole_0))
% 0.23/0.50          | ((X15) = (k1_xboole_0))
% 0.23/0.50          | ~ (v1_relat_1 @ X15))),
% 0.23/0.50      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.23/0.50  thf('31', plain,
% 0.23/0.50      ((((k1_xboole_0) != (k1_xboole_0))
% 0.23/0.50        | ~ (v1_relat_1 @ sk_D)
% 0.23/0.50        | ((sk_D) = (k1_xboole_0)))),
% 0.23/0.50      inference('sup-', [status(thm)], ['29', '30'])).
% 0.23/0.50  thf('32', plain, ((v1_relat_1 @ sk_D)),
% 0.23/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.23/0.50  thf('33', plain,
% 0.23/0.50      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_D) = (k1_xboole_0)))),
% 0.23/0.50      inference('demod', [status(thm)], ['31', '32'])).
% 0.23/0.50  thf('34', plain, (((sk_D) = (k1_xboole_0))),
% 0.23/0.50      inference('simplify', [status(thm)], ['33'])).
% 0.23/0.50  thf(t150_relat_1, axiom,
% 0.23/0.50    (![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.23/0.50  thf('35', plain,
% 0.23/0.50      (![X14 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X14) = (k1_xboole_0))),
% 0.23/0.50      inference('cnf', [status(esa)], [t150_relat_1])).
% 0.23/0.50  thf('36', plain, (((sk_D) = (k1_xboole_0))),
% 0.23/0.50      inference('simplify', [status(thm)], ['33'])).
% 0.23/0.50  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.23/0.50  thf('37', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.23/0.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.23/0.50  thf('38', plain, ($false),
% 0.23/0.50      inference('demod', [status(thm)], ['4', '34', '35', '36', '37'])).
% 0.23/0.50  
% 0.23/0.50  % SZS output end Refutation
% 0.23/0.50  
% 0.23/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
