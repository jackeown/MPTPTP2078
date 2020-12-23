%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5GWYInJ8gA

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:56 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 189 expanded)
%              Number of leaves         :   35 (  72 expanded)
%              Depth                    :   17
%              Number of atoms          :  558 (2080 expanded)
%              Number of equality atoms :   49 ( 118 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( ( k7_relset_1 @ X29 @ X30 @ X28 @ X31 )
        = ( k9_relat_1 @ X28 @ X31 ) ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X13 @ X14 ) @ ( k2_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v4_relat_1 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ~ ( v4_relat_1 @ X11 @ X12 )
      | ( r1_tarski @ ( k1_relat_1 @ X11 ) @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
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
    ! [X4: $i,X5: $i] :
      ( ( X5
        = ( k1_tarski @ X4 ) )
      | ( X5 = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ ( k1_tarski @ X4 ) ) ) ),
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
    ! [X20: $i,X21: $i] :
      ( ( ( k1_relat_1 @ X21 )
       != ( k1_tarski @ X20 ) )
      | ( ( k2_relat_1 @ X21 )
        = ( k1_tarski @ ( k1_funct_1 @ X21 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
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
    ! [X19: $i] :
      ( ( ( k1_relat_1 @ X19 )
       != k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
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

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('35',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('36',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v4_relat_1 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('37',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('38',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X17
        = ( k7_relat_1 @ X17 @ X18 ) )
      | ~ ( v4_relat_1 @ X17 @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k7_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('41',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('42',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k7_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['39','42'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('44',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X15 @ X16 ) )
        = ( k9_relat_1 @ X15 @ X16 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k9_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('46',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('47',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['40','41'])).

thf('48',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k9_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    sk_D = k1_xboole_0 ),
    inference(simplify,[status(thm)],['33'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('50',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['4','34','48','49','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5GWYInJ8gA
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:25:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.34/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.34/0.53  % Solved by: fo/fo7.sh
% 0.34/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.53  % done 154 iterations in 0.059s
% 0.34/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.34/0.53  % SZS output start Refutation
% 0.34/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.34/0.53  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.34/0.53  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.34/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.34/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.34/0.53  thf(sk_D_type, type, sk_D: $i).
% 0.34/0.53  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.34/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.34/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.34/0.53  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.34/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.34/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.34/0.53  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.34/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.34/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.34/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.34/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.34/0.53  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.34/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.34/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.34/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.53  thf(t64_funct_2, conjecture,
% 0.34/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.34/0.53     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.34/0.53         ( m1_subset_1 @
% 0.34/0.53           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.34/0.53       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.34/0.53         ( r1_tarski @
% 0.34/0.53           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.34/0.53           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.34/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.53    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.34/0.53        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.34/0.53            ( m1_subset_1 @
% 0.34/0.53              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.34/0.53          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.34/0.53            ( r1_tarski @
% 0.34/0.53              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.34/0.53              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.34/0.53    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.34/0.53  thf('0', plain,
% 0.34/0.53      (~ (r1_tarski @ 
% 0.34/0.53          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.34/0.53          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('1', plain,
% 0.34/0.53      ((m1_subset_1 @ sk_D @ 
% 0.34/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(redefinition_k7_relset_1, axiom,
% 0.34/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.34/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.34/0.53       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.34/0.53  thf('2', plain,
% 0.34/0.53      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.34/0.53         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.34/0.53          | ((k7_relset_1 @ X29 @ X30 @ X28 @ X31) = (k9_relat_1 @ X28 @ X31)))),
% 0.34/0.53      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.34/0.53  thf('3', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.34/0.53           = (k9_relat_1 @ sk_D @ X0))),
% 0.34/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.34/0.53  thf('4', plain,
% 0.34/0.53      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.34/0.53          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.34/0.53      inference('demod', [status(thm)], ['0', '3'])).
% 0.34/0.53  thf(t144_relat_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( v1_relat_1 @ B ) =>
% 0.34/0.53       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.34/0.53  thf('5', plain,
% 0.34/0.53      (![X13 : $i, X14 : $i]:
% 0.34/0.53         ((r1_tarski @ (k9_relat_1 @ X13 @ X14) @ (k2_relat_1 @ X13))
% 0.34/0.53          | ~ (v1_relat_1 @ X13))),
% 0.34/0.53      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.34/0.53  thf('6', plain,
% 0.34/0.53      ((m1_subset_1 @ sk_D @ 
% 0.34/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(cc2_relset_1, axiom,
% 0.34/0.53    (![A:$i,B:$i,C:$i]:
% 0.34/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.34/0.53       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.34/0.53  thf('7', plain,
% 0.34/0.53      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.34/0.53         ((v4_relat_1 @ X25 @ X26)
% 0.34/0.53          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.34/0.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.34/0.53  thf('8', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 0.34/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.34/0.53  thf(d18_relat_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( v1_relat_1 @ B ) =>
% 0.34/0.53       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.34/0.53  thf('9', plain,
% 0.34/0.53      (![X11 : $i, X12 : $i]:
% 0.34/0.53         (~ (v4_relat_1 @ X11 @ X12)
% 0.34/0.53          | (r1_tarski @ (k1_relat_1 @ X11) @ X12)
% 0.34/0.53          | ~ (v1_relat_1 @ X11))),
% 0.34/0.53      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.34/0.53  thf('10', plain,
% 0.34/0.53      ((~ (v1_relat_1 @ sk_D)
% 0.34/0.53        | (r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['8', '9'])).
% 0.34/0.53  thf('11', plain,
% 0.34/0.53      ((m1_subset_1 @ sk_D @ 
% 0.34/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(cc1_relset_1, axiom,
% 0.34/0.53    (![A:$i,B:$i,C:$i]:
% 0.34/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.34/0.53       ( v1_relat_1 @ C ) ))).
% 0.34/0.53  thf('12', plain,
% 0.34/0.53      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.34/0.53         ((v1_relat_1 @ X22)
% 0.34/0.53          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.34/0.53      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.34/0.53  thf('13', plain, ((v1_relat_1 @ sk_D)),
% 0.34/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.34/0.53  thf('14', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 0.34/0.53      inference('demod', [status(thm)], ['10', '13'])).
% 0.34/0.53  thf(l3_zfmisc_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.34/0.53       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.34/0.53  thf('15', plain,
% 0.34/0.53      (![X4 : $i, X5 : $i]:
% 0.34/0.53         (((X5) = (k1_tarski @ X4))
% 0.34/0.53          | ((X5) = (k1_xboole_0))
% 0.34/0.53          | ~ (r1_tarski @ X5 @ (k1_tarski @ X4)))),
% 0.34/0.53      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.34/0.53  thf('16', plain,
% 0.34/0.53      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.34/0.53        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['14', '15'])).
% 0.34/0.53  thf(t14_funct_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.34/0.53       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.34/0.53         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.34/0.53  thf('17', plain,
% 0.34/0.53      (![X20 : $i, X21 : $i]:
% 0.34/0.53         (((k1_relat_1 @ X21) != (k1_tarski @ X20))
% 0.34/0.53          | ((k2_relat_1 @ X21) = (k1_tarski @ (k1_funct_1 @ X21 @ X20)))
% 0.34/0.53          | ~ (v1_funct_1 @ X21)
% 0.34/0.53          | ~ (v1_relat_1 @ X21))),
% 0.34/0.53      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.34/0.53  thf('18', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 0.34/0.53          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.34/0.53          | ~ (v1_relat_1 @ X0)
% 0.34/0.53          | ~ (v1_funct_1 @ X0)
% 0.34/0.53          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.34/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.34/0.53  thf('19', plain,
% 0.34/0.53      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.34/0.53        | ~ (v1_funct_1 @ sk_D)
% 0.34/0.53        | ~ (v1_relat_1 @ sk_D)
% 0.34/0.53        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.34/0.53      inference('eq_res', [status(thm)], ['18'])).
% 0.34/0.53  thf('20', plain, ((v1_funct_1 @ sk_D)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('21', plain, ((v1_relat_1 @ sk_D)),
% 0.34/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.34/0.53  thf('22', plain,
% 0.34/0.53      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.34/0.53        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.34/0.53      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.34/0.53  thf('23', plain,
% 0.34/0.53      (~ (r1_tarski @ 
% 0.34/0.53          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.34/0.53          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('24', plain,
% 0.34/0.53      ((~ (r1_tarski @ 
% 0.34/0.53           (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.34/0.53           (k2_relat_1 @ sk_D))
% 0.34/0.53        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['22', '23'])).
% 0.34/0.53  thf('25', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.34/0.53           = (k9_relat_1 @ sk_D @ X0))),
% 0.34/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.34/0.53  thf('26', plain,
% 0.34/0.53      ((~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))
% 0.34/0.53        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.34/0.53      inference('demod', [status(thm)], ['24', '25'])).
% 0.34/0.53  thf('27', plain,
% 0.34/0.53      ((~ (v1_relat_1 @ sk_D) | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['5', '26'])).
% 0.34/0.53  thf('28', plain, ((v1_relat_1 @ sk_D)),
% 0.34/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.34/0.53  thf('29', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.34/0.53      inference('demod', [status(thm)], ['27', '28'])).
% 0.34/0.53  thf(t64_relat_1, axiom,
% 0.34/0.53    (![A:$i]:
% 0.34/0.53     ( ( v1_relat_1 @ A ) =>
% 0.34/0.53       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.34/0.53           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.34/0.53         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.34/0.53  thf('30', plain,
% 0.34/0.53      (![X19 : $i]:
% 0.34/0.53         (((k1_relat_1 @ X19) != (k1_xboole_0))
% 0.34/0.53          | ((X19) = (k1_xboole_0))
% 0.34/0.53          | ~ (v1_relat_1 @ X19))),
% 0.34/0.53      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.34/0.53  thf('31', plain,
% 0.34/0.53      ((((k1_xboole_0) != (k1_xboole_0))
% 0.34/0.53        | ~ (v1_relat_1 @ sk_D)
% 0.34/0.53        | ((sk_D) = (k1_xboole_0)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['29', '30'])).
% 0.34/0.53  thf('32', plain, ((v1_relat_1 @ sk_D)),
% 0.34/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.34/0.53  thf('33', plain,
% 0.34/0.53      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_D) = (k1_xboole_0)))),
% 0.34/0.53      inference('demod', [status(thm)], ['31', '32'])).
% 0.34/0.53  thf('34', plain, (((sk_D) = (k1_xboole_0))),
% 0.34/0.53      inference('simplify', [status(thm)], ['33'])).
% 0.34/0.53  thf(t4_subset_1, axiom,
% 0.34/0.53    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.34/0.53  thf('35', plain,
% 0.34/0.53      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.34/0.53      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.34/0.53  thf('36', plain,
% 0.34/0.53      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.34/0.53         ((v4_relat_1 @ X25 @ X26)
% 0.34/0.53          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.34/0.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.34/0.53  thf('37', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 0.34/0.53      inference('sup-', [status(thm)], ['35', '36'])).
% 0.34/0.53  thf(t209_relat_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.34/0.53       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.34/0.53  thf('38', plain,
% 0.34/0.53      (![X17 : $i, X18 : $i]:
% 0.34/0.53         (((X17) = (k7_relat_1 @ X17 @ X18))
% 0.34/0.53          | ~ (v4_relat_1 @ X17 @ X18)
% 0.34/0.53          | ~ (v1_relat_1 @ X17))),
% 0.34/0.53      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.34/0.53  thf('39', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         (~ (v1_relat_1 @ k1_xboole_0)
% 0.34/0.53          | ((k1_xboole_0) = (k7_relat_1 @ k1_xboole_0 @ X0)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['37', '38'])).
% 0.34/0.53  thf('40', plain,
% 0.34/0.53      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.34/0.53      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.34/0.53  thf('41', plain,
% 0.34/0.53      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.34/0.53         ((v1_relat_1 @ X22)
% 0.34/0.53          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.34/0.53      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.34/0.53  thf('42', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.34/0.53      inference('sup-', [status(thm)], ['40', '41'])).
% 0.34/0.53  thf('43', plain,
% 0.34/0.53      (![X0 : $i]: ((k1_xboole_0) = (k7_relat_1 @ k1_xboole_0 @ X0))),
% 0.34/0.53      inference('demod', [status(thm)], ['39', '42'])).
% 0.34/0.53  thf(t148_relat_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( v1_relat_1 @ B ) =>
% 0.34/0.53       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.34/0.53  thf('44', plain,
% 0.34/0.53      (![X15 : $i, X16 : $i]:
% 0.34/0.53         (((k2_relat_1 @ (k7_relat_1 @ X15 @ X16)) = (k9_relat_1 @ X15 @ X16))
% 0.34/0.53          | ~ (v1_relat_1 @ X15))),
% 0.34/0.53      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.34/0.53  thf('45', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         (((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))
% 0.34/0.53          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.34/0.53      inference('sup+', [status(thm)], ['43', '44'])).
% 0.34/0.53  thf(t60_relat_1, axiom,
% 0.34/0.53    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.34/0.53     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.34/0.53  thf('46', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.34/0.53      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.34/0.53  thf('47', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.34/0.53      inference('sup-', [status(thm)], ['40', '41'])).
% 0.34/0.53  thf('48', plain,
% 0.34/0.53      (![X0 : $i]: ((k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))),
% 0.34/0.53      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.34/0.53  thf('49', plain, (((sk_D) = (k1_xboole_0))),
% 0.34/0.53      inference('simplify', [status(thm)], ['33'])).
% 0.34/0.53  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.34/0.53  thf('50', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.34/0.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.34/0.53  thf('51', plain, ($false),
% 0.34/0.53      inference('demod', [status(thm)], ['4', '34', '48', '49', '50'])).
% 0.34/0.53  
% 0.34/0.53  % SZS output end Refutation
% 0.34/0.53  
% 0.36/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
