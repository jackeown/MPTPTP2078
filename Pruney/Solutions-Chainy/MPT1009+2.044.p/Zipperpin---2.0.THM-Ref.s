%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.u9lbJrnIGN

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:54 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 209 expanded)
%              Number of leaves         :   37 (  78 expanded)
%              Depth                    :   18
%              Number of atoms          :  571 (2288 expanded)
%              Number of equality atoms :   52 ( 129 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ( ( k7_relset_1 @ X37 @ X38 @ X36 @ X39 )
        = ( k9_relat_1 @ X36 @ X39 ) ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X17 @ X18 ) @ ( k2_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
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
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v4_relat_1 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('8',plain,(
    v4_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X21: $i,X22: $i] :
      ( ( X21
        = ( k7_relat_1 @ X21 @ X22 ) )
      | ~ ( v4_relat_1 @ X21 @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('12',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v1_relat_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('13',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('15',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X24 @ X25 ) ) @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('16',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('18',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('19',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X11
        = ( k1_tarski @ X10 ) )
      | ( X11 = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('20',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('21',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k1_relat_1 @ X29 )
       != ( k1_tarski @ X28 ) )
      | ( ( k2_relat_1 @ X29 )
        = ( k1_tarski @ ( k1_funct_1 @ X29 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D ) )
      | ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['22'])).

thf('24',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('26',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('28',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('31',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['29','30'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('32',plain,(
    ! [X23: $i] :
      ( ( ( k1_relat_1 @ X23 )
       != k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('33',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('35',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    sk_D = k1_xboole_0 ),
    inference(simplify,[status(thm)],['35'])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('37',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X26 @ X27 ) @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('38',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('39',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('42',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('43',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v1_relat_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('44',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','44'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('46',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X19 @ X20 ) )
        = ( k9_relat_1 @ X19 @ X20 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k9_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('48',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('49',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['42','43'])).

thf('50',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k9_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    sk_D = k1_xboole_0 ),
    inference(simplify,[status(thm)],['35'])).

thf('52',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['4','36','50','51','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.u9lbJrnIGN
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:48:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.45  % Solved by: fo/fo7.sh
% 0.20/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.45  % done 121 iterations in 0.035s
% 0.20/0.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.45  % SZS output start Refutation
% 0.20/0.45  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.45  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.45  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.45  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.45  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.45  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.45  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.45  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.45  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.45  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.45  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.45  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.45  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.45  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.45  thf(t64_funct_2, conjecture,
% 0.20/0.45    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.45     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.20/0.45         ( m1_subset_1 @
% 0.20/0.45           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.20/0.45       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.45         ( r1_tarski @
% 0.20/0.45           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.20/0.45           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.20/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.45    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.45        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.20/0.45            ( m1_subset_1 @
% 0.20/0.45              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.20/0.45          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.45            ( r1_tarski @
% 0.20/0.45              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.20/0.45              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.20/0.45    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.20/0.45  thf('0', plain,
% 0.20/0.45      (~ (r1_tarski @ 
% 0.20/0.45          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.20/0.45          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('1', plain,
% 0.20/0.45      ((m1_subset_1 @ sk_D @ 
% 0.20/0.45        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf(redefinition_k7_relset_1, axiom,
% 0.20/0.45    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.45       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.20/0.45  thf('2', plain,
% 0.20/0.45      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.20/0.45         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.20/0.45          | ((k7_relset_1 @ X37 @ X38 @ X36 @ X39) = (k9_relat_1 @ X36 @ X39)))),
% 0.20/0.45      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.20/0.45  thf('3', plain,
% 0.20/0.45      (![X0 : $i]:
% 0.20/0.45         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.20/0.45           = (k9_relat_1 @ sk_D @ X0))),
% 0.20/0.45      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.45  thf('4', plain,
% 0.20/0.45      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.20/0.45          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.20/0.45      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.45  thf(t144_relat_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( v1_relat_1 @ B ) =>
% 0.20/0.45       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.20/0.45  thf('5', plain,
% 0.20/0.45      (![X17 : $i, X18 : $i]:
% 0.20/0.45         ((r1_tarski @ (k9_relat_1 @ X17 @ X18) @ (k2_relat_1 @ X17))
% 0.20/0.45          | ~ (v1_relat_1 @ X17))),
% 0.20/0.45      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.20/0.45  thf('6', plain,
% 0.20/0.45      ((m1_subset_1 @ sk_D @ 
% 0.20/0.45        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf(cc2_relset_1, axiom,
% 0.20/0.45    (![A:$i,B:$i,C:$i]:
% 0.20/0.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.45       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.45  thf('7', plain,
% 0.20/0.45      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.20/0.45         ((v4_relat_1 @ X33 @ X34)
% 0.20/0.45          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.20/0.45      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.45  thf('8', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 0.20/0.45      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.45  thf(t209_relat_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.20/0.45       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.20/0.45  thf('9', plain,
% 0.20/0.45      (![X21 : $i, X22 : $i]:
% 0.20/0.45         (((X21) = (k7_relat_1 @ X21 @ X22))
% 0.20/0.45          | ~ (v4_relat_1 @ X21 @ X22)
% 0.20/0.45          | ~ (v1_relat_1 @ X21))),
% 0.20/0.45      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.20/0.45  thf('10', plain,
% 0.20/0.45      ((~ (v1_relat_1 @ sk_D)
% 0.20/0.45        | ((sk_D) = (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A))))),
% 0.20/0.45      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.45  thf('11', plain,
% 0.20/0.45      ((m1_subset_1 @ sk_D @ 
% 0.20/0.45        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf(cc1_relset_1, axiom,
% 0.20/0.45    (![A:$i,B:$i,C:$i]:
% 0.20/0.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.45       ( v1_relat_1 @ C ) ))).
% 0.20/0.45  thf('12', plain,
% 0.20/0.45      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.20/0.45         ((v1_relat_1 @ X30)
% 0.20/0.45          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.20/0.45      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.45  thf('13', plain, ((v1_relat_1 @ sk_D)),
% 0.20/0.45      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.45  thf('14', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A)))),
% 0.20/0.45      inference('demod', [status(thm)], ['10', '13'])).
% 0.20/0.45  thf(t87_relat_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( v1_relat_1 @ B ) =>
% 0.20/0.45       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.20/0.45  thf('15', plain,
% 0.20/0.45      (![X24 : $i, X25 : $i]:
% 0.20/0.45         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X24 @ X25)) @ X25)
% 0.20/0.45          | ~ (v1_relat_1 @ X24))),
% 0.20/0.45      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.20/0.45  thf('16', plain,
% 0.20/0.45      (((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))
% 0.20/0.45        | ~ (v1_relat_1 @ sk_D))),
% 0.20/0.45      inference('sup+', [status(thm)], ['14', '15'])).
% 0.20/0.45  thf('17', plain, ((v1_relat_1 @ sk_D)),
% 0.20/0.45      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.45  thf('18', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 0.20/0.45      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.45  thf(l3_zfmisc_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.20/0.45       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.20/0.45  thf('19', plain,
% 0.20/0.45      (![X10 : $i, X11 : $i]:
% 0.20/0.45         (((X11) = (k1_tarski @ X10))
% 0.20/0.45          | ((X11) = (k1_xboole_0))
% 0.20/0.45          | ~ (r1_tarski @ X11 @ (k1_tarski @ X10)))),
% 0.20/0.45      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.20/0.45  thf('20', plain,
% 0.20/0.45      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.20/0.45        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.45  thf(t14_funct_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.45       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.20/0.45         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.20/0.45  thf('21', plain,
% 0.20/0.45      (![X28 : $i, X29 : $i]:
% 0.20/0.45         (((k1_relat_1 @ X29) != (k1_tarski @ X28))
% 0.20/0.45          | ((k2_relat_1 @ X29) = (k1_tarski @ (k1_funct_1 @ X29 @ X28)))
% 0.20/0.45          | ~ (v1_funct_1 @ X29)
% 0.20/0.45          | ~ (v1_relat_1 @ X29))),
% 0.20/0.45      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.20/0.45  thf('22', plain,
% 0.20/0.45      (![X0 : $i]:
% 0.20/0.45         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 0.20/0.45          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.20/0.45          | ~ (v1_relat_1 @ X0)
% 0.20/0.45          | ~ (v1_funct_1 @ X0)
% 0.20/0.45          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.20/0.45      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.45  thf('23', plain,
% 0.20/0.45      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.20/0.45        | ~ (v1_funct_1 @ sk_D)
% 0.20/0.45        | ~ (v1_relat_1 @ sk_D)
% 0.20/0.45        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.20/0.45      inference('eq_res', [status(thm)], ['22'])).
% 0.20/0.45  thf('24', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('25', plain, ((v1_relat_1 @ sk_D)),
% 0.20/0.45      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.45  thf('26', plain,
% 0.20/0.45      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.20/0.45        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.20/0.45      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.20/0.45  thf('27', plain,
% 0.20/0.45      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.20/0.45          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.20/0.45      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.45  thf('28', plain,
% 0.20/0.45      ((~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))
% 0.20/0.45        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.45  thf('29', plain,
% 0.20/0.45      ((~ (v1_relat_1 @ sk_D) | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['5', '28'])).
% 0.20/0.45  thf('30', plain, ((v1_relat_1 @ sk_D)),
% 0.20/0.45      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.45  thf('31', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.20/0.45      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.45  thf(t64_relat_1, axiom,
% 0.20/0.45    (![A:$i]:
% 0.20/0.45     ( ( v1_relat_1 @ A ) =>
% 0.20/0.45       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.45           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.45         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.45  thf('32', plain,
% 0.20/0.45      (![X23 : $i]:
% 0.20/0.45         (((k1_relat_1 @ X23) != (k1_xboole_0))
% 0.20/0.45          | ((X23) = (k1_xboole_0))
% 0.20/0.45          | ~ (v1_relat_1 @ X23))),
% 0.20/0.45      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.20/0.45  thf('33', plain,
% 0.20/0.45      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.45        | ~ (v1_relat_1 @ sk_D)
% 0.20/0.45        | ((sk_D) = (k1_xboole_0)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.45  thf('34', plain, ((v1_relat_1 @ sk_D)),
% 0.20/0.45      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.45  thf('35', plain,
% 0.20/0.45      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_D) = (k1_xboole_0)))),
% 0.20/0.45      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.45  thf('36', plain, (((sk_D) = (k1_xboole_0))),
% 0.20/0.45      inference('simplify', [status(thm)], ['35'])).
% 0.20/0.45  thf(t88_relat_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 0.20/0.45  thf('37', plain,
% 0.20/0.45      (![X26 : $i, X27 : $i]:
% 0.20/0.45         ((r1_tarski @ (k7_relat_1 @ X26 @ X27) @ X26) | ~ (v1_relat_1 @ X26))),
% 0.20/0.45      inference('cnf', [status(esa)], [t88_relat_1])).
% 0.20/0.45  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.45  thf('38', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.20/0.45      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.45  thf(d10_xboole_0, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.45  thf('39', plain,
% 0.20/0.45      (![X0 : $i, X2 : $i]:
% 0.20/0.45         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.45      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.45  thf('40', plain,
% 0.20/0.45      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.45  thf('41', plain,
% 0.20/0.45      (![X0 : $i]:
% 0.20/0.45         (~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.45          | ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['37', '40'])).
% 0.20/0.45  thf(t4_subset_1, axiom,
% 0.20/0.45    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.45  thf('42', plain,
% 0.20/0.45      (![X13 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 0.20/0.45      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.45  thf('43', plain,
% 0.20/0.45      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.20/0.45         ((v1_relat_1 @ X30)
% 0.20/0.45          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.20/0.45      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.45  thf('44', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.45      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.45  thf('45', plain,
% 0.20/0.45      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.45      inference('demod', [status(thm)], ['41', '44'])).
% 0.20/0.45  thf(t148_relat_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( v1_relat_1 @ B ) =>
% 0.20/0.45       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.20/0.45  thf('46', plain,
% 0.20/0.45      (![X19 : $i, X20 : $i]:
% 0.20/0.45         (((k2_relat_1 @ (k7_relat_1 @ X19 @ X20)) = (k9_relat_1 @ X19 @ X20))
% 0.20/0.45          | ~ (v1_relat_1 @ X19))),
% 0.20/0.45      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.45  thf('47', plain,
% 0.20/0.45      (![X0 : $i]:
% 0.20/0.45         (((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))
% 0.20/0.45          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.20/0.45      inference('sup+', [status(thm)], ['45', '46'])).
% 0.20/0.45  thf(t60_relat_1, axiom,
% 0.20/0.45    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.20/0.45     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.45  thf('48', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.45      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.45  thf('49', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.45      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.45  thf('50', plain,
% 0.20/0.45      (![X0 : $i]: ((k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))),
% 0.20/0.45      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.20/0.45  thf('51', plain, (((sk_D) = (k1_xboole_0))),
% 0.20/0.45      inference('simplify', [status(thm)], ['35'])).
% 0.20/0.45  thf('52', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.20/0.45      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.45  thf('53', plain, ($false),
% 0.20/0.45      inference('demod', [status(thm)], ['4', '36', '50', '51', '52'])).
% 0.20/0.45  
% 0.20/0.45  % SZS output end Refutation
% 0.20/0.45  
% 0.20/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
