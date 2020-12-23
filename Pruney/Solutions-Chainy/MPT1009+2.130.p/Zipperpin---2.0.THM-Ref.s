%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.exULLigORz

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:07 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 205 expanded)
%              Number of leaves         :   32 (  76 expanded)
%              Depth                    :   19
%              Number of atoms          :  525 (2209 expanded)
%              Number of equality atoms :   42 ( 112 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

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
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( ( k7_relset_1 @ X28 @ X29 @ X27 @ X30 )
        = ( k9_relat_1 @ X27 @ X30 ) ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X19 @ X20 ) @ ( k2_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v4_relat_1 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ~ ( v4_relat_1 @ X15 @ X16 )
      | ( r1_tarski @ ( k1_relat_1 @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('12',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X17: $i,X18: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('15',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['10','15'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('17',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X11
        = ( k1_tarski @ X10 ) )
      | ( X11 = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('18',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('19',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k1_relat_1 @ X23 )
       != ( k1_tarski @ X22 ) )
      | ( ( k2_relat_1 @ X23 )
        = ( k1_tarski @ ( k1_funct_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D ) )
      | ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['20'])).

thf('22',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('24',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('28',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('31',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['29','30'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('32',plain,(
    ! [X21: $i] :
      ( ( ( k1_relat_1 @ X21 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X21 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('33',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('35',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k2_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X19 @ X20 ) @ ( k2_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('38',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k9_relat_1 @ X0 @ X1 ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k9_relat_1 @ sk_D @ X0 ) )
      | ( ( k2_relat_1 @ sk_D )
        = ( k9_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('41',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('42',plain,
    ( ( k2_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['35'])).

thf('43',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('44',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['40','41','42','43'])).

thf('45',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['4','44','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.exULLigORz
% 0.15/0.37  % Computer   : n009.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 10:27:11 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.24/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.52  % Solved by: fo/fo7.sh
% 0.24/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.52  % done 83 iterations in 0.041s
% 0.24/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.52  % SZS output start Refutation
% 0.24/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.24/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.24/0.52  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.24/0.52  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.24/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.24/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.24/0.52  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.24/0.52  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.24/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.24/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.24/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.52  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.24/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.24/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.24/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.24/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.52  thf(t64_funct_2, conjecture,
% 0.24/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.24/0.52     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.24/0.52         ( m1_subset_1 @
% 0.24/0.52           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.24/0.52       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.24/0.52         ( r1_tarski @
% 0.24/0.52           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.24/0.52           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.24/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.52    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.24/0.52        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.24/0.52            ( m1_subset_1 @
% 0.24/0.52              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.24/0.52          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.24/0.52            ( r1_tarski @
% 0.24/0.52              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.24/0.52              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.24/0.52    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.24/0.52  thf('0', plain,
% 0.24/0.52      (~ (r1_tarski @ 
% 0.24/0.52          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.24/0.52          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('1', plain,
% 0.24/0.52      ((m1_subset_1 @ sk_D @ 
% 0.24/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf(redefinition_k7_relset_1, axiom,
% 0.24/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.24/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.24/0.52       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.24/0.52  thf('2', plain,
% 0.24/0.52      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.24/0.52         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.24/0.52          | ((k7_relset_1 @ X28 @ X29 @ X27 @ X30) = (k9_relat_1 @ X27 @ X30)))),
% 0.24/0.52      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.24/0.52  thf('3', plain,
% 0.24/0.52      (![X0 : $i]:
% 0.24/0.52         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.24/0.52           = (k9_relat_1 @ sk_D @ X0))),
% 0.24/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.24/0.52  thf('4', plain,
% 0.24/0.52      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.24/0.52          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.24/0.52      inference('demod', [status(thm)], ['0', '3'])).
% 0.24/0.52  thf(t144_relat_1, axiom,
% 0.24/0.52    (![A:$i,B:$i]:
% 0.24/0.52     ( ( v1_relat_1 @ B ) =>
% 0.24/0.52       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.24/0.52  thf('5', plain,
% 0.24/0.52      (![X19 : $i, X20 : $i]:
% 0.24/0.52         ((r1_tarski @ (k9_relat_1 @ X19 @ X20) @ (k2_relat_1 @ X19))
% 0.24/0.52          | ~ (v1_relat_1 @ X19))),
% 0.24/0.52      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.24/0.52  thf('6', plain,
% 0.24/0.52      ((m1_subset_1 @ sk_D @ 
% 0.24/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf(cc2_relset_1, axiom,
% 0.24/0.52    (![A:$i,B:$i,C:$i]:
% 0.24/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.24/0.52       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.24/0.52  thf('7', plain,
% 0.24/0.52      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.24/0.52         ((v4_relat_1 @ X24 @ X25)
% 0.24/0.52          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.24/0.52      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.24/0.52  thf('8', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 0.24/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.24/0.52  thf(d18_relat_1, axiom,
% 0.24/0.52    (![A:$i,B:$i]:
% 0.24/0.52     ( ( v1_relat_1 @ B ) =>
% 0.24/0.52       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.24/0.52  thf('9', plain,
% 0.24/0.52      (![X15 : $i, X16 : $i]:
% 0.24/0.52         (~ (v4_relat_1 @ X15 @ X16)
% 0.24/0.52          | (r1_tarski @ (k1_relat_1 @ X15) @ X16)
% 0.24/0.52          | ~ (v1_relat_1 @ X15))),
% 0.24/0.52      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.24/0.52  thf('10', plain,
% 0.24/0.52      ((~ (v1_relat_1 @ sk_D)
% 0.24/0.52        | (r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['8', '9'])).
% 0.24/0.52  thf('11', plain,
% 0.24/0.52      ((m1_subset_1 @ sk_D @ 
% 0.24/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf(cc2_relat_1, axiom,
% 0.24/0.52    (![A:$i]:
% 0.24/0.52     ( ( v1_relat_1 @ A ) =>
% 0.24/0.52       ( ![B:$i]:
% 0.24/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.24/0.52  thf('12', plain,
% 0.24/0.52      (![X13 : $i, X14 : $i]:
% 0.24/0.52         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.24/0.52          | (v1_relat_1 @ X13)
% 0.24/0.52          | ~ (v1_relat_1 @ X14))),
% 0.24/0.52      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.24/0.52  thf('13', plain,
% 0.24/0.52      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.24/0.52        | (v1_relat_1 @ sk_D))),
% 0.24/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.24/0.52  thf(fc6_relat_1, axiom,
% 0.24/0.52    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.24/0.52  thf('14', plain,
% 0.24/0.52      (![X17 : $i, X18 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X17 @ X18))),
% 0.24/0.52      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.24/0.52  thf('15', plain, ((v1_relat_1 @ sk_D)),
% 0.24/0.52      inference('demod', [status(thm)], ['13', '14'])).
% 0.24/0.52  thf('16', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 0.24/0.52      inference('demod', [status(thm)], ['10', '15'])).
% 0.24/0.52  thf(l3_zfmisc_1, axiom,
% 0.24/0.52    (![A:$i,B:$i]:
% 0.24/0.52     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.24/0.52       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.24/0.52  thf('17', plain,
% 0.24/0.52      (![X10 : $i, X11 : $i]:
% 0.24/0.52         (((X11) = (k1_tarski @ X10))
% 0.24/0.52          | ((X11) = (k1_xboole_0))
% 0.24/0.52          | ~ (r1_tarski @ X11 @ (k1_tarski @ X10)))),
% 0.24/0.52      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.24/0.52  thf('18', plain,
% 0.24/0.52      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.24/0.52        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['16', '17'])).
% 0.24/0.52  thf(t14_funct_1, axiom,
% 0.24/0.52    (![A:$i,B:$i]:
% 0.24/0.52     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.24/0.52       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.24/0.52         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.24/0.52  thf('19', plain,
% 0.24/0.52      (![X22 : $i, X23 : $i]:
% 0.24/0.52         (((k1_relat_1 @ X23) != (k1_tarski @ X22))
% 0.24/0.52          | ((k2_relat_1 @ X23) = (k1_tarski @ (k1_funct_1 @ X23 @ X22)))
% 0.24/0.52          | ~ (v1_funct_1 @ X23)
% 0.24/0.52          | ~ (v1_relat_1 @ X23))),
% 0.24/0.52      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.24/0.52  thf('20', plain,
% 0.24/0.52      (![X0 : $i]:
% 0.24/0.52         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 0.24/0.52          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.24/0.52          | ~ (v1_relat_1 @ X0)
% 0.24/0.52          | ~ (v1_funct_1 @ X0)
% 0.24/0.52          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.24/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.24/0.52  thf('21', plain,
% 0.24/0.52      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.24/0.52        | ~ (v1_funct_1 @ sk_D)
% 0.24/0.52        | ~ (v1_relat_1 @ sk_D)
% 0.24/0.52        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.24/0.52      inference('eq_res', [status(thm)], ['20'])).
% 0.24/0.52  thf('22', plain, ((v1_funct_1 @ sk_D)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('23', plain, ((v1_relat_1 @ sk_D)),
% 0.24/0.52      inference('demod', [status(thm)], ['13', '14'])).
% 0.24/0.52  thf('24', plain,
% 0.24/0.52      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.24/0.52        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.24/0.52      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.24/0.52  thf('25', plain,
% 0.24/0.52      (~ (r1_tarski @ 
% 0.24/0.52          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.24/0.52          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('26', plain,
% 0.24/0.52      ((~ (r1_tarski @ 
% 0.24/0.52           (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.24/0.52           (k2_relat_1 @ sk_D))
% 0.24/0.52        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['24', '25'])).
% 0.24/0.52  thf('27', plain,
% 0.24/0.52      (![X0 : $i]:
% 0.24/0.52         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.24/0.52           = (k9_relat_1 @ sk_D @ X0))),
% 0.24/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.24/0.52  thf('28', plain,
% 0.24/0.52      ((~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))
% 0.24/0.52        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.24/0.52      inference('demod', [status(thm)], ['26', '27'])).
% 0.24/0.52  thf('29', plain,
% 0.24/0.52      ((~ (v1_relat_1 @ sk_D) | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['5', '28'])).
% 0.24/0.52  thf('30', plain, ((v1_relat_1 @ sk_D)),
% 0.24/0.52      inference('demod', [status(thm)], ['13', '14'])).
% 0.24/0.52  thf('31', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.24/0.52      inference('demod', [status(thm)], ['29', '30'])).
% 0.24/0.52  thf(t65_relat_1, axiom,
% 0.24/0.52    (![A:$i]:
% 0.24/0.52     ( ( v1_relat_1 @ A ) =>
% 0.24/0.52       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.24/0.52         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.24/0.52  thf('32', plain,
% 0.24/0.52      (![X21 : $i]:
% 0.24/0.52         (((k1_relat_1 @ X21) != (k1_xboole_0))
% 0.24/0.52          | ((k2_relat_1 @ X21) = (k1_xboole_0))
% 0.24/0.52          | ~ (v1_relat_1 @ X21))),
% 0.24/0.52      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.24/0.52  thf('33', plain,
% 0.24/0.52      ((((k1_xboole_0) != (k1_xboole_0))
% 0.24/0.52        | ~ (v1_relat_1 @ sk_D)
% 0.24/0.52        | ((k2_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['31', '32'])).
% 0.24/0.52  thf('34', plain, ((v1_relat_1 @ sk_D)),
% 0.24/0.52      inference('demod', [status(thm)], ['13', '14'])).
% 0.24/0.52  thf('35', plain,
% 0.24/0.52      ((((k1_xboole_0) != (k1_xboole_0))
% 0.24/0.52        | ((k2_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.24/0.52      inference('demod', [status(thm)], ['33', '34'])).
% 0.24/0.52  thf('36', plain, (((k2_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.24/0.52      inference('simplify', [status(thm)], ['35'])).
% 0.24/0.52  thf('37', plain,
% 0.24/0.52      (![X19 : $i, X20 : $i]:
% 0.24/0.52         ((r1_tarski @ (k9_relat_1 @ X19 @ X20) @ (k2_relat_1 @ X19))
% 0.24/0.52          | ~ (v1_relat_1 @ X19))),
% 0.24/0.52      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.24/0.52  thf(d10_xboole_0, axiom,
% 0.24/0.52    (![A:$i,B:$i]:
% 0.24/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.24/0.52  thf('38', plain,
% 0.24/0.52      (![X0 : $i, X2 : $i]:
% 0.24/0.52         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.24/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.24/0.52  thf('39', plain,
% 0.24/0.52      (![X0 : $i, X1 : $i]:
% 0.24/0.52         (~ (v1_relat_1 @ X0)
% 0.24/0.52          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ (k9_relat_1 @ X0 @ X1))
% 0.24/0.52          | ((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ X1)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['37', '38'])).
% 0.24/0.52  thf('40', plain,
% 0.24/0.52      (![X0 : $i]:
% 0.24/0.52         (~ (r1_tarski @ k1_xboole_0 @ (k9_relat_1 @ sk_D @ X0))
% 0.24/0.52          | ((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ X0))
% 0.24/0.52          | ~ (v1_relat_1 @ sk_D))),
% 0.24/0.52      inference('sup-', [status(thm)], ['36', '39'])).
% 0.24/0.52  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.24/0.52  thf('41', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.24/0.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.24/0.52  thf('42', plain, (((k2_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.24/0.52      inference('simplify', [status(thm)], ['35'])).
% 0.24/0.52  thf('43', plain, ((v1_relat_1 @ sk_D)),
% 0.24/0.52      inference('demod', [status(thm)], ['13', '14'])).
% 0.24/0.52  thf('44', plain, (![X0 : $i]: ((k1_xboole_0) = (k9_relat_1 @ sk_D @ X0))),
% 0.24/0.52      inference('demod', [status(thm)], ['40', '41', '42', '43'])).
% 0.24/0.52  thf('45', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.24/0.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.24/0.52  thf('46', plain, ($false),
% 0.24/0.52      inference('demod', [status(thm)], ['4', '44', '45'])).
% 0.24/0.52  
% 0.24/0.52  % SZS output end Refutation
% 0.24/0.52  
% 0.24/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
