%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yu6Ck296lh

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:58 EST 2020

% Result     : Theorem 0.83s
% Output     : Refutation 0.83s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 206 expanded)
%              Number of leaves         :   36 (  76 expanded)
%              Depth                    :   20
%              Number of atoms          :  585 (2382 expanded)
%              Number of equality atoms :   62 ( 161 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( ( k7_relset_1 @ X34 @ X35 @ X33 @ X36 )
        = ( k9_relat_1 @ X33 @ X36 ) ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v4_relat_1 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
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
    ! [X20: $i,X21: $i] :
      ( ( X20
        = ( k7_relat_1 @ X20 @ X21 ) )
      | ~ ( v4_relat_1 @ X20 @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v1_relat_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
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
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X23 @ X24 ) ) @ X24 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
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

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l45_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('20',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( X8
        = ( k2_tarski @ X6 @ X7 ) )
      | ( X8
        = ( k1_tarski @ X7 ) )
      | ( X8
        = ( k1_tarski @ X6 ) )
      | ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ ( k2_tarski @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( k2_tarski @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('25',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('27',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k1_relat_1 @ X26 )
       != ( k1_tarski @ X25 ) )
      | ( ( k2_relat_1 @ X26 )
        = ( k1_tarski @ ( k1_funct_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D ) )
      | ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['28'])).

thf('30',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('32',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('34',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('37',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['35','36'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('38',plain,(
    ! [X22: $i] :
      ( ( ( k1_relat_1 @ X22 )
       != k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('39',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('41',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    sk_D = k1_xboole_0 ),
    inference(simplify,[status(thm)],['41'])).

thf(t150_relat_1,axiom,(
    ! [A: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('43',plain,(
    ! [X19: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X19 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t150_relat_1])).

thf('44',plain,(
    sk_D = k1_xboole_0 ),
    inference(simplify,[status(thm)],['41'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('45',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('46',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['4','42','43','44','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yu6Ck296lh
% 0.13/0.37  % Computer   : n021.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 12:38:49 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.83/1.07  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.83/1.07  % Solved by: fo/fo7.sh
% 0.83/1.07  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.83/1.07  % done 783 iterations in 0.589s
% 0.83/1.07  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.83/1.07  % SZS output start Refutation
% 0.83/1.07  thf(sk_D_type, type, sk_D: $i).
% 0.83/1.07  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.83/1.07  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.83/1.07  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.83/1.07  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.83/1.07  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.83/1.07  thf(sk_B_type, type, sk_B: $i).
% 0.83/1.07  thf(sk_A_type, type, sk_A: $i).
% 0.83/1.07  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.83/1.07  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.83/1.07  thf(sk_C_type, type, sk_C: $i).
% 0.83/1.07  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.83/1.07  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.83/1.07  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.83/1.07  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.83/1.07  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.83/1.07  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.83/1.07  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.83/1.07  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.83/1.07  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.83/1.07  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.83/1.07  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.83/1.07  thf(t64_funct_2, conjecture,
% 0.83/1.07    (![A:$i,B:$i,C:$i,D:$i]:
% 0.83/1.07     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.83/1.07         ( m1_subset_1 @
% 0.83/1.07           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.83/1.07       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.83/1.07         ( r1_tarski @
% 0.83/1.07           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.83/1.07           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.83/1.07  thf(zf_stmt_0, negated_conjecture,
% 0.83/1.07    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.83/1.07        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.83/1.07            ( m1_subset_1 @
% 0.83/1.07              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.83/1.07          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.83/1.07            ( r1_tarski @
% 0.83/1.07              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.83/1.07              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.83/1.07    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.83/1.07  thf('0', plain,
% 0.83/1.07      (~ (r1_tarski @ 
% 0.83/1.07          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.83/1.07          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('1', plain,
% 0.83/1.07      ((m1_subset_1 @ sk_D @ 
% 0.83/1.07        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf(redefinition_k7_relset_1, axiom,
% 0.83/1.07    (![A:$i,B:$i,C:$i,D:$i]:
% 0.83/1.07     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.83/1.07       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.83/1.07  thf('2', plain,
% 0.83/1.07      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.83/1.07         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.83/1.07          | ((k7_relset_1 @ X34 @ X35 @ X33 @ X36) = (k9_relat_1 @ X33 @ X36)))),
% 0.83/1.07      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.83/1.07  thf('3', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.83/1.07           = (k9_relat_1 @ sk_D @ X0))),
% 0.83/1.07      inference('sup-', [status(thm)], ['1', '2'])).
% 0.83/1.07  thf('4', plain,
% 0.83/1.07      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.83/1.07          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.83/1.07      inference('demod', [status(thm)], ['0', '3'])).
% 0.83/1.07  thf(t144_relat_1, axiom,
% 0.83/1.07    (![A:$i,B:$i]:
% 0.83/1.07     ( ( v1_relat_1 @ B ) =>
% 0.83/1.07       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.83/1.07  thf('5', plain,
% 0.83/1.07      (![X17 : $i, X18 : $i]:
% 0.83/1.07         ((r1_tarski @ (k9_relat_1 @ X17 @ X18) @ (k2_relat_1 @ X17))
% 0.83/1.07          | ~ (v1_relat_1 @ X17))),
% 0.83/1.07      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.83/1.07  thf('6', plain,
% 0.83/1.07      ((m1_subset_1 @ sk_D @ 
% 0.83/1.07        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf(cc2_relset_1, axiom,
% 0.83/1.07    (![A:$i,B:$i,C:$i]:
% 0.83/1.07     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.83/1.07       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.83/1.07  thf('7', plain,
% 0.83/1.07      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.83/1.07         ((v4_relat_1 @ X30 @ X31)
% 0.83/1.07          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.83/1.07      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.83/1.07  thf('8', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 0.83/1.07      inference('sup-', [status(thm)], ['6', '7'])).
% 0.83/1.07  thf(t209_relat_1, axiom,
% 0.83/1.07    (![A:$i,B:$i]:
% 0.83/1.07     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.83/1.07       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.83/1.07  thf('9', plain,
% 0.83/1.07      (![X20 : $i, X21 : $i]:
% 0.83/1.07         (((X20) = (k7_relat_1 @ X20 @ X21))
% 0.83/1.07          | ~ (v4_relat_1 @ X20 @ X21)
% 0.83/1.07          | ~ (v1_relat_1 @ X20))),
% 0.83/1.07      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.83/1.07  thf('10', plain,
% 0.83/1.07      ((~ (v1_relat_1 @ sk_D)
% 0.83/1.07        | ((sk_D) = (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A))))),
% 0.83/1.07      inference('sup-', [status(thm)], ['8', '9'])).
% 0.83/1.07  thf('11', plain,
% 0.83/1.07      ((m1_subset_1 @ sk_D @ 
% 0.83/1.07        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf(cc1_relset_1, axiom,
% 0.83/1.07    (![A:$i,B:$i,C:$i]:
% 0.83/1.07     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.83/1.07       ( v1_relat_1 @ C ) ))).
% 0.83/1.07  thf('12', plain,
% 0.83/1.07      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.83/1.07         ((v1_relat_1 @ X27)
% 0.83/1.07          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.83/1.07      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.83/1.07  thf('13', plain, ((v1_relat_1 @ sk_D)),
% 0.83/1.07      inference('sup-', [status(thm)], ['11', '12'])).
% 0.83/1.07  thf('14', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A)))),
% 0.83/1.07      inference('demod', [status(thm)], ['10', '13'])).
% 0.83/1.07  thf(t87_relat_1, axiom,
% 0.83/1.07    (![A:$i,B:$i]:
% 0.83/1.07     ( ( v1_relat_1 @ B ) =>
% 0.83/1.07       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.83/1.07  thf('15', plain,
% 0.83/1.07      (![X23 : $i, X24 : $i]:
% 0.83/1.07         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X23 @ X24)) @ X24)
% 0.83/1.07          | ~ (v1_relat_1 @ X23))),
% 0.83/1.07      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.83/1.07  thf('16', plain,
% 0.83/1.07      (((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))
% 0.83/1.07        | ~ (v1_relat_1 @ sk_D))),
% 0.83/1.07      inference('sup+', [status(thm)], ['14', '15'])).
% 0.83/1.07  thf('17', plain, ((v1_relat_1 @ sk_D)),
% 0.83/1.07      inference('sup-', [status(thm)], ['11', '12'])).
% 0.83/1.07  thf('18', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 0.83/1.07      inference('demod', [status(thm)], ['16', '17'])).
% 0.83/1.07  thf(t69_enumset1, axiom,
% 0.83/1.07    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.83/1.07  thf('19', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.83/1.07      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.83/1.07  thf(l45_zfmisc_1, axiom,
% 0.83/1.07    (![A:$i,B:$i,C:$i]:
% 0.83/1.07     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.83/1.07       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.83/1.07            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.83/1.07  thf('20', plain,
% 0.83/1.07      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.83/1.07         (((X8) = (k2_tarski @ X6 @ X7))
% 0.83/1.07          | ((X8) = (k1_tarski @ X7))
% 0.83/1.07          | ((X8) = (k1_tarski @ X6))
% 0.83/1.07          | ((X8) = (k1_xboole_0))
% 0.83/1.07          | ~ (r1_tarski @ X8 @ (k2_tarski @ X6 @ X7)))),
% 0.83/1.07      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.83/1.07  thf('21', plain,
% 0.83/1.07      (![X0 : $i, X1 : $i]:
% 0.83/1.07         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.83/1.07          | ((X1) = (k1_xboole_0))
% 0.83/1.07          | ((X1) = (k1_tarski @ X0))
% 0.83/1.07          | ((X1) = (k1_tarski @ X0))
% 0.83/1.07          | ((X1) = (k2_tarski @ X0 @ X0)))),
% 0.83/1.07      inference('sup-', [status(thm)], ['19', '20'])).
% 0.83/1.07  thf('22', plain,
% 0.83/1.07      (![X0 : $i, X1 : $i]:
% 0.83/1.07         (((X1) = (k2_tarski @ X0 @ X0))
% 0.83/1.07          | ((X1) = (k1_tarski @ X0))
% 0.83/1.07          | ((X1) = (k1_xboole_0))
% 0.83/1.07          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 0.83/1.07      inference('simplify', [status(thm)], ['21'])).
% 0.83/1.07  thf('23', plain,
% 0.83/1.07      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.83/1.07        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.83/1.07        | ((k1_relat_1 @ sk_D) = (k2_tarski @ sk_A @ sk_A)))),
% 0.83/1.07      inference('sup-', [status(thm)], ['18', '22'])).
% 0.83/1.07  thf('24', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.83/1.07      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.83/1.07  thf('25', plain,
% 0.83/1.07      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.83/1.07        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.83/1.07        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 0.83/1.07      inference('demod', [status(thm)], ['23', '24'])).
% 0.83/1.07  thf('26', plain,
% 0.83/1.07      ((((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.83/1.07        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.83/1.07      inference('simplify', [status(thm)], ['25'])).
% 0.83/1.07  thf(t14_funct_1, axiom,
% 0.83/1.07    (![A:$i,B:$i]:
% 0.83/1.07     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.83/1.07       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.83/1.07         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.83/1.07  thf('27', plain,
% 0.83/1.07      (![X25 : $i, X26 : $i]:
% 0.83/1.07         (((k1_relat_1 @ X26) != (k1_tarski @ X25))
% 0.83/1.07          | ((k2_relat_1 @ X26) = (k1_tarski @ (k1_funct_1 @ X26 @ X25)))
% 0.83/1.07          | ~ (v1_funct_1 @ X26)
% 0.83/1.07          | ~ (v1_relat_1 @ X26))),
% 0.83/1.07      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.83/1.07  thf('28', plain,
% 0.83/1.07      (![X0 : $i]:
% 0.83/1.07         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 0.83/1.07          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.83/1.07          | ~ (v1_relat_1 @ X0)
% 0.83/1.07          | ~ (v1_funct_1 @ X0)
% 0.83/1.07          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.83/1.07      inference('sup-', [status(thm)], ['26', '27'])).
% 0.83/1.07  thf('29', plain,
% 0.83/1.07      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.83/1.07        | ~ (v1_funct_1 @ sk_D)
% 0.83/1.07        | ~ (v1_relat_1 @ sk_D)
% 0.83/1.07        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.83/1.07      inference('eq_res', [status(thm)], ['28'])).
% 0.83/1.07  thf('30', plain, ((v1_funct_1 @ sk_D)),
% 0.83/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.07  thf('31', plain, ((v1_relat_1 @ sk_D)),
% 0.83/1.07      inference('sup-', [status(thm)], ['11', '12'])).
% 0.83/1.07  thf('32', plain,
% 0.83/1.07      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.83/1.07        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.83/1.07      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.83/1.07  thf('33', plain,
% 0.83/1.07      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.83/1.07          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.83/1.07      inference('demod', [status(thm)], ['0', '3'])).
% 0.83/1.07  thf('34', plain,
% 0.83/1.07      ((~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))
% 0.83/1.07        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.83/1.07      inference('sup-', [status(thm)], ['32', '33'])).
% 0.83/1.07  thf('35', plain,
% 0.83/1.07      ((~ (v1_relat_1 @ sk_D) | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.83/1.07      inference('sup-', [status(thm)], ['5', '34'])).
% 0.83/1.07  thf('36', plain, ((v1_relat_1 @ sk_D)),
% 0.83/1.07      inference('sup-', [status(thm)], ['11', '12'])).
% 0.83/1.07  thf('37', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.83/1.07      inference('demod', [status(thm)], ['35', '36'])).
% 0.83/1.07  thf(t64_relat_1, axiom,
% 0.83/1.07    (![A:$i]:
% 0.83/1.07     ( ( v1_relat_1 @ A ) =>
% 0.83/1.07       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.83/1.07           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.83/1.07         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.83/1.07  thf('38', plain,
% 0.83/1.07      (![X22 : $i]:
% 0.83/1.07         (((k1_relat_1 @ X22) != (k1_xboole_0))
% 0.83/1.07          | ((X22) = (k1_xboole_0))
% 0.83/1.07          | ~ (v1_relat_1 @ X22))),
% 0.83/1.07      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.83/1.07  thf('39', plain,
% 0.83/1.07      ((((k1_xboole_0) != (k1_xboole_0))
% 0.83/1.07        | ~ (v1_relat_1 @ sk_D)
% 0.83/1.07        | ((sk_D) = (k1_xboole_0)))),
% 0.83/1.07      inference('sup-', [status(thm)], ['37', '38'])).
% 0.83/1.07  thf('40', plain, ((v1_relat_1 @ sk_D)),
% 0.83/1.07      inference('sup-', [status(thm)], ['11', '12'])).
% 0.83/1.07  thf('41', plain,
% 0.83/1.07      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_D) = (k1_xboole_0)))),
% 0.83/1.07      inference('demod', [status(thm)], ['39', '40'])).
% 0.83/1.07  thf('42', plain, (((sk_D) = (k1_xboole_0))),
% 0.83/1.07      inference('simplify', [status(thm)], ['41'])).
% 0.83/1.07  thf(t150_relat_1, axiom,
% 0.83/1.07    (![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.83/1.07  thf('43', plain,
% 0.83/1.07      (![X19 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X19) = (k1_xboole_0))),
% 0.83/1.07      inference('cnf', [status(esa)], [t150_relat_1])).
% 0.83/1.07  thf('44', plain, (((sk_D) = (k1_xboole_0))),
% 0.83/1.07      inference('simplify', [status(thm)], ['41'])).
% 0.83/1.07  thf(t4_subset_1, axiom,
% 0.83/1.07    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.83/1.07  thf('45', plain,
% 0.83/1.07      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 0.83/1.07      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.83/1.07  thf(t3_subset, axiom,
% 0.83/1.07    (![A:$i,B:$i]:
% 0.83/1.07     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.83/1.07  thf('46', plain,
% 0.83/1.07      (![X11 : $i, X12 : $i]:
% 0.83/1.07         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.83/1.07      inference('cnf', [status(esa)], [t3_subset])).
% 0.83/1.07  thf('47', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.83/1.07      inference('sup-', [status(thm)], ['45', '46'])).
% 0.83/1.07  thf('48', plain, ($false),
% 0.83/1.07      inference('demod', [status(thm)], ['4', '42', '43', '44', '47'])).
% 0.83/1.07  
% 0.83/1.07  % SZS output end Refutation
% 0.83/1.07  
% 0.83/1.08  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
