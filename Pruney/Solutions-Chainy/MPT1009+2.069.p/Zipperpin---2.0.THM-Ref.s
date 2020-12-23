%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QPUnXg6kb7

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:58 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 189 expanded)
%              Number of leaves         :   34 (  71 expanded)
%              Depth                    :   18
%              Number of atoms          :  482 (2164 expanded)
%              Number of equality atoms :   42 ( 119 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( ( k7_relset_1 @ X33 @ X34 @ X32 @ X35 )
        = ( k9_relat_1 @ X32 @ X35 ) ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X16 @ X17 ) @ ( k2_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v4_relat_1 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( ( X19
        = ( k7_relat_1 @ X19 @ X20 ) )
      | ~ ( v4_relat_1 @ X19 @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v1_relat_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
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
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X22 @ X23 ) ) @ X23 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
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
    ! [X6: $i,X7: $i] :
      ( ( X7
        = ( k1_tarski @ X6 ) )
      | ( X7 = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ ( k1_tarski @ X6 ) ) ) ),
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
    ! [X24: $i,X25: $i] :
      ( ( ( k1_relat_1 @ X25 )
       != ( k1_tarski @ X24 ) )
      | ( ( k2_relat_1 @ X25 )
        = ( k1_tarski @ ( k1_funct_1 @ X25 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
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
    ! [X21: $i] :
      ( ( ( k1_relat_1 @ X21 )
       != k1_xboole_0 )
      | ( X21 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
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

thf(t150_relat_1,axiom,(
    ! [A: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('37',plain,(
    ! [X18: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t150_relat_1])).

thf('38',plain,(
    sk_D = k1_xboole_0 ),
    inference(simplify,[status(thm)],['35'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('39',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('40',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['4','36','37','38','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QPUnXg6kb7
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:47:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.52/0.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.52/0.74  % Solved by: fo/fo7.sh
% 0.52/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.74  % done 671 iterations in 0.286s
% 0.52/0.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.52/0.74  % SZS output start Refutation
% 0.52/0.74  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.52/0.74  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.52/0.74  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.52/0.74  thf(sk_D_type, type, sk_D: $i).
% 0.52/0.74  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.52/0.74  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.52/0.74  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.52/0.74  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.52/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.74  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.74  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.52/0.74  thf(sk_C_type, type, sk_C: $i).
% 0.52/0.74  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.52/0.74  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.52/0.74  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.52/0.74  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.52/0.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.74  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.52/0.74  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.52/0.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.74  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.52/0.74  thf(t64_funct_2, conjecture,
% 0.52/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.74     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.52/0.74         ( m1_subset_1 @
% 0.52/0.74           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.52/0.74       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.52/0.74         ( r1_tarski @
% 0.52/0.74           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.52/0.74           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.52/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.74    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.74        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.52/0.74            ( m1_subset_1 @
% 0.52/0.74              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.52/0.74          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.52/0.74            ( r1_tarski @
% 0.52/0.74              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.52/0.74              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.52/0.74    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.52/0.74  thf('0', plain,
% 0.52/0.74      (~ (r1_tarski @ 
% 0.52/0.74          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.52/0.74          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf('1', plain,
% 0.52/0.74      ((m1_subset_1 @ sk_D @ 
% 0.52/0.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf(redefinition_k7_relset_1, axiom,
% 0.52/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.74       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.52/0.74  thf('2', plain,
% 0.52/0.74      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.52/0.74         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.52/0.74          | ((k7_relset_1 @ X33 @ X34 @ X32 @ X35) = (k9_relat_1 @ X32 @ X35)))),
% 0.52/0.74      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.52/0.74  thf('3', plain,
% 0.52/0.74      (![X0 : $i]:
% 0.52/0.74         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.52/0.74           = (k9_relat_1 @ sk_D @ X0))),
% 0.52/0.74      inference('sup-', [status(thm)], ['1', '2'])).
% 0.52/0.74  thf('4', plain,
% 0.52/0.74      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.52/0.74          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.52/0.74      inference('demod', [status(thm)], ['0', '3'])).
% 0.52/0.74  thf(t144_relat_1, axiom,
% 0.52/0.74    (![A:$i,B:$i]:
% 0.52/0.74     ( ( v1_relat_1 @ B ) =>
% 0.52/0.74       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.52/0.74  thf('5', plain,
% 0.52/0.74      (![X16 : $i, X17 : $i]:
% 0.52/0.74         ((r1_tarski @ (k9_relat_1 @ X16 @ X17) @ (k2_relat_1 @ X16))
% 0.52/0.74          | ~ (v1_relat_1 @ X16))),
% 0.52/0.74      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.52/0.74  thf('6', plain,
% 0.52/0.74      ((m1_subset_1 @ sk_D @ 
% 0.52/0.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf(cc2_relset_1, axiom,
% 0.52/0.74    (![A:$i,B:$i,C:$i]:
% 0.52/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.74       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.52/0.74  thf('7', plain,
% 0.52/0.74      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.52/0.74         ((v4_relat_1 @ X29 @ X30)
% 0.52/0.74          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.52/0.74      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.52/0.74  thf('8', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 0.52/0.74      inference('sup-', [status(thm)], ['6', '7'])).
% 0.52/0.74  thf(t209_relat_1, axiom,
% 0.52/0.74    (![A:$i,B:$i]:
% 0.52/0.74     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.52/0.74       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.52/0.74  thf('9', plain,
% 0.52/0.74      (![X19 : $i, X20 : $i]:
% 0.52/0.74         (((X19) = (k7_relat_1 @ X19 @ X20))
% 0.52/0.74          | ~ (v4_relat_1 @ X19 @ X20)
% 0.52/0.74          | ~ (v1_relat_1 @ X19))),
% 0.52/0.74      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.52/0.74  thf('10', plain,
% 0.52/0.74      ((~ (v1_relat_1 @ sk_D)
% 0.52/0.74        | ((sk_D) = (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A))))),
% 0.52/0.74      inference('sup-', [status(thm)], ['8', '9'])).
% 0.52/0.74  thf('11', plain,
% 0.52/0.74      ((m1_subset_1 @ sk_D @ 
% 0.52/0.74        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf(cc1_relset_1, axiom,
% 0.52/0.74    (![A:$i,B:$i,C:$i]:
% 0.52/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.74       ( v1_relat_1 @ C ) ))).
% 0.52/0.74  thf('12', plain,
% 0.52/0.74      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.52/0.74         ((v1_relat_1 @ X26)
% 0.52/0.74          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.52/0.74      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.52/0.74  thf('13', plain, ((v1_relat_1 @ sk_D)),
% 0.52/0.74      inference('sup-', [status(thm)], ['11', '12'])).
% 0.52/0.74  thf('14', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A)))),
% 0.52/0.74      inference('demod', [status(thm)], ['10', '13'])).
% 0.52/0.74  thf(t87_relat_1, axiom,
% 0.52/0.74    (![A:$i,B:$i]:
% 0.52/0.74     ( ( v1_relat_1 @ B ) =>
% 0.52/0.74       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.52/0.74  thf('15', plain,
% 0.52/0.74      (![X22 : $i, X23 : $i]:
% 0.52/0.74         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X22 @ X23)) @ X23)
% 0.52/0.74          | ~ (v1_relat_1 @ X22))),
% 0.52/0.74      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.52/0.74  thf('16', plain,
% 0.52/0.74      (((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))
% 0.52/0.74        | ~ (v1_relat_1 @ sk_D))),
% 0.52/0.74      inference('sup+', [status(thm)], ['14', '15'])).
% 0.52/0.74  thf('17', plain, ((v1_relat_1 @ sk_D)),
% 0.52/0.74      inference('sup-', [status(thm)], ['11', '12'])).
% 0.52/0.74  thf('18', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 0.52/0.74      inference('demod', [status(thm)], ['16', '17'])).
% 0.52/0.74  thf(l3_zfmisc_1, axiom,
% 0.52/0.74    (![A:$i,B:$i]:
% 0.52/0.74     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.52/0.74       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.52/0.74  thf('19', plain,
% 0.52/0.74      (![X6 : $i, X7 : $i]:
% 0.52/0.74         (((X7) = (k1_tarski @ X6))
% 0.52/0.74          | ((X7) = (k1_xboole_0))
% 0.52/0.74          | ~ (r1_tarski @ X7 @ (k1_tarski @ X6)))),
% 0.52/0.74      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.52/0.74  thf('20', plain,
% 0.52/0.74      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.52/0.74        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['18', '19'])).
% 0.52/0.74  thf(t14_funct_1, axiom,
% 0.52/0.74    (![A:$i,B:$i]:
% 0.52/0.74     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.52/0.74       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.52/0.74         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.52/0.75  thf('21', plain,
% 0.52/0.75      (![X24 : $i, X25 : $i]:
% 0.52/0.75         (((k1_relat_1 @ X25) != (k1_tarski @ X24))
% 0.52/0.75          | ((k2_relat_1 @ X25) = (k1_tarski @ (k1_funct_1 @ X25 @ X24)))
% 0.52/0.75          | ~ (v1_funct_1 @ X25)
% 0.52/0.75          | ~ (v1_relat_1 @ X25))),
% 0.52/0.75      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.52/0.75  thf('22', plain,
% 0.52/0.75      (![X0 : $i]:
% 0.52/0.75         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 0.52/0.75          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.52/0.75          | ~ (v1_relat_1 @ X0)
% 0.52/0.75          | ~ (v1_funct_1 @ X0)
% 0.52/0.75          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.52/0.75      inference('sup-', [status(thm)], ['20', '21'])).
% 0.52/0.75  thf('23', plain,
% 0.52/0.75      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.52/0.75        | ~ (v1_funct_1 @ sk_D)
% 0.52/0.75        | ~ (v1_relat_1 @ sk_D)
% 0.52/0.75        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.52/0.75      inference('eq_res', [status(thm)], ['22'])).
% 0.52/0.75  thf('24', plain, ((v1_funct_1 @ sk_D)),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf('25', plain, ((v1_relat_1 @ sk_D)),
% 0.52/0.75      inference('sup-', [status(thm)], ['11', '12'])).
% 0.52/0.75  thf('26', plain,
% 0.52/0.75      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.52/0.75        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.52/0.75      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.52/0.75  thf('27', plain,
% 0.52/0.75      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.52/0.75          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.52/0.75      inference('demod', [status(thm)], ['0', '3'])).
% 0.52/0.75  thf('28', plain,
% 0.52/0.75      ((~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))
% 0.52/0.75        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.52/0.75      inference('sup-', [status(thm)], ['26', '27'])).
% 0.52/0.75  thf('29', plain,
% 0.52/0.75      ((~ (v1_relat_1 @ sk_D) | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.52/0.75      inference('sup-', [status(thm)], ['5', '28'])).
% 0.52/0.75  thf('30', plain, ((v1_relat_1 @ sk_D)),
% 0.52/0.75      inference('sup-', [status(thm)], ['11', '12'])).
% 0.52/0.75  thf('31', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.52/0.75      inference('demod', [status(thm)], ['29', '30'])).
% 0.52/0.75  thf(t64_relat_1, axiom,
% 0.52/0.75    (![A:$i]:
% 0.52/0.75     ( ( v1_relat_1 @ A ) =>
% 0.52/0.75       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.52/0.75           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.52/0.75         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.52/0.75  thf('32', plain,
% 0.52/0.75      (![X21 : $i]:
% 0.52/0.75         (((k1_relat_1 @ X21) != (k1_xboole_0))
% 0.52/0.75          | ((X21) = (k1_xboole_0))
% 0.52/0.75          | ~ (v1_relat_1 @ X21))),
% 0.52/0.75      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.52/0.75  thf('33', plain,
% 0.52/0.75      ((((k1_xboole_0) != (k1_xboole_0))
% 0.52/0.75        | ~ (v1_relat_1 @ sk_D)
% 0.52/0.75        | ((sk_D) = (k1_xboole_0)))),
% 0.52/0.75      inference('sup-', [status(thm)], ['31', '32'])).
% 0.52/0.75  thf('34', plain, ((v1_relat_1 @ sk_D)),
% 0.52/0.75      inference('sup-', [status(thm)], ['11', '12'])).
% 0.52/0.75  thf('35', plain,
% 0.52/0.75      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_D) = (k1_xboole_0)))),
% 0.52/0.75      inference('demod', [status(thm)], ['33', '34'])).
% 0.52/0.75  thf('36', plain, (((sk_D) = (k1_xboole_0))),
% 0.52/0.75      inference('simplify', [status(thm)], ['35'])).
% 0.52/0.75  thf(t150_relat_1, axiom,
% 0.52/0.75    (![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.52/0.75  thf('37', plain,
% 0.52/0.75      (![X18 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X18) = (k1_xboole_0))),
% 0.52/0.75      inference('cnf', [status(esa)], [t150_relat_1])).
% 0.52/0.75  thf('38', plain, (((sk_D) = (k1_xboole_0))),
% 0.52/0.75      inference('simplify', [status(thm)], ['35'])).
% 0.52/0.75  thf(t4_subset_1, axiom,
% 0.52/0.75    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.52/0.75  thf('39', plain,
% 0.52/0.75      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.52/0.75      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.52/0.75  thf(t3_subset, axiom,
% 0.52/0.75    (![A:$i,B:$i]:
% 0.52/0.75     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.52/0.75  thf('40', plain,
% 0.52/0.75      (![X10 : $i, X11 : $i]:
% 0.52/0.75         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.52/0.75      inference('cnf', [status(esa)], [t3_subset])).
% 0.52/0.75  thf('41', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.52/0.75      inference('sup-', [status(thm)], ['39', '40'])).
% 0.52/0.75  thf('42', plain, ($false),
% 0.52/0.75      inference('demod', [status(thm)], ['4', '36', '37', '38', '41'])).
% 0.52/0.75  
% 0.52/0.75  % SZS output end Refutation
% 0.52/0.75  
% 0.59/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
