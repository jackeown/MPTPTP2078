%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uDlaGjF6GO

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:56 EST 2020

% Result     : Theorem 0.56s
% Output     : Refutation 0.56s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 168 expanded)
%              Number of leaves         :   32 (  64 expanded)
%              Depth                    :   16
%              Number of atoms          :  448 (1938 expanded)
%              Number of equality atoms :   38 ( 107 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X15 @ X16 ) @ ( k2_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ~ ( v4_relat_1 @ X13 @ X14 )
      | ( r1_tarski @ ( k1_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
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
    ! [X3: $i,X4: $i] :
      ( ( X4
        = ( k1_tarski @ X3 ) )
      | ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ ( k1_tarski @ X3 ) ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( ( ( k1_relat_1 @ X20 )
       != ( k1_tarski @ X19 ) )
      | ( ( k2_relat_1 @ X20 )
        = ( k1_tarski @ ( k1_funct_1 @ X20 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
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
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('24',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('27',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['25','26'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('28',plain,(
    ! [X18: $i] :
      ( ( ( k1_relat_1 @ X18 )
       != k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('29',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('31',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    sk_D = k1_xboole_0 ),
    inference(simplify,[status(thm)],['31'])).

thf(t150_relat_1,axiom,(
    ! [A: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('33',plain,(
    ! [X17: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X17 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t150_relat_1])).

thf('34',plain,(
    sk_D = k1_xboole_0 ),
    inference(simplify,[status(thm)],['31'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('35',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('36',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('37',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    $false ),
    inference(demod,[status(thm)],['4','32','33','34','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uDlaGjF6GO
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:29:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.56/0.75  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.56/0.75  % Solved by: fo/fo7.sh
% 0.56/0.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.56/0.75  % done 728 iterations in 0.289s
% 0.56/0.75  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.56/0.75  % SZS output start Refutation
% 0.56/0.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.56/0.75  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.56/0.75  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.56/0.75  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.56/0.75  thf(sk_A_type, type, sk_A: $i).
% 0.56/0.75  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.56/0.75  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.56/0.75  thf(sk_D_type, type, sk_D: $i).
% 0.56/0.75  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.56/0.75  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.56/0.75  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.56/0.75  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.56/0.75  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.56/0.75  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.56/0.75  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.56/0.75  thf(sk_B_type, type, sk_B: $i).
% 0.56/0.75  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.56/0.75  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.56/0.75  thf(sk_C_type, type, sk_C: $i).
% 0.56/0.75  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.56/0.75  thf(t64_funct_2, conjecture,
% 0.56/0.75    (![A:$i,B:$i,C:$i,D:$i]:
% 0.56/0.75     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.56/0.75         ( m1_subset_1 @
% 0.56/0.75           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.56/0.75       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.56/0.75         ( r1_tarski @
% 0.56/0.75           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.56/0.75           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.56/0.75  thf(zf_stmt_0, negated_conjecture,
% 0.56/0.75    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.56/0.75        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.56/0.75            ( m1_subset_1 @
% 0.56/0.75              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.56/0.75          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.56/0.75            ( r1_tarski @
% 0.56/0.75              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.56/0.75              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.56/0.75    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.56/0.75  thf('0', plain,
% 0.56/0.75      (~ (r1_tarski @ 
% 0.56/0.75          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.56/0.75          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.56/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.75  thf('1', plain,
% 0.56/0.75      ((m1_subset_1 @ sk_D @ 
% 0.56/0.75        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.56/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.75  thf(redefinition_k7_relset_1, axiom,
% 0.56/0.75    (![A:$i,B:$i,C:$i,D:$i]:
% 0.56/0.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.56/0.75       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.56/0.75  thf('2', plain,
% 0.56/0.75      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.56/0.75         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.56/0.75          | ((k7_relset_1 @ X28 @ X29 @ X27 @ X30) = (k9_relat_1 @ X27 @ X30)))),
% 0.56/0.75      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.56/0.75  thf('3', plain,
% 0.56/0.75      (![X0 : $i]:
% 0.56/0.75         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.56/0.75           = (k9_relat_1 @ sk_D @ X0))),
% 0.56/0.75      inference('sup-', [status(thm)], ['1', '2'])).
% 0.56/0.75  thf('4', plain,
% 0.56/0.75      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.56/0.75          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.56/0.75      inference('demod', [status(thm)], ['0', '3'])).
% 0.56/0.75  thf(t144_relat_1, axiom,
% 0.56/0.75    (![A:$i,B:$i]:
% 0.56/0.75     ( ( v1_relat_1 @ B ) =>
% 0.56/0.75       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.56/0.75  thf('5', plain,
% 0.56/0.75      (![X15 : $i, X16 : $i]:
% 0.56/0.75         ((r1_tarski @ (k9_relat_1 @ X15 @ X16) @ (k2_relat_1 @ X15))
% 0.56/0.75          | ~ (v1_relat_1 @ X15))),
% 0.56/0.75      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.56/0.75  thf('6', plain,
% 0.56/0.75      ((m1_subset_1 @ sk_D @ 
% 0.56/0.75        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.56/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.75  thf(cc2_relset_1, axiom,
% 0.56/0.75    (![A:$i,B:$i,C:$i]:
% 0.56/0.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.56/0.75       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.56/0.75  thf('7', plain,
% 0.56/0.75      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.56/0.75         ((v4_relat_1 @ X24 @ X25)
% 0.56/0.75          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.56/0.75      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.56/0.75  thf('8', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 0.56/0.75      inference('sup-', [status(thm)], ['6', '7'])).
% 0.56/0.75  thf(d18_relat_1, axiom,
% 0.56/0.75    (![A:$i,B:$i]:
% 0.56/0.75     ( ( v1_relat_1 @ B ) =>
% 0.56/0.75       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.56/0.75  thf('9', plain,
% 0.56/0.75      (![X13 : $i, X14 : $i]:
% 0.56/0.75         (~ (v4_relat_1 @ X13 @ X14)
% 0.56/0.75          | (r1_tarski @ (k1_relat_1 @ X13) @ X14)
% 0.56/0.75          | ~ (v1_relat_1 @ X13))),
% 0.56/0.75      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.56/0.75  thf('10', plain,
% 0.56/0.75      ((~ (v1_relat_1 @ sk_D)
% 0.56/0.75        | (r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A)))),
% 0.56/0.75      inference('sup-', [status(thm)], ['8', '9'])).
% 0.56/0.75  thf('11', plain,
% 0.56/0.75      ((m1_subset_1 @ sk_D @ 
% 0.56/0.75        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.56/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.75  thf(cc1_relset_1, axiom,
% 0.56/0.75    (![A:$i,B:$i,C:$i]:
% 0.56/0.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.56/0.75       ( v1_relat_1 @ C ) ))).
% 0.56/0.75  thf('12', plain,
% 0.56/0.75      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.56/0.75         ((v1_relat_1 @ X21)
% 0.56/0.75          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.56/0.75      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.56/0.75  thf('13', plain, ((v1_relat_1 @ sk_D)),
% 0.56/0.75      inference('sup-', [status(thm)], ['11', '12'])).
% 0.56/0.75  thf('14', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 0.56/0.75      inference('demod', [status(thm)], ['10', '13'])).
% 0.56/0.75  thf(l3_zfmisc_1, axiom,
% 0.56/0.75    (![A:$i,B:$i]:
% 0.56/0.75     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.56/0.75       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.56/0.75  thf('15', plain,
% 0.56/0.75      (![X3 : $i, X4 : $i]:
% 0.56/0.75         (((X4) = (k1_tarski @ X3))
% 0.56/0.75          | ((X4) = (k1_xboole_0))
% 0.56/0.75          | ~ (r1_tarski @ X4 @ (k1_tarski @ X3)))),
% 0.56/0.75      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.56/0.75  thf('16', plain,
% 0.56/0.75      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.56/0.75        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 0.56/0.75      inference('sup-', [status(thm)], ['14', '15'])).
% 0.56/0.75  thf(t14_funct_1, axiom,
% 0.56/0.75    (![A:$i,B:$i]:
% 0.56/0.75     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.56/0.75       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.56/0.75         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.56/0.75  thf('17', plain,
% 0.56/0.75      (![X19 : $i, X20 : $i]:
% 0.56/0.75         (((k1_relat_1 @ X20) != (k1_tarski @ X19))
% 0.56/0.75          | ((k2_relat_1 @ X20) = (k1_tarski @ (k1_funct_1 @ X20 @ X19)))
% 0.56/0.75          | ~ (v1_funct_1 @ X20)
% 0.56/0.75          | ~ (v1_relat_1 @ X20))),
% 0.56/0.75      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.56/0.75  thf('18', plain,
% 0.56/0.75      (![X0 : $i]:
% 0.56/0.75         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 0.56/0.75          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.56/0.75          | ~ (v1_relat_1 @ X0)
% 0.56/0.75          | ~ (v1_funct_1 @ X0)
% 0.56/0.75          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.56/0.75      inference('sup-', [status(thm)], ['16', '17'])).
% 0.56/0.75  thf('19', plain,
% 0.56/0.75      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.56/0.75        | ~ (v1_funct_1 @ sk_D)
% 0.56/0.75        | ~ (v1_relat_1 @ sk_D)
% 0.56/0.75        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.56/0.75      inference('eq_res', [status(thm)], ['18'])).
% 0.56/0.75  thf('20', plain, ((v1_funct_1 @ sk_D)),
% 0.56/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.75  thf('21', plain, ((v1_relat_1 @ sk_D)),
% 0.56/0.75      inference('sup-', [status(thm)], ['11', '12'])).
% 0.56/0.75  thf('22', plain,
% 0.56/0.75      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.56/0.75        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.56/0.75      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.56/0.75  thf('23', plain,
% 0.56/0.75      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.56/0.75          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.56/0.75      inference('demod', [status(thm)], ['0', '3'])).
% 0.56/0.75  thf('24', plain,
% 0.56/0.75      ((~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))
% 0.56/0.75        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.56/0.75      inference('sup-', [status(thm)], ['22', '23'])).
% 0.56/0.75  thf('25', plain,
% 0.56/0.75      ((~ (v1_relat_1 @ sk_D) | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.56/0.75      inference('sup-', [status(thm)], ['5', '24'])).
% 0.56/0.75  thf('26', plain, ((v1_relat_1 @ sk_D)),
% 0.56/0.75      inference('sup-', [status(thm)], ['11', '12'])).
% 0.56/0.75  thf('27', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.56/0.75      inference('demod', [status(thm)], ['25', '26'])).
% 0.56/0.75  thf(t64_relat_1, axiom,
% 0.56/0.75    (![A:$i]:
% 0.56/0.75     ( ( v1_relat_1 @ A ) =>
% 0.56/0.75       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.56/0.75           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.56/0.75         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.56/0.75  thf('28', plain,
% 0.56/0.75      (![X18 : $i]:
% 0.56/0.75         (((k1_relat_1 @ X18) != (k1_xboole_0))
% 0.56/0.75          | ((X18) = (k1_xboole_0))
% 0.56/0.75          | ~ (v1_relat_1 @ X18))),
% 0.56/0.75      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.56/0.75  thf('29', plain,
% 0.56/0.75      ((((k1_xboole_0) != (k1_xboole_0))
% 0.56/0.75        | ~ (v1_relat_1 @ sk_D)
% 0.56/0.75        | ((sk_D) = (k1_xboole_0)))),
% 0.56/0.75      inference('sup-', [status(thm)], ['27', '28'])).
% 0.56/0.75  thf('30', plain, ((v1_relat_1 @ sk_D)),
% 0.56/0.75      inference('sup-', [status(thm)], ['11', '12'])).
% 0.56/0.75  thf('31', plain,
% 0.56/0.75      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_D) = (k1_xboole_0)))),
% 0.56/0.75      inference('demod', [status(thm)], ['29', '30'])).
% 0.56/0.75  thf('32', plain, (((sk_D) = (k1_xboole_0))),
% 0.56/0.75      inference('simplify', [status(thm)], ['31'])).
% 0.56/0.75  thf(t150_relat_1, axiom,
% 0.56/0.75    (![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.56/0.75  thf('33', plain,
% 0.56/0.75      (![X17 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X17) = (k1_xboole_0))),
% 0.56/0.75      inference('cnf', [status(esa)], [t150_relat_1])).
% 0.56/0.75  thf('34', plain, (((sk_D) = (k1_xboole_0))),
% 0.56/0.75      inference('simplify', [status(thm)], ['31'])).
% 0.56/0.75  thf(t4_subset_1, axiom,
% 0.56/0.75    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.56/0.75  thf('35', plain,
% 0.56/0.75      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 0.56/0.75      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.56/0.75  thf(t3_subset, axiom,
% 0.56/0.75    (![A:$i,B:$i]:
% 0.56/0.75     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.56/0.75  thf('36', plain,
% 0.56/0.75      (![X7 : $i, X8 : $i]:
% 0.56/0.75         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.56/0.75      inference('cnf', [status(esa)], [t3_subset])).
% 0.56/0.75  thf('37', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.56/0.75      inference('sup-', [status(thm)], ['35', '36'])).
% 0.56/0.75  thf('38', plain, ($false),
% 0.56/0.75      inference('demod', [status(thm)], ['4', '32', '33', '34', '37'])).
% 0.56/0.75  
% 0.56/0.75  % SZS output end Refutation
% 0.56/0.75  
% 0.56/0.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
