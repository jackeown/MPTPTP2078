%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Hgt7XYhvnK

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:57 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 197 expanded)
%              Number of leaves         :   35 (  73 expanded)
%              Depth                    :   19
%              Number of atoms          :  710 (2509 expanded)
%              Number of equality atoms :   91 ( 217 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( ( k7_relset_1 @ X27 @ X28 @ X26 @ X29 )
        = ( k9_relat_1 @ X26 @ X29 ) ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X14 @ X15 ) @ ( k2_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v4_relat_1 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ~ ( v4_relat_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('13',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['10','13'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('15',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k1_enumset1 @ X2 @ X2 @ X3 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t142_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) )
    <=> ~ ( ( D != k1_xboole_0 )
          & ( D
           != ( k1_tarski @ A ) )
          & ( D
           != ( k1_tarski @ B ) )
          & ( D
           != ( k1_tarski @ C ) )
          & ( D
           != ( k2_tarski @ A @ B ) )
          & ( D
           != ( k2_tarski @ B @ C ) )
          & ( D
           != ( k2_tarski @ A @ C ) )
          & ( D
           != ( k1_enumset1 @ A @ B @ C ) ) ) ) )).

thf('17',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( X10
        = ( k1_enumset1 @ X7 @ X8 @ X9 ) )
      | ( X10
        = ( k2_tarski @ X7 @ X9 ) )
      | ( X10
        = ( k2_tarski @ X8 @ X9 ) )
      | ( X10
        = ( k2_tarski @ X7 @ X8 ) )
      | ( X10
        = ( k1_tarski @ X9 ) )
      | ( X10
        = ( k1_tarski @ X8 ) )
      | ( X10
        = ( k1_tarski @ X7 ) )
      | ( X10 = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t142_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( X2 = k1_xboole_0 )
      | ( X2
        = ( k1_tarski @ X1 ) )
      | ( X2
        = ( k1_tarski @ X1 ) )
      | ( X2
        = ( k1_tarski @ X0 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X1 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X2
        = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k1_enumset1 @ X2 @ X2 @ X3 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( X2 = k1_xboole_0 )
      | ( X2
        = ( k1_tarski @ X1 ) )
      | ( X2
        = ( k1_tarski @ X1 ) )
      | ( X2
        = ( k1_tarski @ X0 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X1 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X1 ) )
      | ( X2
        = ( k1_tarski @ X0 ) )
      | ( X2
        = ( k1_tarski @ X1 ) )
      | ( X2 = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( k2_tarski @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','23'])).

thf('25',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('26',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('28',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k1_relat_1 @ X19 )
       != ( k1_tarski @ X18 ) )
      | ( ( k2_relat_1 @ X19 )
        = ( k1_tarski @ ( k1_funct_1 @ X19 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D ) )
      | ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['29'])).

thf('31',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('33',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('35',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('38',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['36','37'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('39',plain,(
    ! [X17: $i] :
      ( ( ( k1_relat_1 @ X17 )
       != k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('40',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('42',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    sk_D = k1_xboole_0 ),
    inference(simplify,[status(thm)],['42'])).

thf(t150_relat_1,axiom,(
    ! [A: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('44',plain,(
    ! [X16: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t150_relat_1])).

thf('45',plain,(
    sk_D = k1_xboole_0 ),
    inference(simplify,[status(thm)],['42'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['4','43','44','45','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Hgt7XYhvnK
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:46:45 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.37/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.54  % Solved by: fo/fo7.sh
% 0.37/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.54  % done 235 iterations in 0.104s
% 0.37/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.54  % SZS output start Refutation
% 0.37/0.54  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.37/0.54  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.37/0.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.37/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.54  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.37/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.37/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.37/0.54  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.37/0.54  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.37/0.54  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.37/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.54  thf(sk_D_type, type, sk_D: $i).
% 0.37/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.54  thf(t64_funct_2, conjecture,
% 0.37/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.54     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.37/0.54         ( m1_subset_1 @
% 0.37/0.54           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.37/0.54       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.37/0.54         ( r1_tarski @
% 0.37/0.54           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.37/0.54           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.37/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.54    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.54        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.37/0.54            ( m1_subset_1 @
% 0.37/0.54              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.37/0.54          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.37/0.54            ( r1_tarski @
% 0.37/0.54              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.37/0.54              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.37/0.54    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.37/0.54  thf('0', plain,
% 0.37/0.54      (~ (r1_tarski @ 
% 0.37/0.54          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.37/0.54          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('1', plain,
% 0.37/0.54      ((m1_subset_1 @ sk_D @ 
% 0.37/0.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf(redefinition_k7_relset_1, axiom,
% 0.37/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.54       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.37/0.54  thf('2', plain,
% 0.37/0.54      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.37/0.54         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.37/0.54          | ((k7_relset_1 @ X27 @ X28 @ X26 @ X29) = (k9_relat_1 @ X26 @ X29)))),
% 0.37/0.54      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.37/0.54  thf('3', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.37/0.54           = (k9_relat_1 @ sk_D @ X0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.54  thf('4', plain,
% 0.37/0.54      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.37/0.54          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.37/0.54      inference('demod', [status(thm)], ['0', '3'])).
% 0.37/0.54  thf(t144_relat_1, axiom,
% 0.37/0.54    (![A:$i,B:$i]:
% 0.37/0.54     ( ( v1_relat_1 @ B ) =>
% 0.37/0.54       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.37/0.54  thf('5', plain,
% 0.37/0.54      (![X14 : $i, X15 : $i]:
% 0.37/0.54         ((r1_tarski @ (k9_relat_1 @ X14 @ X15) @ (k2_relat_1 @ X14))
% 0.37/0.54          | ~ (v1_relat_1 @ X14))),
% 0.37/0.54      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.37/0.54  thf('6', plain,
% 0.37/0.54      ((m1_subset_1 @ sk_D @ 
% 0.37/0.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf(cc2_relset_1, axiom,
% 0.37/0.54    (![A:$i,B:$i,C:$i]:
% 0.37/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.54       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.37/0.54  thf('7', plain,
% 0.37/0.54      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.37/0.54         ((v4_relat_1 @ X23 @ X24)
% 0.37/0.54          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.37/0.54      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.37/0.54  thf('8', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 0.37/0.54      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.54  thf(d18_relat_1, axiom,
% 0.37/0.54    (![A:$i,B:$i]:
% 0.37/0.54     ( ( v1_relat_1 @ B ) =>
% 0.37/0.54       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.37/0.54  thf('9', plain,
% 0.37/0.54      (![X12 : $i, X13 : $i]:
% 0.37/0.54         (~ (v4_relat_1 @ X12 @ X13)
% 0.37/0.54          | (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 0.37/0.54          | ~ (v1_relat_1 @ X12))),
% 0.37/0.54      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.37/0.54  thf('10', plain,
% 0.37/0.54      ((~ (v1_relat_1 @ sk_D)
% 0.37/0.54        | (r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['8', '9'])).
% 0.37/0.54  thf('11', plain,
% 0.37/0.54      ((m1_subset_1 @ sk_D @ 
% 0.37/0.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf(cc1_relset_1, axiom,
% 0.37/0.54    (![A:$i,B:$i,C:$i]:
% 0.37/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.54       ( v1_relat_1 @ C ) ))).
% 0.37/0.54  thf('12', plain,
% 0.37/0.54      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.37/0.54         ((v1_relat_1 @ X20)
% 0.37/0.54          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.37/0.54      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.37/0.54  thf('13', plain, ((v1_relat_1 @ sk_D)),
% 0.37/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.37/0.54  thf('14', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 0.37/0.54      inference('demod', [status(thm)], ['10', '13'])).
% 0.37/0.54  thf(t69_enumset1, axiom,
% 0.37/0.54    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.37/0.54  thf('15', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.37/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.54  thf(t70_enumset1, axiom,
% 0.37/0.54    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.37/0.54  thf('16', plain,
% 0.37/0.54      (![X2 : $i, X3 : $i]:
% 0.37/0.54         ((k1_enumset1 @ X2 @ X2 @ X3) = (k2_tarski @ X2 @ X3))),
% 0.37/0.54      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.37/0.54  thf(t142_zfmisc_1, axiom,
% 0.37/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.54     ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.37/0.54       ( ~( ( ( D ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_tarski @ A ) ) & 
% 0.37/0.54            ( ( D ) != ( k1_tarski @ B ) ) & ( ( D ) != ( k1_tarski @ C ) ) & 
% 0.37/0.54            ( ( D ) != ( k2_tarski @ A @ B ) ) & 
% 0.37/0.54            ( ( D ) != ( k2_tarski @ B @ C ) ) & 
% 0.37/0.54            ( ( D ) != ( k2_tarski @ A @ C ) ) & 
% 0.37/0.54            ( ( D ) != ( k1_enumset1 @ A @ B @ C ) ) ) ) ))).
% 0.37/0.54  thf('17', plain,
% 0.37/0.54      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.37/0.54         (((X10) = (k1_enumset1 @ X7 @ X8 @ X9))
% 0.37/0.54          | ((X10) = (k2_tarski @ X7 @ X9))
% 0.37/0.54          | ((X10) = (k2_tarski @ X8 @ X9))
% 0.37/0.54          | ((X10) = (k2_tarski @ X7 @ X8))
% 0.37/0.54          | ((X10) = (k1_tarski @ X9))
% 0.37/0.54          | ((X10) = (k1_tarski @ X8))
% 0.37/0.54          | ((X10) = (k1_tarski @ X7))
% 0.37/0.54          | ((X10) = (k1_xboole_0))
% 0.37/0.54          | ~ (r1_tarski @ X10 @ (k1_enumset1 @ X7 @ X8 @ X9)))),
% 0.37/0.54      inference('cnf', [status(esa)], [t142_zfmisc_1])).
% 0.37/0.54  thf('18', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.54         (~ (r1_tarski @ X2 @ (k2_tarski @ X1 @ X0))
% 0.37/0.54          | ((X2) = (k1_xboole_0))
% 0.37/0.54          | ((X2) = (k1_tarski @ X1))
% 0.37/0.54          | ((X2) = (k1_tarski @ X1))
% 0.37/0.54          | ((X2) = (k1_tarski @ X0))
% 0.37/0.54          | ((X2) = (k2_tarski @ X1 @ X1))
% 0.37/0.54          | ((X2) = (k2_tarski @ X1 @ X0))
% 0.37/0.54          | ((X2) = (k2_tarski @ X1 @ X0))
% 0.37/0.54          | ((X2) = (k1_enumset1 @ X1 @ X1 @ X0)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.37/0.54  thf('19', plain,
% 0.37/0.54      (![X2 : $i, X3 : $i]:
% 0.37/0.54         ((k1_enumset1 @ X2 @ X2 @ X3) = (k2_tarski @ X2 @ X3))),
% 0.37/0.54      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.37/0.54  thf('20', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.54         (~ (r1_tarski @ X2 @ (k2_tarski @ X1 @ X0))
% 0.37/0.54          | ((X2) = (k1_xboole_0))
% 0.37/0.54          | ((X2) = (k1_tarski @ X1))
% 0.37/0.54          | ((X2) = (k1_tarski @ X1))
% 0.37/0.54          | ((X2) = (k1_tarski @ X0))
% 0.37/0.54          | ((X2) = (k2_tarski @ X1 @ X1))
% 0.37/0.54          | ((X2) = (k2_tarski @ X1 @ X0))
% 0.37/0.54          | ((X2) = (k2_tarski @ X1 @ X0))
% 0.37/0.54          | ((X2) = (k2_tarski @ X1 @ X0)))),
% 0.37/0.54      inference('demod', [status(thm)], ['18', '19'])).
% 0.37/0.54  thf('21', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.54         (((X2) = (k2_tarski @ X1 @ X0))
% 0.37/0.54          | ((X2) = (k2_tarski @ X1 @ X1))
% 0.37/0.54          | ((X2) = (k1_tarski @ X0))
% 0.37/0.54          | ((X2) = (k1_tarski @ X1))
% 0.37/0.54          | ((X2) = (k1_xboole_0))
% 0.37/0.54          | ~ (r1_tarski @ X2 @ (k2_tarski @ X1 @ X0)))),
% 0.37/0.54      inference('simplify', [status(thm)], ['20'])).
% 0.37/0.54  thf('22', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.37/0.54          | ((X1) = (k1_xboole_0))
% 0.37/0.54          | ((X1) = (k1_tarski @ X0))
% 0.37/0.54          | ((X1) = (k1_tarski @ X0))
% 0.37/0.54          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.37/0.54          | ((X1) = (k2_tarski @ X0 @ X0)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['15', '21'])).
% 0.37/0.54  thf('23', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         (((X1) = (k2_tarski @ X0 @ X0))
% 0.37/0.54          | ((X1) = (k1_tarski @ X0))
% 0.37/0.54          | ((X1) = (k1_xboole_0))
% 0.37/0.54          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 0.37/0.54      inference('simplify', [status(thm)], ['22'])).
% 0.37/0.54  thf('24', plain,
% 0.37/0.54      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.37/0.54        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.37/0.54        | ((k1_relat_1 @ sk_D) = (k2_tarski @ sk_A @ sk_A)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['14', '23'])).
% 0.37/0.54  thf('25', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.37/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.54  thf('26', plain,
% 0.37/0.54      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.37/0.54        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.37/0.54        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 0.37/0.54      inference('demod', [status(thm)], ['24', '25'])).
% 0.37/0.54  thf('27', plain,
% 0.37/0.54      ((((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.37/0.54        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.37/0.54      inference('simplify', [status(thm)], ['26'])).
% 0.37/0.54  thf(t14_funct_1, axiom,
% 0.37/0.54    (![A:$i,B:$i]:
% 0.37/0.54     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.37/0.54       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.37/0.54         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.37/0.54  thf('28', plain,
% 0.37/0.54      (![X18 : $i, X19 : $i]:
% 0.37/0.54         (((k1_relat_1 @ X19) != (k1_tarski @ X18))
% 0.37/0.54          | ((k2_relat_1 @ X19) = (k1_tarski @ (k1_funct_1 @ X19 @ X18)))
% 0.37/0.54          | ~ (v1_funct_1 @ X19)
% 0.37/0.54          | ~ (v1_relat_1 @ X19))),
% 0.37/0.54      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.37/0.54  thf('29', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 0.37/0.54          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.37/0.54          | ~ (v1_relat_1 @ X0)
% 0.37/0.54          | ~ (v1_funct_1 @ X0)
% 0.37/0.54          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.37/0.54      inference('sup-', [status(thm)], ['27', '28'])).
% 0.37/0.54  thf('30', plain,
% 0.37/0.54      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.37/0.54        | ~ (v1_funct_1 @ sk_D)
% 0.37/0.54        | ~ (v1_relat_1 @ sk_D)
% 0.37/0.54        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.37/0.54      inference('eq_res', [status(thm)], ['29'])).
% 0.37/0.54  thf('31', plain, ((v1_funct_1 @ sk_D)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('32', plain, ((v1_relat_1 @ sk_D)),
% 0.37/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.37/0.54  thf('33', plain,
% 0.37/0.54      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.37/0.54        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.37/0.54      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.37/0.54  thf('34', plain,
% 0.37/0.54      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.37/0.54          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.37/0.54      inference('demod', [status(thm)], ['0', '3'])).
% 0.37/0.54  thf('35', plain,
% 0.37/0.54      ((~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))
% 0.37/0.54        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['33', '34'])).
% 0.37/0.54  thf('36', plain,
% 0.37/0.54      ((~ (v1_relat_1 @ sk_D) | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['5', '35'])).
% 0.37/0.54  thf('37', plain, ((v1_relat_1 @ sk_D)),
% 0.37/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.37/0.54  thf('38', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.37/0.54      inference('demod', [status(thm)], ['36', '37'])).
% 0.37/0.54  thf(t64_relat_1, axiom,
% 0.37/0.54    (![A:$i]:
% 0.37/0.54     ( ( v1_relat_1 @ A ) =>
% 0.37/0.54       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.37/0.54           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.37/0.54         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.37/0.54  thf('39', plain,
% 0.37/0.54      (![X17 : $i]:
% 0.37/0.54         (((k1_relat_1 @ X17) != (k1_xboole_0))
% 0.37/0.54          | ((X17) = (k1_xboole_0))
% 0.37/0.54          | ~ (v1_relat_1 @ X17))),
% 0.37/0.54      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.37/0.54  thf('40', plain,
% 0.37/0.54      ((((k1_xboole_0) != (k1_xboole_0))
% 0.37/0.54        | ~ (v1_relat_1 @ sk_D)
% 0.37/0.54        | ((sk_D) = (k1_xboole_0)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['38', '39'])).
% 0.37/0.54  thf('41', plain, ((v1_relat_1 @ sk_D)),
% 0.37/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.37/0.54  thf('42', plain,
% 0.37/0.54      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_D) = (k1_xboole_0)))),
% 0.37/0.54      inference('demod', [status(thm)], ['40', '41'])).
% 0.37/0.54  thf('43', plain, (((sk_D) = (k1_xboole_0))),
% 0.37/0.54      inference('simplify', [status(thm)], ['42'])).
% 0.37/0.54  thf(t150_relat_1, axiom,
% 0.37/0.54    (![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.37/0.54  thf('44', plain,
% 0.37/0.54      (![X16 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X16) = (k1_xboole_0))),
% 0.37/0.54      inference('cnf', [status(esa)], [t150_relat_1])).
% 0.37/0.54  thf('45', plain, (((sk_D) = (k1_xboole_0))),
% 0.37/0.54      inference('simplify', [status(thm)], ['42'])).
% 0.37/0.54  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.37/0.54  thf('46', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.37/0.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.37/0.54  thf('47', plain, ($false),
% 0.37/0.54      inference('demod', [status(thm)], ['4', '43', '44', '45', '46'])).
% 0.37/0.54  
% 0.37/0.54  % SZS output end Refutation
% 0.37/0.54  
% 0.37/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
