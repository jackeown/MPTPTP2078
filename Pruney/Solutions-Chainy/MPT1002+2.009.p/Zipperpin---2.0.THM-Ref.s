%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4kJAQUXtjE

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:01 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 187 expanded)
%              Number of leaves         :   34 (  67 expanded)
%              Depth                    :   17
%              Number of atoms          :  814 (2492 expanded)
%              Number of equality atoms :   78 ( 204 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t50_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ C @ A )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( r1_tarski @ C @ ( k8_relset_1 @ A @ B @ D @ ( k7_relset_1 @ A @ B @ D @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( r1_tarski @ C @ A )
         => ( ( ( B = k1_xboole_0 )
              & ( A != k1_xboole_0 ) )
            | ( r1_tarski @ C @ ( k8_relset_1 @ A @ B @ D @ ( k7_relset_1 @ A @ B @ D @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_funct_2])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_C @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( ( k7_relset_1 @ X13 @ X14 @ X12 @ X15 )
        = ( k9_relat_1 @ X12 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ sk_C @ ( k8_relset_1 @ sk_A @ sk_B @ sk_D @ ( k9_relat_1 @ sk_D @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('6',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( ( k8_relset_1 @ X17 @ X18 @ X16 @ X19 )
        = ( k10_relat_1 @ X16 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k10_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ~ ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_D @ ( k9_relat_1 @ sk_D @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('9',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ C @ A @ B )
          <=> ( A
              = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_1 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('13',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ( X22
        = ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ~ ( zip_tseitin_1 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('17',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('19',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('20',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('23',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X7 @ ( k1_relat_1 @ X8 ) )
      | ( r1_tarski @ X7 @ ( k10_relat_1 @ X8 @ ( k9_relat_1 @ X8 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( sk_B = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_D )
      | ( r1_tarski @ X0 @ ( k10_relat_1 @ sk_D @ ( k9_relat_1 @ sk_D @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('26',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('28',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('29',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( sk_B = k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k10_relat_1 @ sk_D @ ( k9_relat_1 @ sk_D @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['24','29'])).

thf('31',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['31'])).

thf('33',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['31'])).

thf('34',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['31'])).

thf('37',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ( X22
        = ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ~ ( zip_tseitin_1 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('40',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['31'])).

thf('42',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('44',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X1 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('45',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','45'])).

thf('47',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('48',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ X1 )
        = ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ! [X0: $i] :
        ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ sk_D )
        = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relat_1 @ sk_D ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','50'])).

thf('52',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','45'])).

thf('53',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('54',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_1 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X21 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('57',plain,(
    ! [X20: $i] :
      ( zip_tseitin_0 @ X20 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['55','57'])).

thf('59',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','58'])).

thf('60',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','59'])).

thf('61',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X7 @ ( k1_relat_1 @ X8 ) )
      | ( r1_tarski @ X7 @ ( k10_relat_1 @ X8 @ ( k9_relat_1 @ X8 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('62',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
        | ~ ( v1_relat_1 @ sk_D )
        | ( r1_tarski @ X0 @ ( k10_relat_1 @ sk_D @ ( k9_relat_1 @ sk_D @ X0 ) ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['27','28'])).

thf('64',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
        | ( r1_tarski @ X0 @ ( k10_relat_1 @ sk_D @ ( k9_relat_1 @ sk_D @ X0 ) ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_D @ ( k9_relat_1 @ sk_D @ sk_C ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','64'])).

thf('66',plain,(
    ~ ( r1_tarski @ sk_C @ ( k10_relat_1 @ sk_D @ ( k9_relat_1 @ sk_D @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('67',plain,(
    sk_A != k1_xboole_0 ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['31'])).

thf('69',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['67','68'])).

thf('70',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['32','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( r1_tarski @ X0 @ ( k10_relat_1 @ sk_D @ ( k9_relat_1 @ sk_D @ X0 ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['30','70'])).

thf('72',plain,(
    r1_tarski @ sk_C @ ( k10_relat_1 @ sk_D @ ( k9_relat_1 @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','71'])).

thf('73',plain,(
    $false ),
    inference(demod,[status(thm)],['8','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4kJAQUXtjE
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:45:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.58/0.77  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.58/0.77  % Solved by: fo/fo7.sh
% 0.58/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.77  % done 367 iterations in 0.319s
% 0.58/0.77  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.58/0.77  % SZS output start Refutation
% 0.58/0.77  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.58/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.77  thf(sk_D_type, type, sk_D: $i).
% 0.58/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.77  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.58/0.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.77  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.58/0.77  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.58/0.77  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.58/0.77  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.77  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.58/0.77  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.58/0.77  thf(sk_C_type, type, sk_C: $i).
% 0.58/0.77  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.58/0.77  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.58/0.77  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.58/0.77  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.58/0.77  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.58/0.77  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.58/0.77  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.58/0.77  thf(t50_funct_2, conjecture,
% 0.58/0.77    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.77     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.58/0.77         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.58/0.77       ( ( r1_tarski @ C @ A ) =>
% 0.58/0.77         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.58/0.77           ( r1_tarski @
% 0.58/0.77             C @ ( k8_relset_1 @ A @ B @ D @ ( k7_relset_1 @ A @ B @ D @ C ) ) ) ) ) ))).
% 0.58/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.77    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.77        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.58/0.77            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.58/0.77          ( ( r1_tarski @ C @ A ) =>
% 0.58/0.77            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.58/0.77              ( r1_tarski @
% 0.58/0.77                C @ 
% 0.58/0.77                ( k8_relset_1 @ A @ B @ D @ ( k7_relset_1 @ A @ B @ D @ C ) ) ) ) ) ) )),
% 0.58/0.77    inference('cnf.neg', [status(esa)], [t50_funct_2])).
% 0.58/0.77  thf('0', plain,
% 0.58/0.77      (~ (r1_tarski @ sk_C @ 
% 0.58/0.77          (k8_relset_1 @ sk_A @ sk_B @ sk_D @ 
% 0.58/0.77           (k7_relset_1 @ sk_A @ sk_B @ sk_D @ sk_C)))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('1', plain,
% 0.58/0.77      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf(redefinition_k7_relset_1, axiom,
% 0.58/0.77    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.77       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.58/0.77  thf('2', plain,
% 0.58/0.77      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.58/0.77         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.58/0.77          | ((k7_relset_1 @ X13 @ X14 @ X12 @ X15) = (k9_relat_1 @ X12 @ X15)))),
% 0.58/0.77      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.58/0.77  thf('3', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((k7_relset_1 @ sk_A @ sk_B @ sk_D @ X0) = (k9_relat_1 @ sk_D @ X0))),
% 0.58/0.77      inference('sup-', [status(thm)], ['1', '2'])).
% 0.58/0.77  thf('4', plain,
% 0.58/0.77      (~ (r1_tarski @ sk_C @ 
% 0.58/0.77          (k8_relset_1 @ sk_A @ sk_B @ sk_D @ (k9_relat_1 @ sk_D @ sk_C)))),
% 0.58/0.77      inference('demod', [status(thm)], ['0', '3'])).
% 0.58/0.77  thf('5', plain,
% 0.58/0.77      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf(redefinition_k8_relset_1, axiom,
% 0.58/0.77    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.77       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.58/0.77  thf('6', plain,
% 0.58/0.77      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.58/0.77         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.58/0.77          | ((k8_relset_1 @ X17 @ X18 @ X16 @ X19) = (k10_relat_1 @ X16 @ X19)))),
% 0.58/0.77      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.58/0.77  thf('7', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((k8_relset_1 @ sk_A @ sk_B @ sk_D @ X0) = (k10_relat_1 @ sk_D @ X0))),
% 0.58/0.77      inference('sup-', [status(thm)], ['5', '6'])).
% 0.58/0.77  thf('8', plain,
% 0.58/0.77      (~ (r1_tarski @ sk_C @ (k10_relat_1 @ sk_D @ (k9_relat_1 @ sk_D @ sk_C)))),
% 0.58/0.77      inference('demod', [status(thm)], ['4', '7'])).
% 0.58/0.77  thf('9', plain, ((r1_tarski @ sk_C @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf(d1_funct_2, axiom,
% 0.58/0.77    (![A:$i,B:$i,C:$i]:
% 0.58/0.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.77       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.58/0.77           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.58/0.77             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.58/0.77         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.58/0.77           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.58/0.77             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.58/0.77  thf(zf_stmt_1, axiom,
% 0.58/0.77    (![B:$i,A:$i]:
% 0.58/0.77     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.58/0.77       ( zip_tseitin_0 @ B @ A ) ))).
% 0.58/0.77  thf('10', plain,
% 0.58/0.77      (![X20 : $i, X21 : $i]:
% 0.58/0.77         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.58/0.77  thf('11', plain,
% 0.58/0.77      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.58/0.77  thf(zf_stmt_3, axiom,
% 0.58/0.77    (![C:$i,B:$i,A:$i]:
% 0.58/0.77     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.58/0.77       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.58/0.77  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.58/0.77  thf(zf_stmt_5, axiom,
% 0.58/0.77    (![A:$i,B:$i,C:$i]:
% 0.58/0.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.77       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.58/0.77         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.58/0.77           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.58/0.77             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.58/0.77  thf('12', plain,
% 0.58/0.77      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.58/0.77         (~ (zip_tseitin_0 @ X25 @ X26)
% 0.58/0.77          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 0.58/0.77          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.58/0.77  thf('13', plain,
% 0.58/0.77      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.58/0.77      inference('sup-', [status(thm)], ['11', '12'])).
% 0.58/0.77  thf('14', plain,
% 0.58/0.77      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 0.58/0.77      inference('sup-', [status(thm)], ['10', '13'])).
% 0.58/0.77  thf('15', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('16', plain,
% 0.58/0.77      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.58/0.77         (~ (v1_funct_2 @ X24 @ X22 @ X23)
% 0.58/0.77          | ((X22) = (k1_relset_1 @ X22 @ X23 @ X24))
% 0.58/0.77          | ~ (zip_tseitin_1 @ X24 @ X23 @ X22))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.58/0.77  thf('17', plain,
% 0.58/0.77      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 0.58/0.77        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['15', '16'])).
% 0.58/0.77  thf('18', plain,
% 0.58/0.77      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf(redefinition_k1_relset_1, axiom,
% 0.58/0.77    (![A:$i,B:$i,C:$i]:
% 0.58/0.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.77       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.58/0.77  thf('19', plain,
% 0.58/0.77      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.58/0.77         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 0.58/0.77          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.58/0.77      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.58/0.77  thf('20', plain,
% 0.58/0.77      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.58/0.77      inference('sup-', [status(thm)], ['18', '19'])).
% 0.58/0.77  thf('21', plain,
% 0.58/0.77      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.58/0.77      inference('demod', [status(thm)], ['17', '20'])).
% 0.58/0.77  thf('22', plain,
% 0.58/0.77      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['14', '21'])).
% 0.58/0.77  thf(t146_funct_1, axiom,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ( v1_relat_1 @ B ) =>
% 0.58/0.77       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.58/0.77         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.58/0.77  thf('23', plain,
% 0.58/0.77      (![X7 : $i, X8 : $i]:
% 0.58/0.77         (~ (r1_tarski @ X7 @ (k1_relat_1 @ X8))
% 0.58/0.77          | (r1_tarski @ X7 @ (k10_relat_1 @ X8 @ (k9_relat_1 @ X8 @ X7)))
% 0.58/0.77          | ~ (v1_relat_1 @ X8))),
% 0.58/0.77      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.58/0.77  thf('24', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (r1_tarski @ X0 @ sk_A)
% 0.58/0.77          | ((sk_B) = (k1_xboole_0))
% 0.58/0.77          | ~ (v1_relat_1 @ sk_D)
% 0.58/0.77          | (r1_tarski @ X0 @ (k10_relat_1 @ sk_D @ (k9_relat_1 @ sk_D @ X0))))),
% 0.58/0.77      inference('sup-', [status(thm)], ['22', '23'])).
% 0.58/0.77  thf('25', plain,
% 0.58/0.77      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf(cc2_relat_1, axiom,
% 0.58/0.77    (![A:$i]:
% 0.58/0.77     ( ( v1_relat_1 @ A ) =>
% 0.58/0.77       ( ![B:$i]:
% 0.58/0.77         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.58/0.77  thf('26', plain,
% 0.58/0.77      (![X3 : $i, X4 : $i]:
% 0.58/0.77         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.58/0.77          | (v1_relat_1 @ X3)
% 0.58/0.77          | ~ (v1_relat_1 @ X4))),
% 0.58/0.77      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.58/0.77  thf('27', plain,
% 0.58/0.77      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 0.58/0.77      inference('sup-', [status(thm)], ['25', '26'])).
% 0.58/0.77  thf(fc6_relat_1, axiom,
% 0.58/0.77    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.58/0.77  thf('28', plain,
% 0.58/0.77      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.58/0.77      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.58/0.77  thf('29', plain, ((v1_relat_1 @ sk_D)),
% 0.58/0.77      inference('demod', [status(thm)], ['27', '28'])).
% 0.58/0.77  thf('30', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (r1_tarski @ X0 @ sk_A)
% 0.58/0.77          | ((sk_B) = (k1_xboole_0))
% 0.58/0.77          | (r1_tarski @ X0 @ (k10_relat_1 @ sk_D @ (k9_relat_1 @ sk_D @ X0))))),
% 0.58/0.77      inference('demod', [status(thm)], ['24', '29'])).
% 0.58/0.77  thf('31', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('32', plain,
% 0.58/0.77      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.58/0.77      inference('split', [status(esa)], ['31'])).
% 0.58/0.77  thf('33', plain,
% 0.58/0.77      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.77      inference('split', [status(esa)], ['31'])).
% 0.58/0.77  thf('34', plain, ((r1_tarski @ sk_C @ sk_A)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('35', plain,
% 0.58/0.77      (((r1_tarski @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.77      inference('sup+', [status(thm)], ['33', '34'])).
% 0.58/0.77  thf('36', plain,
% 0.58/0.77      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.77      inference('split', [status(esa)], ['31'])).
% 0.58/0.77  thf('37', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('38', plain,
% 0.58/0.77      (((v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B))
% 0.58/0.77         <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.77      inference('sup+', [status(thm)], ['36', '37'])).
% 0.58/0.77  thf('39', plain,
% 0.58/0.77      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.58/0.77         (~ (v1_funct_2 @ X24 @ X22 @ X23)
% 0.58/0.77          | ((X22) = (k1_relset_1 @ X22 @ X23 @ X24))
% 0.58/0.77          | ~ (zip_tseitin_1 @ X24 @ X23 @ X22))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.58/0.77  thf('40', plain,
% 0.58/0.77      (((~ (zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 0.58/0.77         | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D))))
% 0.58/0.77         <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.77      inference('sup-', [status(thm)], ['38', '39'])).
% 0.58/0.77  thf('41', plain,
% 0.58/0.77      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.77      inference('split', [status(esa)], ['31'])).
% 0.58/0.77  thf('42', plain,
% 0.58/0.77      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('43', plain,
% 0.58/0.77      (((m1_subset_1 @ sk_D @ 
% 0.58/0.77         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.58/0.77         <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.77      inference('sup+', [status(thm)], ['41', '42'])).
% 0.58/0.77  thf(t113_zfmisc_1, axiom,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.58/0.77       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.58/0.77  thf('44', plain,
% 0.58/0.77      (![X1 : $i, X2 : $i]:
% 0.58/0.77         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X1) != (k1_xboole_0)))),
% 0.58/0.77      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.58/0.77  thf('45', plain,
% 0.58/0.77      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.58/0.77      inference('simplify', [status(thm)], ['44'])).
% 0.58/0.77  thf('46', plain,
% 0.58/0.77      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.58/0.77         <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.77      inference('demod', [status(thm)], ['43', '45'])).
% 0.58/0.77  thf('47', plain,
% 0.58/0.77      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.58/0.77      inference('simplify', [status(thm)], ['44'])).
% 0.58/0.77  thf('48', plain,
% 0.58/0.77      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.58/0.77         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 0.58/0.77          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.58/0.77      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.58/0.77  thf('49', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.58/0.77          | ((k1_relset_1 @ k1_xboole_0 @ X0 @ X1) = (k1_relat_1 @ X1)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['47', '48'])).
% 0.58/0.77  thf('50', plain,
% 0.58/0.77      ((![X0 : $i]:
% 0.58/0.77          ((k1_relset_1 @ k1_xboole_0 @ X0 @ sk_D) = (k1_relat_1 @ sk_D)))
% 0.58/0.77         <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.77      inference('sup-', [status(thm)], ['46', '49'])).
% 0.58/0.77  thf('51', plain,
% 0.58/0.77      (((~ (zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 0.58/0.77         | ((k1_xboole_0) = (k1_relat_1 @ sk_D))))
% 0.58/0.77         <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.77      inference('demod', [status(thm)], ['40', '50'])).
% 0.58/0.77  thf('52', plain,
% 0.58/0.77      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.58/0.77         <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.77      inference('demod', [status(thm)], ['43', '45'])).
% 0.58/0.77  thf('53', plain,
% 0.58/0.77      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.58/0.77      inference('simplify', [status(thm)], ['44'])).
% 0.58/0.77  thf('54', plain,
% 0.58/0.77      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.58/0.77         (~ (zip_tseitin_0 @ X25 @ X26)
% 0.58/0.77          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 0.58/0.77          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.58/0.77  thf('55', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.58/0.77          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0)
% 0.58/0.77          | ~ (zip_tseitin_0 @ X0 @ k1_xboole_0))),
% 0.58/0.77      inference('sup-', [status(thm)], ['53', '54'])).
% 0.58/0.77  thf('56', plain,
% 0.58/0.77      (![X20 : $i, X21 : $i]:
% 0.58/0.77         ((zip_tseitin_0 @ X20 @ X21) | ((X21) != (k1_xboole_0)))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.58/0.77  thf('57', plain, (![X20 : $i]: (zip_tseitin_0 @ X20 @ k1_xboole_0)),
% 0.58/0.77      inference('simplify', [status(thm)], ['56'])).
% 0.58/0.77  thf('58', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.58/0.77          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0))),
% 0.58/0.77      inference('demod', [status(thm)], ['55', '57'])).
% 0.58/0.77  thf('59', plain,
% 0.58/0.77      ((![X0 : $i]: (zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0))
% 0.58/0.77         <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.77      inference('sup-', [status(thm)], ['52', '58'])).
% 0.58/0.77  thf('60', plain,
% 0.58/0.77      ((((k1_xboole_0) = (k1_relat_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.77      inference('demod', [status(thm)], ['51', '59'])).
% 0.58/0.77  thf('61', plain,
% 0.58/0.77      (![X7 : $i, X8 : $i]:
% 0.58/0.77         (~ (r1_tarski @ X7 @ (k1_relat_1 @ X8))
% 0.58/0.77          | (r1_tarski @ X7 @ (k10_relat_1 @ X8 @ (k9_relat_1 @ X8 @ X7)))
% 0.58/0.77          | ~ (v1_relat_1 @ X8))),
% 0.58/0.77      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.58/0.77  thf('62', plain,
% 0.58/0.77      ((![X0 : $i]:
% 0.58/0.77          (~ (r1_tarski @ X0 @ k1_xboole_0)
% 0.58/0.77           | ~ (v1_relat_1 @ sk_D)
% 0.58/0.77           | (r1_tarski @ X0 @ (k10_relat_1 @ sk_D @ (k9_relat_1 @ sk_D @ X0)))))
% 0.58/0.77         <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.77      inference('sup-', [status(thm)], ['60', '61'])).
% 0.58/0.77  thf('63', plain, ((v1_relat_1 @ sk_D)),
% 0.58/0.77      inference('demod', [status(thm)], ['27', '28'])).
% 0.58/0.77  thf('64', plain,
% 0.58/0.77      ((![X0 : $i]:
% 0.58/0.77          (~ (r1_tarski @ X0 @ k1_xboole_0)
% 0.58/0.77           | (r1_tarski @ X0 @ (k10_relat_1 @ sk_D @ (k9_relat_1 @ sk_D @ X0)))))
% 0.58/0.77         <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.77      inference('demod', [status(thm)], ['62', '63'])).
% 0.58/0.77  thf('65', plain,
% 0.58/0.77      (((r1_tarski @ sk_C @ (k10_relat_1 @ sk_D @ (k9_relat_1 @ sk_D @ sk_C))))
% 0.58/0.77         <= ((((sk_A) = (k1_xboole_0))))),
% 0.58/0.77      inference('sup-', [status(thm)], ['35', '64'])).
% 0.58/0.78  thf('66', plain,
% 0.58/0.78      (~ (r1_tarski @ sk_C @ (k10_relat_1 @ sk_D @ (k9_relat_1 @ sk_D @ sk_C)))),
% 0.58/0.78      inference('demod', [status(thm)], ['4', '7'])).
% 0.58/0.78  thf('67', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['65', '66'])).
% 0.58/0.78  thf('68', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.58/0.78      inference('split', [status(esa)], ['31'])).
% 0.58/0.78  thf('69', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.58/0.78      inference('sat_resolution*', [status(thm)], ['67', '68'])).
% 0.58/0.78  thf('70', plain, (((sk_B) != (k1_xboole_0))),
% 0.58/0.78      inference('simpl_trail', [status(thm)], ['32', '69'])).
% 0.58/0.78  thf('71', plain,
% 0.58/0.78      (![X0 : $i]:
% 0.58/0.78         (~ (r1_tarski @ X0 @ sk_A)
% 0.58/0.78          | (r1_tarski @ X0 @ (k10_relat_1 @ sk_D @ (k9_relat_1 @ sk_D @ X0))))),
% 0.58/0.78      inference('simplify_reflect-', [status(thm)], ['30', '70'])).
% 0.58/0.78  thf('72', plain,
% 0.58/0.78      ((r1_tarski @ sk_C @ (k10_relat_1 @ sk_D @ (k9_relat_1 @ sk_D @ sk_C)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['9', '71'])).
% 0.58/0.78  thf('73', plain, ($false), inference('demod', [status(thm)], ['8', '72'])).
% 0.58/0.78  
% 0.58/0.78  % SZS output end Refutation
% 0.58/0.78  
% 0.58/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
