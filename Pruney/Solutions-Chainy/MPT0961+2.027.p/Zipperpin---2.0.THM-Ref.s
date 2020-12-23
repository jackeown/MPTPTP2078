%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AyBidd5wzL

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:42 EST 2020

% Result     : Theorem 1.20s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 301 expanded)
%              Number of leaves         :   33 ( 103 expanded)
%              Depth                    :   18
%              Number of atoms          :  914 (2508 expanded)
%              Number of equality atoms :   60 ( 133 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('2',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X5 ) @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('4',plain,(
    ! [X4: $i] :
      ( ( k2_subset_1 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('5',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_relset_1 @ X14 @ X15 @ X13 )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      = ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','7'])).

thf('9',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('12',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      = ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(fc10_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('17',plain,(
    ! [X9: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X9 ) )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc10_relat_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('24',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','25'])).

thf('27',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('28',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','28'])).

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

thf(zf_stmt_0,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('30',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( X21
       != ( k1_relset_1 @ X21 @ X22 @ X23 ) )
      | ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ~ ( zip_tseitin_1 @ X23 @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('34',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_4,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('35',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( zip_tseitin_0 @ X24 @ X25 )
      | ( zip_tseitin_1 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 )
      | ( X20 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('38',plain,(
    ! [X19: $i] :
      ( zip_tseitin_0 @ X19 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['36','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['32','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ X0 @ k1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t3_funct_2,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf(zf_stmt_5,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ( v1_funct_1 @ A )
          & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
          & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t3_funct_2])).

thf('44',plain,
    ( ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('45',plain,
    ( ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
   <= ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['44'])).

thf('46',plain,
    ( ( ~ ( v1_funct_2 @ sk_A @ k1_xboole_0 @ ( k2_relat_1 @ sk_A ) )
      | ~ ( v1_xboole_0 @ sk_A ) )
   <= ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('48',plain,
    ( ~ ( v1_funct_1 @ sk_A )
   <= ~ ( v1_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['44'])).

thf('49',plain,(
    v1_funct_1 @ sk_A ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('51',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('52',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('54',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X16 ) @ X17 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X16 ) @ X18 )
      | ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,
    ( ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) )
   <= ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference(split,[status(esa)],['44'])).

thf('58',plain,
    ( ~ ( v1_relat_1 @ sk_A )
   <= ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('60',plain,(
    m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['44'])).

thf('62',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['49','60','61'])).

thf('63',plain,
    ( ~ ( v1_funct_2 @ sk_A @ k1_xboole_0 @ ( k2_relat_1 @ sk_A ) )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['46','62'])).

thf('64',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','63'])).

thf('65',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('68',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( zip_tseitin_0 @ X24 @ X25 )
      | ( zip_tseitin_1 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('72',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_relset_1 @ X14 @ X15 @ X13 )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( X21
       != ( k1_relset_1 @ X21 @ X22 @ X23 ) )
      | ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ~ ( zip_tseitin_1 @ X23 @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['70','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,
    ( ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
   <= ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['44'])).

thf('80',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['49','60','61'])).

thf('81',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['79','80'])).

thf('82',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('84',plain,
    ( ( k2_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('86',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X10 ) ) )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['84','87'])).

thf('89',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('90',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('91',plain,(
    v1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,(
    $false ),
    inference(demod,[status(thm)],['65','91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AyBidd5wzL
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:26:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 1.20/1.41  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.20/1.41  % Solved by: fo/fo7.sh
% 1.20/1.41  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.20/1.41  % done 1217 iterations in 0.958s
% 1.20/1.41  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.20/1.41  % SZS output start Refutation
% 1.20/1.41  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.20/1.41  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.20/1.41  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.20/1.41  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.20/1.41  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.20/1.41  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.20/1.41  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.20/1.41  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.20/1.41  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.20/1.41  thf(sk_A_type, type, sk_A: $i).
% 1.20/1.41  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.20/1.41  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.20/1.41  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.20/1.41  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 1.20/1.41  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.20/1.41  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.20/1.41  thf(l13_xboole_0, axiom,
% 1.20/1.41    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.20/1.41  thf('0', plain,
% 1.20/1.41      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.20/1.41      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.20/1.41  thf(t113_zfmisc_1, axiom,
% 1.20/1.41    (![A:$i,B:$i]:
% 1.20/1.41     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.20/1.41       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.20/1.41  thf('1', plain,
% 1.20/1.41      (![X2 : $i, X3 : $i]:
% 1.20/1.41         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 1.20/1.41      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.20/1.41  thf('2', plain,
% 1.20/1.41      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 1.20/1.41      inference('simplify', [status(thm)], ['1'])).
% 1.20/1.41  thf(dt_k2_subset_1, axiom,
% 1.20/1.41    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 1.20/1.41  thf('3', plain,
% 1.20/1.41      (![X5 : $i]: (m1_subset_1 @ (k2_subset_1 @ X5) @ (k1_zfmisc_1 @ X5))),
% 1.20/1.41      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 1.20/1.41  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 1.20/1.41  thf('4', plain, (![X4 : $i]: ((k2_subset_1 @ X4) = (X4))),
% 1.20/1.41      inference('cnf', [status(esa)], [d4_subset_1])).
% 1.20/1.41  thf('5', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 1.20/1.41      inference('demod', [status(thm)], ['3', '4'])).
% 1.20/1.41  thf(redefinition_k1_relset_1, axiom,
% 1.20/1.41    (![A:$i,B:$i,C:$i]:
% 1.20/1.41     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.20/1.41       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.20/1.41  thf('6', plain,
% 1.20/1.41      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.20/1.41         (((k1_relset_1 @ X14 @ X15 @ X13) = (k1_relat_1 @ X13))
% 1.20/1.41          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 1.20/1.41      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.20/1.41  thf('7', plain,
% 1.20/1.41      (![X0 : $i, X1 : $i]:
% 1.20/1.41         ((k1_relset_1 @ X1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0))
% 1.20/1.41           = (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 1.20/1.41      inference('sup-', [status(thm)], ['5', '6'])).
% 1.20/1.41  thf('8', plain,
% 1.20/1.41      (![X0 : $i]:
% 1.20/1.41         ((k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)
% 1.20/1.41           = (k1_relat_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0)))),
% 1.20/1.41      inference('sup+', [status(thm)], ['2', '7'])).
% 1.20/1.41  thf('9', plain,
% 1.20/1.41      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 1.20/1.41      inference('simplify', [status(thm)], ['1'])).
% 1.20/1.41  thf('10', plain,
% 1.20/1.41      (![X0 : $i]:
% 1.20/1.41         ((k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)
% 1.20/1.41           = (k1_relat_1 @ k1_xboole_0))),
% 1.20/1.41      inference('demod', [status(thm)], ['8', '9'])).
% 1.20/1.41  thf('11', plain,
% 1.20/1.41      (![X2 : $i, X3 : $i]:
% 1.20/1.41         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 1.20/1.41      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.20/1.41  thf('12', plain,
% 1.20/1.41      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 1.20/1.41      inference('simplify', [status(thm)], ['11'])).
% 1.20/1.41  thf('13', plain,
% 1.20/1.41      (![X0 : $i, X1 : $i]:
% 1.20/1.41         ((k1_relset_1 @ X1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0))
% 1.20/1.41           = (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 1.20/1.41      inference('sup-', [status(thm)], ['5', '6'])).
% 1.20/1.41  thf('14', plain,
% 1.20/1.41      (![X0 : $i]:
% 1.20/1.41         ((k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0)
% 1.20/1.41           = (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0)))),
% 1.20/1.41      inference('sup+', [status(thm)], ['12', '13'])).
% 1.20/1.41  thf('15', plain,
% 1.20/1.41      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 1.20/1.41      inference('simplify', [status(thm)], ['11'])).
% 1.20/1.41  thf('16', plain,
% 1.20/1.41      (![X0 : $i]:
% 1.20/1.41         ((k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0)
% 1.20/1.41           = (k1_relat_1 @ k1_xboole_0))),
% 1.20/1.41      inference('demod', [status(thm)], ['14', '15'])).
% 1.20/1.41  thf(fc10_relat_1, axiom,
% 1.20/1.41    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ))).
% 1.20/1.41  thf('17', plain,
% 1.20/1.41      (![X9 : $i]: ((v1_xboole_0 @ (k1_relat_1 @ X9)) | ~ (v1_xboole_0 @ X9))),
% 1.20/1.41      inference('cnf', [status(esa)], [fc10_relat_1])).
% 1.20/1.41  thf('18', plain,
% 1.20/1.41      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.20/1.41      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.20/1.41  thf('19', plain,
% 1.20/1.41      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_relat_1 @ X0) = (k1_xboole_0)))),
% 1.20/1.41      inference('sup-', [status(thm)], ['17', '18'])).
% 1.20/1.41  thf('20', plain,
% 1.20/1.41      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.20/1.41      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.20/1.41  thf('21', plain,
% 1.20/1.41      (![X0 : $i]:
% 1.20/1.41         ((k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0)
% 1.20/1.41           = (k1_relat_1 @ k1_xboole_0))),
% 1.20/1.41      inference('demod', [status(thm)], ['14', '15'])).
% 1.20/1.41  thf('22', plain,
% 1.20/1.41      (![X0 : $i, X1 : $i]:
% 1.20/1.41         (((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))
% 1.20/1.41          | ~ (v1_xboole_0 @ X0))),
% 1.20/1.41      inference('sup+', [status(thm)], ['20', '21'])).
% 1.20/1.41  thf('23', plain,
% 1.20/1.41      (![X0 : $i, X1 : $i]:
% 1.20/1.41         (((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 1.20/1.41          | ~ (v1_xboole_0 @ k1_xboole_0)
% 1.20/1.41          | ~ (v1_xboole_0 @ X0))),
% 1.20/1.41      inference('sup+', [status(thm)], ['19', '22'])).
% 1.20/1.41  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.20/1.41  thf('24', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.20/1.41      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.20/1.41  thf('25', plain,
% 1.20/1.41      (![X0 : $i, X1 : $i]:
% 1.20/1.41         (((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 1.20/1.41          | ~ (v1_xboole_0 @ X0))),
% 1.20/1.41      inference('demod', [status(thm)], ['23', '24'])).
% 1.20/1.41  thf('26', plain,
% 1.20/1.41      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 1.20/1.41        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 1.20/1.41      inference('sup+', [status(thm)], ['16', '25'])).
% 1.20/1.41  thf('27', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.20/1.41      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.20/1.41  thf('28', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.20/1.41      inference('demod', [status(thm)], ['26', '27'])).
% 1.20/1.41  thf('29', plain,
% 1.20/1.41      (![X0 : $i]:
% 1.20/1.41         ((k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.20/1.41      inference('demod', [status(thm)], ['10', '28'])).
% 1.20/1.41  thf(d1_funct_2, axiom,
% 1.20/1.41    (![A:$i,B:$i,C:$i]:
% 1.20/1.41     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.20/1.41       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.20/1.41           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.20/1.41             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.20/1.41         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.20/1.41           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.20/1.41             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.20/1.41  thf(zf_stmt_0, axiom,
% 1.20/1.41    (![C:$i,B:$i,A:$i]:
% 1.20/1.41     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.20/1.41       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.20/1.41  thf('30', plain,
% 1.20/1.41      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.20/1.41         (((X21) != (k1_relset_1 @ X21 @ X22 @ X23))
% 1.20/1.41          | (v1_funct_2 @ X23 @ X21 @ X22)
% 1.20/1.41          | ~ (zip_tseitin_1 @ X23 @ X22 @ X21))),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.41  thf('31', plain,
% 1.20/1.41      (![X0 : $i]:
% 1.20/1.41         (((k1_xboole_0) != (k1_xboole_0))
% 1.20/1.41          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)
% 1.20/1.41          | (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0))),
% 1.20/1.41      inference('sup-', [status(thm)], ['29', '30'])).
% 1.20/1.41  thf('32', plain,
% 1.20/1.41      (![X0 : $i]:
% 1.20/1.41         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 1.20/1.41          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 1.20/1.41      inference('simplify', [status(thm)], ['31'])).
% 1.20/1.41  thf('33', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 1.20/1.41      inference('demod', [status(thm)], ['3', '4'])).
% 1.20/1.41  thf('34', plain,
% 1.20/1.41      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 1.20/1.41      inference('simplify', [status(thm)], ['1'])).
% 1.20/1.41  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.20/1.41  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $o).
% 1.20/1.41  thf(zf_stmt_3, axiom,
% 1.20/1.41    (![B:$i,A:$i]:
% 1.20/1.41     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.20/1.41       ( zip_tseitin_0 @ B @ A ) ))).
% 1.20/1.41  thf(zf_stmt_4, axiom,
% 1.20/1.41    (![A:$i,B:$i,C:$i]:
% 1.20/1.41     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.20/1.41       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.20/1.41         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.20/1.41           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.20/1.41             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.20/1.41  thf('35', plain,
% 1.20/1.41      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.20/1.41         (~ (zip_tseitin_0 @ X24 @ X25)
% 1.20/1.41          | (zip_tseitin_1 @ X26 @ X24 @ X25)
% 1.20/1.41          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24))))),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.20/1.41  thf('36', plain,
% 1.20/1.41      (![X0 : $i, X1 : $i]:
% 1.20/1.41         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.20/1.41          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0)
% 1.20/1.41          | ~ (zip_tseitin_0 @ X0 @ k1_xboole_0))),
% 1.20/1.41      inference('sup-', [status(thm)], ['34', '35'])).
% 1.20/1.41  thf('37', plain,
% 1.20/1.41      (![X19 : $i, X20 : $i]:
% 1.20/1.41         ((zip_tseitin_0 @ X19 @ X20) | ((X20) != (k1_xboole_0)))),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.20/1.41  thf('38', plain, (![X19 : $i]: (zip_tseitin_0 @ X19 @ k1_xboole_0)),
% 1.20/1.41      inference('simplify', [status(thm)], ['37'])).
% 1.20/1.41  thf('39', plain,
% 1.20/1.41      (![X0 : $i, X1 : $i]:
% 1.20/1.41         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.20/1.41          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0))),
% 1.20/1.41      inference('demod', [status(thm)], ['36', '38'])).
% 1.20/1.41  thf('40', plain,
% 1.20/1.41      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.20/1.41      inference('sup-', [status(thm)], ['33', '39'])).
% 1.20/1.41  thf('41', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.20/1.41      inference('demod', [status(thm)], ['32', '40'])).
% 1.20/1.41  thf('42', plain,
% 1.20/1.41      (![X0 : $i, X1 : $i]:
% 1.20/1.41         ((v1_funct_2 @ X0 @ k1_xboole_0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.20/1.41      inference('sup+', [status(thm)], ['0', '41'])).
% 1.20/1.41  thf('43', plain,
% 1.20/1.41      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_relat_1 @ X0) = (k1_xboole_0)))),
% 1.20/1.41      inference('sup-', [status(thm)], ['17', '18'])).
% 1.20/1.41  thf(t3_funct_2, conjecture,
% 1.20/1.41    (![A:$i]:
% 1.20/1.41     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.20/1.41       ( ( v1_funct_1 @ A ) & 
% 1.20/1.41         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 1.20/1.41         ( m1_subset_1 @
% 1.20/1.41           A @ 
% 1.20/1.41           ( k1_zfmisc_1 @
% 1.20/1.41             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.20/1.41  thf(zf_stmt_5, negated_conjecture,
% 1.20/1.41    (~( ![A:$i]:
% 1.20/1.41        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.20/1.41          ( ( v1_funct_1 @ A ) & 
% 1.20/1.41            ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 1.20/1.41            ( m1_subset_1 @
% 1.20/1.41              A @ 
% 1.20/1.41              ( k1_zfmisc_1 @
% 1.20/1.41                ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )),
% 1.20/1.41    inference('cnf.neg', [status(esa)], [t3_funct_2])).
% 1.20/1.41  thf('44', plain,
% 1.20/1.41      ((~ (v1_funct_1 @ sk_A)
% 1.20/1.41        | ~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 1.20/1.41        | ~ (m1_subset_1 @ sk_A @ 
% 1.20/1.41             (k1_zfmisc_1 @ 
% 1.20/1.41              (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.20/1.41  thf('45', plain,
% 1.20/1.41      ((~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))
% 1.20/1.41         <= (~
% 1.20/1.41             ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))),
% 1.20/1.41      inference('split', [status(esa)], ['44'])).
% 1.20/1.41  thf('46', plain,
% 1.20/1.41      (((~ (v1_funct_2 @ sk_A @ k1_xboole_0 @ (k2_relat_1 @ sk_A))
% 1.20/1.41         | ~ (v1_xboole_0 @ sk_A)))
% 1.20/1.41         <= (~
% 1.20/1.41             ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))),
% 1.20/1.41      inference('sup-', [status(thm)], ['43', '45'])).
% 1.20/1.41  thf('47', plain, ((v1_funct_1 @ sk_A)),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.20/1.41  thf('48', plain, ((~ (v1_funct_1 @ sk_A)) <= (~ ((v1_funct_1 @ sk_A)))),
% 1.20/1.41      inference('split', [status(esa)], ['44'])).
% 1.20/1.41  thf('49', plain, (((v1_funct_1 @ sk_A))),
% 1.20/1.41      inference('sup-', [status(thm)], ['47', '48'])).
% 1.20/1.41  thf('50', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 1.20/1.41      inference('demod', [status(thm)], ['3', '4'])).
% 1.20/1.41  thf(t3_subset, axiom,
% 1.20/1.41    (![A:$i,B:$i]:
% 1.20/1.41     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.20/1.41  thf('51', plain,
% 1.20/1.41      (![X6 : $i, X7 : $i]:
% 1.20/1.41         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 1.20/1.41      inference('cnf', [status(esa)], [t3_subset])).
% 1.20/1.41  thf('52', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.20/1.41      inference('sup-', [status(thm)], ['50', '51'])).
% 1.20/1.41  thf('53', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.20/1.41      inference('sup-', [status(thm)], ['50', '51'])).
% 1.20/1.41  thf(t11_relset_1, axiom,
% 1.20/1.41    (![A:$i,B:$i,C:$i]:
% 1.20/1.41     ( ( v1_relat_1 @ C ) =>
% 1.20/1.41       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 1.20/1.41           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 1.20/1.41         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 1.20/1.41  thf('54', plain,
% 1.20/1.41      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.20/1.41         (~ (r1_tarski @ (k1_relat_1 @ X16) @ X17)
% 1.20/1.41          | ~ (r1_tarski @ (k2_relat_1 @ X16) @ X18)
% 1.20/1.41          | (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 1.20/1.41          | ~ (v1_relat_1 @ X16))),
% 1.20/1.41      inference('cnf', [status(esa)], [t11_relset_1])).
% 1.20/1.41  thf('55', plain,
% 1.20/1.41      (![X0 : $i, X1 : $i]:
% 1.20/1.41         (~ (v1_relat_1 @ X0)
% 1.20/1.41          | (m1_subset_1 @ X0 @ 
% 1.20/1.41             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 1.20/1.41          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 1.20/1.41      inference('sup-', [status(thm)], ['53', '54'])).
% 1.20/1.41  thf('56', plain,
% 1.20/1.41      (![X0 : $i]:
% 1.20/1.41         ((m1_subset_1 @ X0 @ 
% 1.20/1.41           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 1.20/1.41          | ~ (v1_relat_1 @ X0))),
% 1.20/1.41      inference('sup-', [status(thm)], ['52', '55'])).
% 1.20/1.41  thf('57', plain,
% 1.20/1.41      ((~ (m1_subset_1 @ sk_A @ 
% 1.20/1.41           (k1_zfmisc_1 @ 
% 1.20/1.41            (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))
% 1.20/1.41         <= (~
% 1.20/1.41             ((m1_subset_1 @ sk_A @ 
% 1.20/1.41               (k1_zfmisc_1 @ 
% 1.20/1.41                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 1.20/1.41      inference('split', [status(esa)], ['44'])).
% 1.20/1.41  thf('58', plain,
% 1.20/1.41      ((~ (v1_relat_1 @ sk_A))
% 1.20/1.41         <= (~
% 1.20/1.41             ((m1_subset_1 @ sk_A @ 
% 1.20/1.41               (k1_zfmisc_1 @ 
% 1.20/1.41                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 1.20/1.41      inference('sup-', [status(thm)], ['56', '57'])).
% 1.20/1.41  thf('59', plain, ((v1_relat_1 @ sk_A)),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.20/1.41  thf('60', plain,
% 1.20/1.41      (((m1_subset_1 @ sk_A @ 
% 1.20/1.41         (k1_zfmisc_1 @ 
% 1.20/1.41          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 1.20/1.41      inference('demod', [status(thm)], ['58', '59'])).
% 1.20/1.41  thf('61', plain,
% 1.20/1.41      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))) | 
% 1.20/1.41       ~
% 1.20/1.41       ((m1_subset_1 @ sk_A @ 
% 1.20/1.41         (k1_zfmisc_1 @ 
% 1.20/1.41          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))) | 
% 1.20/1.41       ~ ((v1_funct_1 @ sk_A))),
% 1.20/1.41      inference('split', [status(esa)], ['44'])).
% 1.20/1.41  thf('62', plain,
% 1.20/1.41      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))),
% 1.20/1.41      inference('sat_resolution*', [status(thm)], ['49', '60', '61'])).
% 1.20/1.41  thf('63', plain,
% 1.20/1.41      ((~ (v1_funct_2 @ sk_A @ k1_xboole_0 @ (k2_relat_1 @ sk_A))
% 1.20/1.41        | ~ (v1_xboole_0 @ sk_A))),
% 1.20/1.41      inference('simpl_trail', [status(thm)], ['46', '62'])).
% 1.20/1.41  thf('64', plain, ((~ (v1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ sk_A))),
% 1.20/1.41      inference('sup-', [status(thm)], ['42', '63'])).
% 1.20/1.41  thf('65', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.20/1.41      inference('simplify', [status(thm)], ['64'])).
% 1.20/1.41  thf('66', plain,
% 1.20/1.41      (![X19 : $i, X20 : $i]:
% 1.20/1.41         ((zip_tseitin_0 @ X19 @ X20) | ((X19) = (k1_xboole_0)))),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.20/1.41  thf('67', plain,
% 1.20/1.41      (![X0 : $i]:
% 1.20/1.41         ((m1_subset_1 @ X0 @ 
% 1.20/1.41           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 1.20/1.41          | ~ (v1_relat_1 @ X0))),
% 1.20/1.41      inference('sup-', [status(thm)], ['52', '55'])).
% 1.20/1.41  thf('68', plain,
% 1.20/1.41      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.20/1.41         (~ (zip_tseitin_0 @ X24 @ X25)
% 1.20/1.41          | (zip_tseitin_1 @ X26 @ X24 @ X25)
% 1.20/1.41          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24))))),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.20/1.41  thf('69', plain,
% 1.20/1.41      (![X0 : $i]:
% 1.20/1.41         (~ (v1_relat_1 @ X0)
% 1.20/1.41          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 1.20/1.41          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 1.20/1.41      inference('sup-', [status(thm)], ['67', '68'])).
% 1.20/1.41  thf('70', plain,
% 1.20/1.41      (![X0 : $i]:
% 1.20/1.41         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 1.20/1.41          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 1.20/1.41          | ~ (v1_relat_1 @ X0))),
% 1.20/1.41      inference('sup-', [status(thm)], ['66', '69'])).
% 1.20/1.41  thf('71', plain,
% 1.20/1.41      (![X0 : $i]:
% 1.20/1.41         ((m1_subset_1 @ X0 @ 
% 1.20/1.41           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 1.20/1.41          | ~ (v1_relat_1 @ X0))),
% 1.20/1.41      inference('sup-', [status(thm)], ['52', '55'])).
% 1.20/1.41  thf('72', plain,
% 1.20/1.41      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.20/1.41         (((k1_relset_1 @ X14 @ X15 @ X13) = (k1_relat_1 @ X13))
% 1.20/1.41          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 1.20/1.41      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.20/1.41  thf('73', plain,
% 1.20/1.41      (![X0 : $i]:
% 1.20/1.41         (~ (v1_relat_1 @ X0)
% 1.20/1.41          | ((k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 1.20/1.41              = (k1_relat_1 @ X0)))),
% 1.20/1.41      inference('sup-', [status(thm)], ['71', '72'])).
% 1.20/1.41  thf('74', plain,
% 1.20/1.41      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.20/1.41         (((X21) != (k1_relset_1 @ X21 @ X22 @ X23))
% 1.20/1.41          | (v1_funct_2 @ X23 @ X21 @ X22)
% 1.20/1.41          | ~ (zip_tseitin_1 @ X23 @ X22 @ X21))),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.41  thf('75', plain,
% 1.20/1.41      (![X0 : $i]:
% 1.20/1.41         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 1.20/1.41          | ~ (v1_relat_1 @ X0)
% 1.20/1.41          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 1.20/1.41          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 1.20/1.41      inference('sup-', [status(thm)], ['73', '74'])).
% 1.20/1.41  thf('76', plain,
% 1.20/1.41      (![X0 : $i]:
% 1.20/1.41         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 1.20/1.41          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 1.20/1.41          | ~ (v1_relat_1 @ X0))),
% 1.20/1.41      inference('simplify', [status(thm)], ['75'])).
% 1.20/1.41  thf('77', plain,
% 1.20/1.41      (![X0 : $i]:
% 1.20/1.41         (~ (v1_relat_1 @ X0)
% 1.20/1.41          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 1.20/1.41          | ~ (v1_relat_1 @ X0)
% 1.20/1.41          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 1.20/1.41      inference('sup-', [status(thm)], ['70', '76'])).
% 1.20/1.41  thf('78', plain,
% 1.20/1.41      (![X0 : $i]:
% 1.20/1.41         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 1.20/1.41          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 1.20/1.41          | ~ (v1_relat_1 @ X0))),
% 1.20/1.41      inference('simplify', [status(thm)], ['77'])).
% 1.20/1.41  thf('79', plain,
% 1.20/1.41      ((~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))
% 1.20/1.41         <= (~
% 1.20/1.41             ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))),
% 1.20/1.41      inference('split', [status(esa)], ['44'])).
% 1.20/1.41  thf('80', plain,
% 1.20/1.41      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))),
% 1.20/1.41      inference('sat_resolution*', [status(thm)], ['49', '60', '61'])).
% 1.20/1.41  thf('81', plain,
% 1.20/1.41      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 1.20/1.41      inference('simpl_trail', [status(thm)], ['79', '80'])).
% 1.20/1.41  thf('82', plain,
% 1.20/1.41      ((~ (v1_relat_1 @ sk_A) | ((k2_relat_1 @ sk_A) = (k1_xboole_0)))),
% 1.20/1.41      inference('sup-', [status(thm)], ['78', '81'])).
% 1.20/1.41  thf('83', plain, ((v1_relat_1 @ sk_A)),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.20/1.41  thf('84', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 1.20/1.41      inference('demod', [status(thm)], ['82', '83'])).
% 1.20/1.41  thf('85', plain,
% 1.20/1.41      (![X0 : $i]:
% 1.20/1.41         ((m1_subset_1 @ X0 @ 
% 1.20/1.41           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 1.20/1.41          | ~ (v1_relat_1 @ X0))),
% 1.20/1.41      inference('sup-', [status(thm)], ['52', '55'])).
% 1.20/1.41  thf(cc4_relset_1, axiom,
% 1.20/1.41    (![A:$i,B:$i]:
% 1.20/1.41     ( ( v1_xboole_0 @ A ) =>
% 1.20/1.41       ( ![C:$i]:
% 1.20/1.41         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 1.20/1.41           ( v1_xboole_0 @ C ) ) ) ))).
% 1.20/1.41  thf('86', plain,
% 1.20/1.41      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.20/1.41         (~ (v1_xboole_0 @ X10)
% 1.20/1.41          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X10)))
% 1.20/1.41          | (v1_xboole_0 @ X11))),
% 1.20/1.41      inference('cnf', [status(esa)], [cc4_relset_1])).
% 1.20/1.41  thf('87', plain,
% 1.20/1.41      (![X0 : $i]:
% 1.20/1.41         (~ (v1_relat_1 @ X0)
% 1.20/1.41          | (v1_xboole_0 @ X0)
% 1.20/1.41          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0)))),
% 1.20/1.41      inference('sup-', [status(thm)], ['85', '86'])).
% 1.20/1.41  thf('88', plain,
% 1.20/1.41      ((~ (v1_xboole_0 @ k1_xboole_0)
% 1.20/1.41        | (v1_xboole_0 @ sk_A)
% 1.20/1.41        | ~ (v1_relat_1 @ sk_A))),
% 1.20/1.41      inference('sup-', [status(thm)], ['84', '87'])).
% 1.20/1.41  thf('89', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.20/1.41      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.20/1.41  thf('90', plain, ((v1_relat_1 @ sk_A)),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.20/1.41  thf('91', plain, ((v1_xboole_0 @ sk_A)),
% 1.20/1.41      inference('demod', [status(thm)], ['88', '89', '90'])).
% 1.20/1.41  thf('92', plain, ($false), inference('demod', [status(thm)], ['65', '91'])).
% 1.20/1.41  
% 1.20/1.41  % SZS output end Refutation
% 1.20/1.41  
% 1.20/1.42  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
