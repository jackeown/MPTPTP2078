%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vyxd2ns4Zg

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:49 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :  158 (1099 expanded)
%              Number of leaves         :   39 ( 332 expanded)
%              Depth                    :   24
%              Number of atoms          : 1188 (11169 expanded)
%              Number of equality atoms :   97 ( 576 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t4_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
         => ( ( v1_funct_1 @ B )
            & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t4_funct_2])).

thf('0',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('3',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X23 ) @ X24 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X23 ) @ X25 )
      | ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('6',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('8',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_partfun1 @ X26 @ X27 )
      | ( v1_funct_2 @ X26 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('9',plain,
    ( ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( v1_partfun1 @ sk_B @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( v1_partfun1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ~ ( v1_funct_1 @ sk_B )
   <= ~ ( v1_funct_1 @ sk_B ) ),
    inference(split,[status(esa)],['12'])).

thf('16',plain,(
    v1_funct_1 @ sk_B ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('18',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['12'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference(split,[status(esa)],['12'])).

thf('21',plain,(
    ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['16','19','20'])).

thf('22',plain,(
    ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['13','21'])).

thf('23',plain,(
    ~ ( v1_partfun1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['11','22'])).

thf(t194_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ B ) )).

thf('24',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) @ X14 ) ),
    inference(cnf,[status(esa)],[t194_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('27',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('29',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t117_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) )
          | ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) )
        & ~ ( r1_tarski @ B @ C ) ) )).

thf('31',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X4 @ X3 ) @ ( k2_zfmisc_1 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t193_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ A ) )).

thf('33',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) @ X11 ) ),
    inference(cnf,[status(esa)],[t193_relat_1])).

thf('34',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1
        = ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('37',plain,(
    ! [X18: $i] :
      ( ( ( k1_relat_1 @ X18 )
       != k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X1: $i] :
      ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ X1 )
        = k1_xboole_0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) @ X14 ) ),
    inference(cnf,[status(esa)],[t194_relat_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X1: $i] :
      ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ X1 )
        = k1_xboole_0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1
        = ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['47'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('49',plain,(
    ! [X19: $i] :
      ( ( ( k1_relat_1 @ X19 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X19 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('50',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X1: $i] :
      ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ X1 )
        = k1_xboole_0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('53',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('56',plain,
    ( ( v1_relat_1 @ k1_xboole_0 )
    | ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['43','58'])).

thf('60',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('62',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) )
    | ( sk_A
      = ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

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

thf('63',plain,(
    ! [X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('64',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

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

thf('65',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( zip_tseitin_0 @ X37 @ X38 )
      | ( zip_tseitin_1 @ X39 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('66',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('68',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('69',plain,
    ( ( k1_relset_1 @ ( k1_relat_1 @ sk_B ) @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( X34
       != ( k1_relset_1 @ X34 @ X35 @ X36 ) )
      | ( v1_funct_2 @ X36 @ X34 @ X35 )
      | ~ ( zip_tseitin_1 @ X36 @ X35 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('71',plain,
    ( ( ( k1_relat_1 @ sk_B )
     != ( k1_relat_1 @ sk_B ) )
    | ~ ( zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['13','21'])).

thf('74',plain,(
    ~ ( zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['66','74'])).

thf('76',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['63','75'])).

thf('77',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['63','75'])).

thf('78',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_relat_1 @ sk_B ) )
    | ( k1_xboole_0
      = ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['62','76','77'])).

thf('79',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = k1_xboole_0 )
    | ( k1_xboole_0
      = ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['59','78'])).

thf('80',plain,
    ( ( k2_relat_1 @ sk_B )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X18: $i] :
      ( ( ( k2_relat_1 @ X18 )
       != k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('82',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['84'])).

thf('87',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['47'])).

thf('88',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','57'])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('89',plain,(
    ! [X15: $i] :
      ( ( r1_tarski @ X15 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X15 ) @ ( k2_relat_1 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('90',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( r1_tarski @ ( k2_relat_1 @ X17 ) @ ( k2_relat_1 @ X16 ) )
      | ~ ( r1_tarski @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) @ X14 ) ),
    inference(cnf,[status(esa)],[t194_relat_1])).

thf('96',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['94','97'])).

thf('99',plain,(
    ! [X18: $i] :
      ( ( ( k2_relat_1 @ X18 )
       != k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k2_relat_1 @ k1_xboole_0 ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['88','102'])).

thf('104',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['47'])).

thf('105',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','57'])).

thf('106',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['56'])).

thf('107',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['103','104','105','106'])).

thf('108',plain,
    ( ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('110',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('111',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf(cc1_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_partfun1 @ C @ A ) ) ) )).

thf('112',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_xboole_0 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X31 ) ) )
      | ( v1_partfun1 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[cc1_partfun1])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_partfun1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['108','113'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('115',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('116',plain,(
    v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    $false ),
    inference(demod,[status(thm)],['23','85','86','87','116'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vyxd2ns4Zg
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:13:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.54/0.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.54/0.73  % Solved by: fo/fo7.sh
% 0.54/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.73  % done 271 iterations in 0.285s
% 0.54/0.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.54/0.73  % SZS output start Refutation
% 0.54/0.73  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.54/0.73  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.54/0.73  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.54/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.54/0.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.54/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.54/0.73  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.54/0.73  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.54/0.73  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.54/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.73  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.54/0.73  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.54/0.73  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.54/0.73  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.54/0.73  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.54/0.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.54/0.73  thf(t4_funct_2, conjecture,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.54/0.73       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.54/0.73         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.54/0.73           ( m1_subset_1 @
% 0.54/0.73             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.54/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.73    (~( ![A:$i,B:$i]:
% 0.54/0.73        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.54/0.73          ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.54/0.73            ( ( v1_funct_1 @ B ) & 
% 0.54/0.73              ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.54/0.73              ( m1_subset_1 @
% 0.54/0.73                B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )),
% 0.54/0.73    inference('cnf.neg', [status(esa)], [t4_funct_2])).
% 0.54/0.73  thf('0', plain, ((r1_tarski @ (k2_relat_1 @ sk_B) @ sk_A)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf(d10_xboole_0, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.54/0.73  thf('1', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.54/0.73      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.54/0.73  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.54/0.73      inference('simplify', [status(thm)], ['1'])).
% 0.54/0.73  thf(t11_relset_1, axiom,
% 0.54/0.73    (![A:$i,B:$i,C:$i]:
% 0.54/0.73     ( ( v1_relat_1 @ C ) =>
% 0.54/0.73       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.54/0.73           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.54/0.73         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.54/0.73  thf('3', plain,
% 0.54/0.73      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.54/0.73         (~ (r1_tarski @ (k1_relat_1 @ X23) @ X24)
% 0.54/0.73          | ~ (r1_tarski @ (k2_relat_1 @ X23) @ X25)
% 0.54/0.73          | (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.54/0.73          | ~ (v1_relat_1 @ X23))),
% 0.54/0.73      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.54/0.73  thf('4', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         (~ (v1_relat_1 @ X0)
% 0.54/0.73          | (m1_subset_1 @ X0 @ 
% 0.54/0.73             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.54/0.73          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.54/0.73      inference('sup-', [status(thm)], ['2', '3'])).
% 0.54/0.73  thf('5', plain,
% 0.54/0.73      (((m1_subset_1 @ sk_B @ 
% 0.54/0.73         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))
% 0.54/0.73        | ~ (v1_relat_1 @ sk_B))),
% 0.54/0.73      inference('sup-', [status(thm)], ['0', '4'])).
% 0.54/0.73  thf('6', plain, ((v1_relat_1 @ sk_B)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('7', plain,
% 0.54/0.73      ((m1_subset_1 @ sk_B @ 
% 0.54/0.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.54/0.73      inference('demod', [status(thm)], ['5', '6'])).
% 0.54/0.73  thf(cc1_funct_2, axiom,
% 0.54/0.73    (![A:$i,B:$i,C:$i]:
% 0.54/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.73       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 0.54/0.73         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 0.54/0.73  thf('8', plain,
% 0.54/0.73      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.54/0.73         (~ (v1_funct_1 @ X26)
% 0.54/0.73          | ~ (v1_partfun1 @ X26 @ X27)
% 0.54/0.73          | (v1_funct_2 @ X26 @ X27 @ X28)
% 0.54/0.73          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.54/0.73      inference('cnf', [status(esa)], [cc1_funct_2])).
% 0.54/0.73  thf('9', plain,
% 0.54/0.73      (((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.54/0.73        | ~ (v1_partfun1 @ sk_B @ (k1_relat_1 @ sk_B))
% 0.54/0.73        | ~ (v1_funct_1 @ sk_B))),
% 0.54/0.73      inference('sup-', [status(thm)], ['7', '8'])).
% 0.54/0.73  thf('10', plain, ((v1_funct_1 @ sk_B)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('11', plain,
% 0.54/0.73      (((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.54/0.73        | ~ (v1_partfun1 @ sk_B @ (k1_relat_1 @ sk_B)))),
% 0.54/0.73      inference('demod', [status(thm)], ['9', '10'])).
% 0.54/0.73  thf('12', plain,
% 0.54/0.73      ((~ (v1_funct_1 @ sk_B)
% 0.54/0.73        | ~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.54/0.73        | ~ (m1_subset_1 @ sk_B @ 
% 0.54/0.73             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('13', plain,
% 0.54/0.73      ((~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.54/0.73         <= (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.54/0.73      inference('split', [status(esa)], ['12'])).
% 0.54/0.73  thf('14', plain, ((v1_funct_1 @ sk_B)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('15', plain, ((~ (v1_funct_1 @ sk_B)) <= (~ ((v1_funct_1 @ sk_B)))),
% 0.54/0.73      inference('split', [status(esa)], ['12'])).
% 0.54/0.73  thf('16', plain, (((v1_funct_1 @ sk_B))),
% 0.54/0.73      inference('sup-', [status(thm)], ['14', '15'])).
% 0.54/0.73  thf('17', plain,
% 0.54/0.73      ((m1_subset_1 @ sk_B @ 
% 0.54/0.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.54/0.73      inference('demod', [status(thm)], ['5', '6'])).
% 0.54/0.73  thf('18', plain,
% 0.54/0.73      ((~ (m1_subset_1 @ sk_B @ 
% 0.54/0.73           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))))
% 0.54/0.73         <= (~
% 0.54/0.73             ((m1_subset_1 @ sk_B @ 
% 0.54/0.73               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))))),
% 0.54/0.73      inference('split', [status(esa)], ['12'])).
% 0.54/0.73  thf('19', plain,
% 0.54/0.73      (((m1_subset_1 @ sk_B @ 
% 0.54/0.73         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))))),
% 0.54/0.73      inference('sup-', [status(thm)], ['17', '18'])).
% 0.54/0.73  thf('20', plain,
% 0.54/0.73      (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 0.54/0.73       ~
% 0.54/0.73       ((m1_subset_1 @ sk_B @ 
% 0.54/0.73         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))) | 
% 0.54/0.73       ~ ((v1_funct_1 @ sk_B))),
% 0.54/0.73      inference('split', [status(esa)], ['12'])).
% 0.54/0.73  thf('21', plain, (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.54/0.73      inference('sat_resolution*', [status(thm)], ['16', '19', '20'])).
% 0.54/0.73  thf('22', plain, (~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.54/0.73      inference('simpl_trail', [status(thm)], ['13', '21'])).
% 0.54/0.73  thf('23', plain, (~ (v1_partfun1 @ sk_B @ (k1_relat_1 @ sk_B))),
% 0.54/0.73      inference('clc', [status(thm)], ['11', '22'])).
% 0.54/0.73  thf(t194_relat_1, axiom,
% 0.54/0.73    (![A:$i,B:$i]: ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ B ))).
% 0.54/0.73  thf('24', plain,
% 0.54/0.73      (![X13 : $i, X14 : $i]:
% 0.54/0.73         (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X13 @ X14)) @ X14)),
% 0.54/0.73      inference('cnf', [status(esa)], [t194_relat_1])).
% 0.54/0.73  thf('25', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         (~ (v1_relat_1 @ X0)
% 0.54/0.73          | (m1_subset_1 @ X0 @ 
% 0.54/0.73             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.54/0.73          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.54/0.73      inference('sup-', [status(thm)], ['2', '3'])).
% 0.54/0.73  thf('26', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         ((m1_subset_1 @ (k2_zfmisc_1 @ X1 @ X0) @ 
% 0.54/0.73           (k1_zfmisc_1 @ 
% 0.54/0.73            (k2_zfmisc_1 @ (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0)))
% 0.54/0.73          | ~ (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.54/0.73      inference('sup-', [status(thm)], ['24', '25'])).
% 0.54/0.73  thf(fc6_relat_1, axiom,
% 0.54/0.73    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.54/0.73  thf('27', plain,
% 0.54/0.73      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 0.54/0.73      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.54/0.73  thf('28', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         (m1_subset_1 @ (k2_zfmisc_1 @ X1 @ X0) @ 
% 0.54/0.73          (k1_zfmisc_1 @ 
% 0.54/0.73           (k2_zfmisc_1 @ (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0)))),
% 0.54/0.73      inference('demod', [status(thm)], ['26', '27'])).
% 0.54/0.73  thf(t3_subset, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.54/0.73  thf('29', plain,
% 0.54/0.73      (![X6 : $i, X7 : $i]:
% 0.54/0.73         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.54/0.73      inference('cnf', [status(esa)], [t3_subset])).
% 0.54/0.73  thf('30', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         (r1_tarski @ (k2_zfmisc_1 @ X1 @ X0) @ 
% 0.54/0.73          (k2_zfmisc_1 @ (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0))),
% 0.54/0.73      inference('sup-', [status(thm)], ['28', '29'])).
% 0.54/0.73  thf(t117_zfmisc_1, axiom,
% 0.54/0.73    (![A:$i,B:$i,C:$i]:
% 0.54/0.73     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.54/0.73          ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) ) | 
% 0.54/0.73            ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 0.54/0.73          ( ~( r1_tarski @ B @ C ) ) ) ))).
% 0.54/0.73  thf('31', plain,
% 0.54/0.73      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.54/0.73         (((X3) = (k1_xboole_0))
% 0.54/0.73          | (r1_tarski @ X4 @ X5)
% 0.54/0.73          | ~ (r1_tarski @ (k2_zfmisc_1 @ X4 @ X3) @ (k2_zfmisc_1 @ X5 @ X3)))),
% 0.54/0.73      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 0.54/0.73  thf('32', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         ((r1_tarski @ X1 @ (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.54/0.73          | ((X0) = (k1_xboole_0)))),
% 0.54/0.73      inference('sup-', [status(thm)], ['30', '31'])).
% 0.54/0.73  thf(t193_relat_1, axiom,
% 0.54/0.73    (![A:$i,B:$i]: ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ A ))).
% 0.54/0.73  thf('33', plain,
% 0.54/0.73      (![X11 : $i, X12 : $i]:
% 0.54/0.73         (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12)) @ X11)),
% 0.54/0.73      inference('cnf', [status(esa)], [t193_relat_1])).
% 0.54/0.73  thf('34', plain,
% 0.54/0.73      (![X0 : $i, X2 : $i]:
% 0.54/0.73         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.54/0.73      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.54/0.73  thf('35', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         (~ (r1_tarski @ X0 @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 0.54/0.73          | ((X0) = (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1))))),
% 0.54/0.73      inference('sup-', [status(thm)], ['33', '34'])).
% 0.54/0.73  thf('36', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         (((X0) = (k1_xboole_0))
% 0.54/0.73          | ((X1) = (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 0.54/0.73      inference('sup-', [status(thm)], ['32', '35'])).
% 0.54/0.73  thf(t64_relat_1, axiom,
% 0.54/0.73    (![A:$i]:
% 0.54/0.73     ( ( v1_relat_1 @ A ) =>
% 0.54/0.73       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.54/0.73           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.54/0.73         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.54/0.73  thf('37', plain,
% 0.54/0.73      (![X18 : $i]:
% 0.54/0.73         (((k1_relat_1 @ X18) != (k1_xboole_0))
% 0.54/0.73          | ((X18) = (k1_xboole_0))
% 0.54/0.73          | ~ (v1_relat_1 @ X18))),
% 0.54/0.73      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.54/0.73  thf('38', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         (((X0) != (k1_xboole_0))
% 0.54/0.73          | ((X1) = (k1_xboole_0))
% 0.54/0.73          | ~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1))
% 0.54/0.73          | ((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)))),
% 0.54/0.73      inference('sup-', [status(thm)], ['36', '37'])).
% 0.54/0.73  thf('39', plain,
% 0.54/0.73      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 0.54/0.73      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.54/0.73  thf('40', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         (((X0) != (k1_xboole_0))
% 0.54/0.73          | ((X1) = (k1_xboole_0))
% 0.54/0.73          | ((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)))),
% 0.54/0.73      inference('demod', [status(thm)], ['38', '39'])).
% 0.54/0.73  thf('41', plain,
% 0.54/0.73      (![X1 : $i]:
% 0.54/0.73         (((k2_zfmisc_1 @ k1_xboole_0 @ X1) = (k1_xboole_0))
% 0.54/0.73          | ((X1) = (k1_xboole_0)))),
% 0.54/0.73      inference('simplify', [status(thm)], ['40'])).
% 0.54/0.73  thf('42', plain,
% 0.54/0.73      (![X13 : $i, X14 : $i]:
% 0.54/0.73         (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X13 @ X14)) @ X14)),
% 0.54/0.73      inference('cnf', [status(esa)], [t194_relat_1])).
% 0.54/0.73  thf('43', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         ((r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0)
% 0.54/0.73          | ((X0) = (k1_xboole_0)))),
% 0.54/0.73      inference('sup+', [status(thm)], ['41', '42'])).
% 0.54/0.73  thf('44', plain,
% 0.54/0.73      (![X1 : $i]:
% 0.54/0.73         (((k2_zfmisc_1 @ k1_xboole_0 @ X1) = (k1_xboole_0))
% 0.54/0.73          | ((X1) = (k1_xboole_0)))),
% 0.54/0.73      inference('simplify', [status(thm)], ['40'])).
% 0.54/0.73  thf('45', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         (((X0) = (k1_xboole_0))
% 0.54/0.73          | ((X1) = (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 0.54/0.73      inference('sup-', [status(thm)], ['32', '35'])).
% 0.54/0.73  thf('46', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))
% 0.54/0.73          | ((X0) = (k1_xboole_0))
% 0.54/0.73          | ((X0) = (k1_xboole_0)))),
% 0.54/0.73      inference('sup+', [status(thm)], ['44', '45'])).
% 0.54/0.73  thf('47', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         (((X0) = (k1_xboole_0)) | ((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.54/0.73      inference('simplify', [status(thm)], ['46'])).
% 0.54/0.73  thf('48', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.54/0.73      inference('condensation', [status(thm)], ['47'])).
% 0.54/0.73  thf(t65_relat_1, axiom,
% 0.54/0.73    (![A:$i]:
% 0.54/0.73     ( ( v1_relat_1 @ A ) =>
% 0.54/0.73       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.54/0.73         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.54/0.73  thf('49', plain,
% 0.54/0.73      (![X19 : $i]:
% 0.54/0.73         (((k1_relat_1 @ X19) != (k1_xboole_0))
% 0.54/0.73          | ((k2_relat_1 @ X19) = (k1_xboole_0))
% 0.54/0.73          | ~ (v1_relat_1 @ X19))),
% 0.54/0.73      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.54/0.73  thf('50', plain,
% 0.54/0.73      ((((k1_xboole_0) != (k1_xboole_0))
% 0.54/0.73        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.54/0.73        | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.54/0.73      inference('sup-', [status(thm)], ['48', '49'])).
% 0.54/0.73  thf('51', plain,
% 0.54/0.73      ((((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.54/0.73        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.54/0.73      inference('simplify', [status(thm)], ['50'])).
% 0.54/0.73  thf('52', plain,
% 0.54/0.73      (![X1 : $i]:
% 0.54/0.73         (((k2_zfmisc_1 @ k1_xboole_0 @ X1) = (k1_xboole_0))
% 0.54/0.73          | ((X1) = (k1_xboole_0)))),
% 0.54/0.73      inference('simplify', [status(thm)], ['40'])).
% 0.54/0.73  thf('53', plain,
% 0.54/0.73      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 0.54/0.73      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.54/0.73  thf('54', plain,
% 0.54/0.73      (![X0 : $i]: ((v1_relat_1 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.54/0.73      inference('sup+', [status(thm)], ['52', '53'])).
% 0.54/0.73  thf('55', plain,
% 0.54/0.73      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 0.54/0.73      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.54/0.73  thf('56', plain, (((v1_relat_1 @ k1_xboole_0) | (v1_relat_1 @ k1_xboole_0))),
% 0.54/0.73      inference('sup+', [status(thm)], ['54', '55'])).
% 0.54/0.73  thf('57', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.54/0.73      inference('simplify', [status(thm)], ['56'])).
% 0.54/0.73  thf('58', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.73      inference('demod', [status(thm)], ['51', '57'])).
% 0.54/0.73  thf('59', plain,
% 0.54/0.73      (![X0 : $i]: ((r1_tarski @ k1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.54/0.73      inference('demod', [status(thm)], ['43', '58'])).
% 0.54/0.73  thf('60', plain, ((r1_tarski @ (k2_relat_1 @ sk_B) @ sk_A)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('61', plain,
% 0.54/0.73      (![X0 : $i, X2 : $i]:
% 0.54/0.73         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.54/0.73      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.54/0.73  thf('62', plain,
% 0.54/0.73      ((~ (r1_tarski @ sk_A @ (k2_relat_1 @ sk_B))
% 0.54/0.73        | ((sk_A) = (k2_relat_1 @ sk_B)))),
% 0.54/0.73      inference('sup-', [status(thm)], ['60', '61'])).
% 0.54/0.73  thf(d1_funct_2, axiom,
% 0.54/0.73    (![A:$i,B:$i,C:$i]:
% 0.54/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.73       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.54/0.73           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.54/0.73             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.54/0.73         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.54/0.73           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.54/0.73             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.54/0.73  thf(zf_stmt_1, axiom,
% 0.54/0.73    (![B:$i,A:$i]:
% 0.54/0.73     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.54/0.73       ( zip_tseitin_0 @ B @ A ) ))).
% 0.54/0.73  thf('63', plain,
% 0.54/0.73      (![X32 : $i, X33 : $i]:
% 0.54/0.73         ((zip_tseitin_0 @ X32 @ X33) | ((X32) = (k1_xboole_0)))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.54/0.73  thf('64', plain,
% 0.54/0.73      ((m1_subset_1 @ sk_B @ 
% 0.54/0.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.54/0.73      inference('demod', [status(thm)], ['5', '6'])).
% 0.54/0.73  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.54/0.73  thf(zf_stmt_3, axiom,
% 0.54/0.73    (![C:$i,B:$i,A:$i]:
% 0.54/0.73     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.54/0.73       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.54/0.73  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.54/0.73  thf(zf_stmt_5, axiom,
% 0.54/0.73    (![A:$i,B:$i,C:$i]:
% 0.54/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.73       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.54/0.73         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.54/0.73           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.54/0.73             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.54/0.73  thf('65', plain,
% 0.54/0.73      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.54/0.73         (~ (zip_tseitin_0 @ X37 @ X38)
% 0.54/0.73          | (zip_tseitin_1 @ X39 @ X37 @ X38)
% 0.54/0.73          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37))))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.54/0.73  thf('66', plain,
% 0.54/0.73      (((zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))
% 0.54/0.73        | ~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.54/0.73      inference('sup-', [status(thm)], ['64', '65'])).
% 0.54/0.73  thf('67', plain,
% 0.54/0.73      ((m1_subset_1 @ sk_B @ 
% 0.54/0.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.54/0.73      inference('demod', [status(thm)], ['5', '6'])).
% 0.54/0.73  thf(redefinition_k1_relset_1, axiom,
% 0.54/0.73    (![A:$i,B:$i,C:$i]:
% 0.54/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.73       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.54/0.73  thf('68', plain,
% 0.54/0.73      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.54/0.73         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 0.54/0.73          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.54/0.73      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.54/0.73  thf('69', plain,
% 0.54/0.73      (((k1_relset_1 @ (k1_relat_1 @ sk_B) @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 0.54/0.73      inference('sup-', [status(thm)], ['67', '68'])).
% 0.54/0.73  thf('70', plain,
% 0.54/0.73      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.54/0.73         (((X34) != (k1_relset_1 @ X34 @ X35 @ X36))
% 0.54/0.73          | (v1_funct_2 @ X36 @ X34 @ X35)
% 0.54/0.73          | ~ (zip_tseitin_1 @ X36 @ X35 @ X34))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.54/0.73  thf('71', plain,
% 0.54/0.73      ((((k1_relat_1 @ sk_B) != (k1_relat_1 @ sk_B))
% 0.54/0.73        | ~ (zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))
% 0.54/0.73        | (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.54/0.73      inference('sup-', [status(thm)], ['69', '70'])).
% 0.54/0.73  thf('72', plain,
% 0.54/0.73      (((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.54/0.73        | ~ (zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.54/0.73      inference('simplify', [status(thm)], ['71'])).
% 0.54/0.73  thf('73', plain, (~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.54/0.73      inference('simpl_trail', [status(thm)], ['13', '21'])).
% 0.54/0.73  thf('74', plain, (~ (zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.54/0.73      inference('clc', [status(thm)], ['72', '73'])).
% 0.54/0.73  thf('75', plain, (~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.54/0.73      inference('clc', [status(thm)], ['66', '74'])).
% 0.54/0.73  thf('76', plain, (((sk_A) = (k1_xboole_0))),
% 0.54/0.73      inference('sup-', [status(thm)], ['63', '75'])).
% 0.54/0.73  thf('77', plain, (((sk_A) = (k1_xboole_0))),
% 0.54/0.73      inference('sup-', [status(thm)], ['63', '75'])).
% 0.54/0.73  thf('78', plain,
% 0.54/0.73      ((~ (r1_tarski @ k1_xboole_0 @ (k2_relat_1 @ sk_B))
% 0.54/0.73        | ((k1_xboole_0) = (k2_relat_1 @ sk_B)))),
% 0.54/0.73      inference('demod', [status(thm)], ['62', '76', '77'])).
% 0.54/0.73  thf('79', plain,
% 0.54/0.73      ((((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.54/0.73        | ((k1_xboole_0) = (k2_relat_1 @ sk_B)))),
% 0.54/0.73      inference('sup-', [status(thm)], ['59', '78'])).
% 0.54/0.73  thf('80', plain, (((k2_relat_1 @ sk_B) = (k1_xboole_0))),
% 0.54/0.73      inference('simplify', [status(thm)], ['79'])).
% 0.54/0.73  thf('81', plain,
% 0.54/0.73      (![X18 : $i]:
% 0.54/0.73         (((k2_relat_1 @ X18) != (k1_xboole_0))
% 0.54/0.73          | ((X18) = (k1_xboole_0))
% 0.54/0.73          | ~ (v1_relat_1 @ X18))),
% 0.54/0.73      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.54/0.73  thf('82', plain,
% 0.54/0.73      ((((k1_xboole_0) != (k1_xboole_0))
% 0.54/0.73        | ~ (v1_relat_1 @ sk_B)
% 0.54/0.73        | ((sk_B) = (k1_xboole_0)))),
% 0.54/0.73      inference('sup-', [status(thm)], ['80', '81'])).
% 0.54/0.73  thf('83', plain, ((v1_relat_1 @ sk_B)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('84', plain,
% 0.54/0.73      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.54/0.73      inference('demod', [status(thm)], ['82', '83'])).
% 0.54/0.73  thf('85', plain, (((sk_B) = (k1_xboole_0))),
% 0.54/0.73      inference('simplify', [status(thm)], ['84'])).
% 0.54/0.73  thf('86', plain, (((sk_B) = (k1_xboole_0))),
% 0.54/0.73      inference('simplify', [status(thm)], ['84'])).
% 0.54/0.73  thf('87', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.54/0.73      inference('condensation', [status(thm)], ['47'])).
% 0.54/0.73  thf('88', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.73      inference('demod', [status(thm)], ['51', '57'])).
% 0.54/0.73  thf(t21_relat_1, axiom,
% 0.54/0.73    (![A:$i]:
% 0.54/0.73     ( ( v1_relat_1 @ A ) =>
% 0.54/0.73       ( r1_tarski @
% 0.54/0.73         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.54/0.73  thf('89', plain,
% 0.54/0.73      (![X15 : $i]:
% 0.54/0.73         ((r1_tarski @ X15 @ 
% 0.54/0.73           (k2_zfmisc_1 @ (k1_relat_1 @ X15) @ (k2_relat_1 @ X15)))
% 0.54/0.73          | ~ (v1_relat_1 @ X15))),
% 0.54/0.73      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.54/0.73  thf(t25_relat_1, axiom,
% 0.54/0.73    (![A:$i]:
% 0.54/0.73     ( ( v1_relat_1 @ A ) =>
% 0.54/0.73       ( ![B:$i]:
% 0.54/0.73         ( ( v1_relat_1 @ B ) =>
% 0.54/0.73           ( ( r1_tarski @ A @ B ) =>
% 0.54/0.73             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.54/0.73               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.54/0.73  thf('90', plain,
% 0.54/0.73      (![X16 : $i, X17 : $i]:
% 0.54/0.73         (~ (v1_relat_1 @ X16)
% 0.54/0.73          | (r1_tarski @ (k2_relat_1 @ X17) @ (k2_relat_1 @ X16))
% 0.54/0.73          | ~ (r1_tarski @ X17 @ X16)
% 0.54/0.73          | ~ (v1_relat_1 @ X17))),
% 0.54/0.73      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.54/0.73  thf('91', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         (~ (v1_relat_1 @ X0)
% 0.54/0.73          | ~ (v1_relat_1 @ X0)
% 0.54/0.73          | (r1_tarski @ (k2_relat_1 @ X0) @ 
% 0.54/0.73             (k2_relat_1 @ 
% 0.54/0.73              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.54/0.73          | ~ (v1_relat_1 @ 
% 0.54/0.73               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 0.54/0.73      inference('sup-', [status(thm)], ['89', '90'])).
% 0.54/0.73  thf('92', plain,
% 0.54/0.73      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 0.54/0.73      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.54/0.73  thf('93', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         (~ (v1_relat_1 @ X0)
% 0.54/0.73          | ~ (v1_relat_1 @ X0)
% 0.54/0.73          | (r1_tarski @ (k2_relat_1 @ X0) @ 
% 0.54/0.73             (k2_relat_1 @ 
% 0.54/0.73              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.54/0.73      inference('demod', [status(thm)], ['91', '92'])).
% 0.54/0.73  thf('94', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         ((r1_tarski @ (k2_relat_1 @ X0) @ 
% 0.54/0.73           (k2_relat_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.54/0.73          | ~ (v1_relat_1 @ X0))),
% 0.54/0.73      inference('simplify', [status(thm)], ['93'])).
% 0.54/0.73  thf('95', plain,
% 0.54/0.73      (![X13 : $i, X14 : $i]:
% 0.54/0.73         (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X13 @ X14)) @ X14)),
% 0.54/0.73      inference('cnf', [status(esa)], [t194_relat_1])).
% 0.54/0.73  thf('96', plain,
% 0.54/0.73      (![X0 : $i, X2 : $i]:
% 0.54/0.73         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.54/0.73      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.54/0.73  thf('97', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         (~ (r1_tarski @ X0 @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.54/0.73          | ((X0) = (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 0.54/0.73      inference('sup-', [status(thm)], ['95', '96'])).
% 0.54/0.73  thf('98', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         (~ (v1_relat_1 @ X0)
% 0.54/0.73          | ((k2_relat_1 @ X0)
% 0.54/0.73              = (k2_relat_1 @ 
% 0.54/0.73                 (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.54/0.73      inference('sup-', [status(thm)], ['94', '97'])).
% 0.54/0.73  thf('99', plain,
% 0.54/0.73      (![X18 : $i]:
% 0.54/0.73         (((k2_relat_1 @ X18) != (k1_xboole_0))
% 0.54/0.73          | ((X18) = (k1_xboole_0))
% 0.54/0.73          | ~ (v1_relat_1 @ X18))),
% 0.54/0.73      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.54/0.73  thf('100', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 0.54/0.73          | ~ (v1_relat_1 @ X0)
% 0.54/0.73          | ~ (v1_relat_1 @ 
% 0.54/0.73               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 0.54/0.73          | ((k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.54/0.73              = (k1_xboole_0)))),
% 0.54/0.73      inference('sup-', [status(thm)], ['98', '99'])).
% 0.54/0.73  thf('101', plain,
% 0.54/0.73      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 0.54/0.73      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.54/0.73  thf('102', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 0.54/0.73          | ~ (v1_relat_1 @ X0)
% 0.54/0.73          | ((k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.54/0.73              = (k1_xboole_0)))),
% 0.54/0.73      inference('demod', [status(thm)], ['100', '101'])).
% 0.54/0.73  thf('103', plain,
% 0.54/0.73      ((((k1_xboole_0) != (k1_xboole_0))
% 0.54/0.73        | ((k2_zfmisc_1 @ (k1_relat_1 @ k1_xboole_0) @ 
% 0.54/0.73            (k2_relat_1 @ k1_xboole_0)) = (k1_xboole_0))
% 0.54/0.73        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.54/0.73      inference('sup-', [status(thm)], ['88', '102'])).
% 0.54/0.73  thf('104', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.54/0.73      inference('condensation', [status(thm)], ['47'])).
% 0.54/0.73  thf('105', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.73      inference('demod', [status(thm)], ['51', '57'])).
% 0.54/0.73  thf('106', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.54/0.73      inference('simplify', [status(thm)], ['56'])).
% 0.54/0.73  thf('107', plain,
% 0.54/0.73      ((((k1_xboole_0) != (k1_xboole_0))
% 0.54/0.73        | ((k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.54/0.73      inference('demod', [status(thm)], ['103', '104', '105', '106'])).
% 0.54/0.73  thf('108', plain,
% 0.54/0.73      (((k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.73      inference('simplify', [status(thm)], ['107'])).
% 0.54/0.73  thf('109', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.54/0.73      inference('simplify', [status(thm)], ['1'])).
% 0.54/0.73  thf('110', plain,
% 0.54/0.73      (![X6 : $i, X8 : $i]:
% 0.54/0.73         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 0.54/0.73      inference('cnf', [status(esa)], [t3_subset])).
% 0.54/0.73  thf('111', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.54/0.73      inference('sup-', [status(thm)], ['109', '110'])).
% 0.54/0.73  thf(cc1_partfun1, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( v1_xboole_0 @ A ) =>
% 0.54/0.73       ( ![C:$i]:
% 0.54/0.73         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.73           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.54/0.73  thf('112', plain,
% 0.54/0.73      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.54/0.73         (~ (v1_xboole_0 @ X29)
% 0.54/0.73          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X31)))
% 0.54/0.73          | (v1_partfun1 @ X30 @ X29))),
% 0.54/0.73      inference('cnf', [status(esa)], [cc1_partfun1])).
% 0.54/0.73  thf('113', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         ((v1_partfun1 @ (k2_zfmisc_1 @ X1 @ X0) @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.54/0.73      inference('sup-', [status(thm)], ['111', '112'])).
% 0.54/0.73  thf('114', plain,
% 0.54/0.73      (((v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)
% 0.54/0.73        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.54/0.73      inference('sup+', [status(thm)], ['108', '113'])).
% 0.54/0.73  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.54/0.73  thf('115', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.54/0.73      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.54/0.73  thf('116', plain, ((v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)),
% 0.54/0.73      inference('demod', [status(thm)], ['114', '115'])).
% 0.54/0.73  thf('117', plain, ($false),
% 0.54/0.73      inference('demod', [status(thm)], ['23', '85', '86', '87', '116'])).
% 0.54/0.73  
% 0.54/0.73  % SZS output end Refutation
% 0.54/0.73  
% 0.54/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
