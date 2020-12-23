%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KeVG8ITXJO

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:31 EST 2020

% Result     : Theorem 28.92s
% Output     : Refutation 28.92s
% Verified   : 
% Statistics : Number of formulae       :  320 (2400 expanded)
%              Number of leaves         :   50 ( 746 expanded)
%              Depth                    :   39
%              Number of atoms          : 2274 (30006 expanded)
%              Number of equality atoms :   65 (1045 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X16: $i,X18: $i] :
      ( ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('4',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('5',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( v1_xboole_0 @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X42 ) ) )
      | ( v1_xboole_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('7',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('8',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( v4_relat_1 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( v4_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('14',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v4_relat_1 @ X22 @ X23 )
      | ( r1_tarski @ ( k1_relat_1 @ X22 ) @ X23 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('17',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v1_relat_1 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X16: $i,X18: $i] :
      ( ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('22',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['10','23'])).

thf('25',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','26'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('28',plain,(
    ! [X30: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X30 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('29',plain,(
    ! [X30: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X30 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('30',plain,(
    ! [X33: $i] :
      ( ~ ( v2_funct_1 @ X33 )
      | ( ( k1_relat_1 @ X33 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('31',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('32',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_zfmisc_1 @ X14 @ X15 )
        = k1_xboole_0 )
      | ( X15 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('33',plain,(
    ! [X14: $i] :
      ( ( k2_zfmisc_1 @ X14 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','33'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('35',plain,(
    ! [X52: $i] :
      ( ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X52 ) @ ( k2_relat_1 @ X52 ) ) ) )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('36',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('37',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_zfmisc_1 @ X14 @ X15 )
        = k1_xboole_0 )
      | ( X14 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('38',plain,(
    ! [X15: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X15 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( v1_xboole_0 @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X42 ) ) )
      | ( v1_xboole_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('40',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('41',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('42',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['35','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','44'])).

thf('46',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v1_xboole_0 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v1_xboole_0 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','52'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('54',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X16: $i,X18: $i] :
      ( ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(t31_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ C )
          & ( ( k2_relset_1 @ A @ B @ C )
            = B ) )
       => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
          & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
          & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( v2_funct_1 @ C )
            & ( ( k2_relset_1 @ A @ B @ C )
              = B ) )
         => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
            & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
            & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_funct_2])).

thf('59',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['59'])).

thf('61',plain,
    ( ~ ( v1_xboole_0 @ ( k2_funct_1 @ sk_C_1 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['58','60'])).

thf('62',plain,
    ( ( ~ ( v2_funct_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_xboole_0 @ sk_C_1 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['53','61'])).

thf('63',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v1_relat_1 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('67',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ~ ( v1_xboole_0 @ sk_C_1 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['62','63','64','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['65','66'])).

thf('70',plain,(
    ! [X30: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X30 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('71',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['59'])).

thf('72',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['69','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(cc1_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_partfun1 @ C @ A ) ) ) )).

thf('77',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( v1_xboole_0 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X51 ) ) )
      | ( v1_partfun1 @ X50 @ X49 ) ) ),
    inference(cnf,[status(esa)],[cc1_partfun1])).

thf('78',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( v1_partfun1 @ X2 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('80',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_partfun1 @ X46 @ X47 )
      | ( v1_funct_2 @ X46 @ X47 @ X48 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( v1_funct_2 @ X2 @ X1 @ X0 )
      | ~ ( v1_partfun1 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v1_funct_2 @ X1 @ X0 @ X2 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ X1 @ X0 @ X2 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','52'])).

thf('85',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['59'])).

thf('88',plain,
    ( ( ~ ( v1_funct_2 @ k1_xboole_0 @ sk_B_1 @ sk_A )
      | ~ ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v2_funct_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['65','66'])).

thf('90',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( ~ ( v1_funct_2 @ k1_xboole_0 @ sk_B_1 @ sk_A )
      | ~ ( v1_xboole_0 @ sk_C_1 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['88','89','90','91'])).

thf('93',plain,
    ( ( ~ ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_C_1 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['83','92'])).

thf('94',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('95',plain,
    ( ( ~ ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_C_1 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','52'])).

thf('97',plain,(
    ! [X33: $i] :
      ( ~ ( v2_funct_1 @ X33 )
      | ( ( k2_relat_1 @ X33 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('98',plain,(
    ! [X30: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X30 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('99',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('100',plain,(
    ! [X30: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X30 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('101',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('102',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( ( k2_relset_1 @ X44 @ X45 @ X43 )
        = ( k2_relat_1 @ X43 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('103',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X33: $i] :
      ( ~ ( v2_funct_1 @ X33 )
      | ( ( k2_relat_1 @ X33 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('107',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X22 ) @ X23 )
      | ( v4_relat_1 @ X22 @ X23 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
      | ~ ( v2_funct_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['105','108'])).

thf('110',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['65','66'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['109','110','111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( v4_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ X0 )
      | ~ ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['100','113'])).

thf('115',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['65','66'])).

thf('116',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ X0 )
      | ~ ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['114','115','116'])).

thf('118',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['99','117'])).

thf('119',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v4_relat_1 @ X22 @ X23 )
      | ( r1_tarski @ ( k1_relat_1 @ X22 ) @ X23 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('120',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['98','120'])).

thf('122',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['65','66'])).

thf('123',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ sk_B_1 ),
    inference(demod,[status(thm)],['121','122','123'])).

thf('125',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('126',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    | ( sk_B_1
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k2_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 )
    | ( sk_B_1
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['97','126'])).

thf('128',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['103','104'])).

thf('129',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('130',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['65','66'])).

thf('131',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( sk_B_1
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['127','128','129','130','131','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','26'])).

thf('135',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('136',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['96','135'])).

thf('137',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['65','66'])).

thf('140',plain,
    ( ~ ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['136','137','138','139'])).

thf('141',plain,
    ( ( ~ ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['95','140'])).

thf('142',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('144',plain,(
    ! [X30: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X30 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['142','146'])).

thf('148',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['65','66'])).

thf('149',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['147','148','149'])).

thf('151',plain,
    ( ~ ( v1_xboole_0 @ sk_C_1 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['141','150'])).

thf('152',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( v4_relat_1 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('154',plain,(
    v4_relat_1 @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v4_relat_1 @ X22 @ X23 )
      | ( r1_tarski @ ( k1_relat_1 @ X22 ) @ X23 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('156',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['65','66'])).

thf('158',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X30: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X30 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('160',plain,(
    ! [X33: $i] :
      ( ~ ( v2_funct_1 @ X33 )
      | ( ( k1_relat_1 @ X33 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('161',plain,(
    ! [X30: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X30 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('162',plain,(
    ! [X30: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X30 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('163',plain,
    ( sk_B_1
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['127','128','129','130','131','132'])).

thf('164',plain,(
    ! [X52: $i] :
      ( ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X52 ) @ ( k2_relat_1 @ X52 ) ) ) )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('165',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['163','164'])).

thf('166',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['162','165'])).

thf('167',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['65','66'])).

thf('168',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['166','167','168'])).

thf('170',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['161','169'])).

thf('171',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['65','66'])).

thf('172',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ) ),
    inference(demod,[status(thm)],['170','171','172'])).

thf('174',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ ( k1_relat_1 @ sk_C_1 ) ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['160','173'])).

thf('175',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['65','66'])).

thf('176',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['174','175','176','177'])).

thf(t9_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_2 @ D @ A @ B )
        & ( v1_funct_1 @ D ) )
     => ( ( r1_tarski @ B @ C )
       => ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
            & ( v1_funct_2 @ D @ A @ C )
            & ( v1_funct_1 @ D ) )
          | ( ( A != k1_xboole_0 )
            & ( B = k1_xboole_0 ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_1 @ B @ A )
     => ( ( B = k1_xboole_0 )
        & ( A != k1_xboole_0 ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [D: $i,C: $i,A: $i] :
      ( ( zip_tseitin_0 @ D @ C @ A )
     => ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ C )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ B @ C )
       => ( ( zip_tseitin_1 @ B @ A )
          | ( zip_tseitin_0 @ D @ C @ A ) ) ) ) )).

thf('179',plain,(
    ! [X58: $i,X59: $i,X60: $i,X61: $i] :
      ( ~ ( r1_tarski @ X58 @ X59 )
      | ( zip_tseitin_1 @ X58 @ X60 )
      | ~ ( v1_funct_1 @ X61 )
      | ~ ( v1_funct_2 @ X61 @ X60 @ X58 )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X60 @ X58 ) ) )
      | ( zip_tseitin_0 @ X61 @ X59 @ X60 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ sk_B_1 )
      | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
      | ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B_1 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    ! [X33: $i] :
      ( ~ ( v2_funct_1 @ X33 )
      | ( ( k1_relat_1 @ X33 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('182',plain,(
    ! [X30: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X30 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('183',plain,(
    ! [X30: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X30 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('184',plain,
    ( sk_B_1
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['127','128','129','130','131','132'])).

thf('185',plain,(
    ! [X52: $i] :
      ( ( v1_funct_2 @ X52 @ ( k1_relat_1 @ X52 ) @ ( k2_relat_1 @ X52 ) )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('186',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['184','185'])).

thf('187',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['183','186'])).

thf('188',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['65','66'])).

thf('189',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['187','188','189'])).

thf('191',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['182','190'])).

thf('192',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['65','66'])).

thf('193',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['191','192','193'])).

thf('195',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['181','194'])).

thf('196',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['65','66'])).

thf('197',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['195','196','197','198'])).

thf('200',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ sk_B_1 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
      | ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B_1 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['180','199'])).

thf('201',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ X0 )
      | ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B_1 )
      | ( zip_tseitin_0 @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['159','200'])).

thf('202',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['65','66'])).

thf('203',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ X0 )
      | ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B_1 )
      | ( zip_tseitin_0 @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['201','202','203'])).

thf('205',plain,
    ( ( zip_tseitin_0 @ ( k2_funct_1 @ sk_C_1 ) @ sk_A @ sk_B_1 )
    | ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['158','204'])).

thf('206',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( v1_funct_2 @ X53 @ X55 @ X54 )
      | ~ ( zip_tseitin_0 @ X53 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('207',plain,
    ( ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B_1 )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['205','206'])).

thf('208',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['59'])).

thf('209',plain,
    ( ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B_1 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['207','208'])).

thf('210',plain,(
    ! [X56: $i,X57: $i] :
      ( ( X56 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X56 @ X57 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('211',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['209','210'])).

thf('212',plain,(
    ! [X52: $i] :
      ( ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X52 ) @ ( k2_relat_1 @ X52 ) ) ) )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('213',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('214',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['212','213'])).

thf('215',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('216',plain,(
    ! [X14: $i] :
      ( ( k2_zfmisc_1 @ X14 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('217',plain,(
    ! [X0: $i,X1: $i] :
      ( v4_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('218',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['216','217'])).

thf('219',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v4_relat_1 @ X22 @ X23 )
      | ( r1_tarski @ ( k1_relat_1 @ X22 ) @ X23 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('220',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['218','219'])).

thf('221',plain,(
    ! [X14: $i] :
      ( ( k2_zfmisc_1 @ X14 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('222',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('223',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['221','222'])).

thf('224',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['220','223'])).

thf('225',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['220','223'])).

thf('226',plain,(
    ! [X16: $i,X18: $i] :
      ( ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('227',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['225','226'])).

thf('228',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('229',plain,(
    v1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['227','228'])).

thf('230',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('231',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['229','230'])).

thf('232',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['224','231'])).

thf('233',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('234',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['232','233'])).

thf('235',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['215','234'])).

thf('236',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['214','235'])).

thf('237',plain,
    ( ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) ) )
      | ( sk_C_1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['211','236'])).

thf('238',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['103','104'])).

thf('239',plain,(
    ! [X15: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X15 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('240',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('241',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['65','66'])).

thf('242',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['237','238','239','240','241','242'])).

thf('244',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('245',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['151','243','244'])).

thf('246',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B_1 @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['59'])).

thf('247',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['75','245','246'])).

thf('248',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['68','247'])).

thf('249',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['103','104'])).

thf('250',plain,(
    ! [X52: $i] :
      ( ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X52 ) @ ( k2_relat_1 @ X52 ) ) ) )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('251',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['249','250'])).

thf('252',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['65','66'])).

thf('253',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('254',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['251','252','253'])).

thf('255',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( v1_xboole_0 @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X42 ) ) )
      | ( v1_xboole_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('256',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['254','255'])).

thf('257',plain,
    ( ( zip_tseitin_0 @ ( k2_funct_1 @ sk_C_1 ) @ sk_A @ sk_B_1 )
    | ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['158','204'])).

thf('258',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X54 ) ) )
      | ~ ( zip_tseitin_0 @ X53 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('259',plain,
    ( ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B_1 )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['257','258'])).

thf('260',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['59'])).

thf('261',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['75','245','246'])).

thf('262',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['260','261'])).

thf('263',plain,(
    zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B_1 ),
    inference(clc,[status(thm)],['259','262'])).

thf('264',plain,(
    ! [X56: $i,X57: $i] :
      ( ( X56 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X56 @ X57 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('265',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['263','264'])).

thf('266',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('267',plain,(
    v1_xboole_0 @ sk_C_1 ),
    inference(demod,[status(thm)],['256','265','266'])).

thf('268',plain,(
    $false ),
    inference(demod,[status(thm)],['248','267'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KeVG8ITXJO
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:34:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 28.92/29.10  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 28.92/29.10  % Solved by: fo/fo7.sh
% 28.92/29.10  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 28.92/29.10  % done 30064 iterations in 28.635s
% 28.92/29.10  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 28.92/29.10  % SZS output start Refutation
% 28.92/29.10  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 28.92/29.10  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 28.92/29.10  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 28.92/29.10  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 28.92/29.10  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 28.92/29.10  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 28.92/29.10  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 28.92/29.10  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 28.92/29.10  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 28.92/29.10  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 28.92/29.10  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 28.92/29.10  thf(sk_B_type, type, sk_B: $i > $i).
% 28.92/29.10  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 28.92/29.10  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 28.92/29.10  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 28.92/29.10  thf(sk_B_1_type, type, sk_B_1: $i).
% 28.92/29.10  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 28.92/29.10  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 28.92/29.10  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 28.92/29.10  thf(sk_C_1_type, type, sk_C_1: $i).
% 28.92/29.10  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 28.92/29.10  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 28.92/29.10  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 28.92/29.10  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 28.92/29.10  thf(sk_A_type, type, sk_A: $i).
% 28.92/29.10  thf(d1_xboole_0, axiom,
% 28.92/29.10    (![A:$i]:
% 28.92/29.10     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 28.92/29.10  thf('0', plain,
% 28.92/29.10      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 28.92/29.10      inference('cnf', [status(esa)], [d1_xboole_0])).
% 28.92/29.10  thf(d10_xboole_0, axiom,
% 28.92/29.10    (![A:$i,B:$i]:
% 28.92/29.10     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 28.92/29.10  thf('1', plain,
% 28.92/29.10      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 28.92/29.10      inference('cnf', [status(esa)], [d10_xboole_0])).
% 28.92/29.10  thf('2', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 28.92/29.10      inference('simplify', [status(thm)], ['1'])).
% 28.92/29.10  thf(t3_subset, axiom,
% 28.92/29.10    (![A:$i,B:$i]:
% 28.92/29.10     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 28.92/29.10  thf('3', plain,
% 28.92/29.10      (![X16 : $i, X18 : $i]:
% 28.92/29.10         ((m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X18)) | ~ (r1_tarski @ X16 @ X18))),
% 28.92/29.10      inference('cnf', [status(esa)], [t3_subset])).
% 28.92/29.10  thf('4', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 28.92/29.10      inference('sup-', [status(thm)], ['2', '3'])).
% 28.92/29.10  thf(cc3_relset_1, axiom,
% 28.92/29.10    (![A:$i,B:$i]:
% 28.92/29.10     ( ( v1_xboole_0 @ A ) =>
% 28.92/29.10       ( ![C:$i]:
% 28.92/29.10         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 28.92/29.10           ( v1_xboole_0 @ C ) ) ) ))).
% 28.92/29.10  thf('5', plain,
% 28.92/29.10      (![X40 : $i, X41 : $i, X42 : $i]:
% 28.92/29.10         (~ (v1_xboole_0 @ X40)
% 28.92/29.10          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X42)))
% 28.92/29.10          | (v1_xboole_0 @ X41))),
% 28.92/29.10      inference('cnf', [status(esa)], [cc3_relset_1])).
% 28.92/29.10  thf('6', plain,
% 28.92/29.10      (![X0 : $i, X1 : $i]:
% 28.92/29.10         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)) | ~ (v1_xboole_0 @ X1))),
% 28.92/29.10      inference('sup-', [status(thm)], ['4', '5'])).
% 28.92/29.10  thf(l13_xboole_0, axiom,
% 28.92/29.10    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 28.92/29.10  thf('7', plain,
% 28.92/29.10      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 28.92/29.10      inference('cnf', [status(esa)], [l13_xboole_0])).
% 28.92/29.10  thf('8', plain,
% 28.92/29.10      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 28.92/29.10      inference('cnf', [status(esa)], [l13_xboole_0])).
% 28.92/29.10  thf('9', plain,
% 28.92/29.10      (![X0 : $i, X1 : $i]:
% 28.92/29.10         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 28.92/29.10      inference('sup+', [status(thm)], ['7', '8'])).
% 28.92/29.10  thf('10', plain,
% 28.92/29.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 28.92/29.10         (~ (v1_xboole_0 @ X1)
% 28.92/29.10          | ~ (v1_xboole_0 @ X2)
% 28.92/29.10          | ((k2_zfmisc_1 @ X1 @ X0) = (X2)))),
% 28.92/29.10      inference('sup-', [status(thm)], ['6', '9'])).
% 28.92/29.10  thf('11', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 28.92/29.10      inference('sup-', [status(thm)], ['2', '3'])).
% 28.92/29.10  thf(cc2_relset_1, axiom,
% 28.92/29.10    (![A:$i,B:$i,C:$i]:
% 28.92/29.10     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 28.92/29.10       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 28.92/29.10  thf('12', plain,
% 28.92/29.10      (![X37 : $i, X38 : $i, X39 : $i]:
% 28.92/29.10         ((v4_relat_1 @ X37 @ X38)
% 28.92/29.10          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 28.92/29.10      inference('cnf', [status(esa)], [cc2_relset_1])).
% 28.92/29.10  thf('13', plain,
% 28.92/29.10      (![X0 : $i, X1 : $i]: (v4_relat_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X1)),
% 28.92/29.10      inference('sup-', [status(thm)], ['11', '12'])).
% 28.92/29.10  thf(d18_relat_1, axiom,
% 28.92/29.10    (![A:$i,B:$i]:
% 28.92/29.10     ( ( v1_relat_1 @ B ) =>
% 28.92/29.10       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 28.92/29.10  thf('14', plain,
% 28.92/29.10      (![X22 : $i, X23 : $i]:
% 28.92/29.10         (~ (v4_relat_1 @ X22 @ X23)
% 28.92/29.10          | (r1_tarski @ (k1_relat_1 @ X22) @ X23)
% 28.92/29.10          | ~ (v1_relat_1 @ X22))),
% 28.92/29.10      inference('cnf', [status(esa)], [d18_relat_1])).
% 28.92/29.10  thf('15', plain,
% 28.92/29.10      (![X0 : $i, X1 : $i]:
% 28.92/29.10         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1))
% 28.92/29.10          | (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) @ X0))),
% 28.92/29.10      inference('sup-', [status(thm)], ['13', '14'])).
% 28.92/29.10  thf('16', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 28.92/29.10      inference('sup-', [status(thm)], ['2', '3'])).
% 28.92/29.10  thf(cc1_relset_1, axiom,
% 28.92/29.10    (![A:$i,B:$i,C:$i]:
% 28.92/29.10     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 28.92/29.10       ( v1_relat_1 @ C ) ))).
% 28.92/29.10  thf('17', plain,
% 28.92/29.10      (![X34 : $i, X35 : $i, X36 : $i]:
% 28.92/29.10         ((v1_relat_1 @ X34)
% 28.92/29.10          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 28.92/29.10      inference('cnf', [status(esa)], [cc1_relset_1])).
% 28.92/29.10  thf('18', plain,
% 28.92/29.10      (![X0 : $i, X1 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))),
% 28.92/29.10      inference('sup-', [status(thm)], ['16', '17'])).
% 28.92/29.10  thf('19', plain,
% 28.92/29.10      (![X0 : $i, X1 : $i]:
% 28.92/29.10         (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) @ X0)),
% 28.92/29.10      inference('demod', [status(thm)], ['15', '18'])).
% 28.92/29.10  thf('20', plain,
% 28.92/29.10      (![X16 : $i, X18 : $i]:
% 28.92/29.10         ((m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X18)) | ~ (r1_tarski @ X16 @ X18))),
% 28.92/29.10      inference('cnf', [status(esa)], [t3_subset])).
% 28.92/29.10  thf('21', plain,
% 28.92/29.10      (![X0 : $i, X1 : $i]:
% 28.92/29.10         (m1_subset_1 @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) @ 
% 28.92/29.10          (k1_zfmisc_1 @ X0))),
% 28.92/29.10      inference('sup-', [status(thm)], ['19', '20'])).
% 28.92/29.10  thf(t5_subset, axiom,
% 28.92/29.10    (![A:$i,B:$i,C:$i]:
% 28.92/29.10     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 28.92/29.10          ( v1_xboole_0 @ C ) ) ))).
% 28.92/29.10  thf('22', plain,
% 28.92/29.10      (![X19 : $i, X20 : $i, X21 : $i]:
% 28.92/29.10         (~ (r2_hidden @ X19 @ X20)
% 28.92/29.10          | ~ (v1_xboole_0 @ X21)
% 28.92/29.10          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 28.92/29.10      inference('cnf', [status(esa)], [t5_subset])).
% 28.92/29.10  thf('23', plain,
% 28.92/29.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 28.92/29.10         (~ (v1_xboole_0 @ X0)
% 28.92/29.10          | ~ (r2_hidden @ X2 @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1))))),
% 28.92/29.10      inference('sup-', [status(thm)], ['21', '22'])).
% 28.92/29.10  thf('24', plain,
% 28.92/29.10      (![X0 : $i, X2 : $i, X3 : $i]:
% 28.92/29.10         (~ (r2_hidden @ X3 @ (k1_relat_1 @ X0))
% 28.92/29.10          | ~ (v1_xboole_0 @ X0)
% 28.92/29.10          | ~ (v1_xboole_0 @ X2)
% 28.92/29.10          | ~ (v1_xboole_0 @ X2))),
% 28.92/29.10      inference('sup-', [status(thm)], ['10', '23'])).
% 28.92/29.10  thf('25', plain,
% 28.92/29.10      (![X0 : $i, X2 : $i, X3 : $i]:
% 28.92/29.10         (~ (v1_xboole_0 @ X2)
% 28.92/29.10          | ~ (v1_xboole_0 @ X0)
% 28.92/29.10          | ~ (r2_hidden @ X3 @ (k1_relat_1 @ X0)))),
% 28.92/29.10      inference('simplify', [status(thm)], ['24'])).
% 28.92/29.10  thf('26', plain,
% 28.92/29.10      (![X0 : $i, X1 : $i]:
% 28.92/29.10         (~ (r2_hidden @ X1 @ (k1_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 28.92/29.10      inference('condensation', [status(thm)], ['25'])).
% 28.92/29.10  thf('27', plain,
% 28.92/29.10      (![X0 : $i]: ((v1_xboole_0 @ (k1_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 28.92/29.10      inference('sup-', [status(thm)], ['0', '26'])).
% 28.92/29.10  thf(dt_k2_funct_1, axiom,
% 28.92/29.10    (![A:$i]:
% 28.92/29.10     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 28.92/29.10       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 28.92/29.10         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 28.92/29.10  thf('28', plain,
% 28.92/29.10      (![X30 : $i]:
% 28.92/29.10         ((v1_funct_1 @ (k2_funct_1 @ X30))
% 28.92/29.10          | ~ (v1_funct_1 @ X30)
% 28.92/29.10          | ~ (v1_relat_1 @ X30))),
% 28.92/29.10      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 28.92/29.10  thf('29', plain,
% 28.92/29.10      (![X30 : $i]:
% 28.92/29.10         ((v1_relat_1 @ (k2_funct_1 @ X30))
% 28.92/29.10          | ~ (v1_funct_1 @ X30)
% 28.92/29.10          | ~ (v1_relat_1 @ X30))),
% 28.92/29.10      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 28.92/29.10  thf(t55_funct_1, axiom,
% 28.92/29.10    (![A:$i]:
% 28.92/29.10     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 28.92/29.10       ( ( v2_funct_1 @ A ) =>
% 28.92/29.10         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 28.92/29.10           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 28.92/29.10  thf('30', plain,
% 28.92/29.10      (![X33 : $i]:
% 28.92/29.10         (~ (v2_funct_1 @ X33)
% 28.92/29.10          | ((k1_relat_1 @ X33) = (k2_relat_1 @ (k2_funct_1 @ X33)))
% 28.92/29.10          | ~ (v1_funct_1 @ X33)
% 28.92/29.10          | ~ (v1_relat_1 @ X33))),
% 28.92/29.10      inference('cnf', [status(esa)], [t55_funct_1])).
% 28.92/29.10  thf('31', plain,
% 28.92/29.10      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 28.92/29.10      inference('cnf', [status(esa)], [l13_xboole_0])).
% 28.92/29.10  thf(t113_zfmisc_1, axiom,
% 28.92/29.10    (![A:$i,B:$i]:
% 28.92/29.10     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 28.92/29.10       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 28.92/29.10  thf('32', plain,
% 28.92/29.10      (![X14 : $i, X15 : $i]:
% 28.92/29.10         (((k2_zfmisc_1 @ X14 @ X15) = (k1_xboole_0))
% 28.92/29.10          | ((X15) != (k1_xboole_0)))),
% 28.92/29.10      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 28.92/29.10  thf('33', plain,
% 28.92/29.10      (![X14 : $i]: ((k2_zfmisc_1 @ X14 @ k1_xboole_0) = (k1_xboole_0))),
% 28.92/29.10      inference('simplify', [status(thm)], ['32'])).
% 28.92/29.10  thf('34', plain,
% 28.92/29.10      (![X0 : $i, X1 : $i]:
% 28.92/29.10         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 28.92/29.10      inference('sup+', [status(thm)], ['31', '33'])).
% 28.92/29.10  thf(t3_funct_2, axiom,
% 28.92/29.10    (![A:$i]:
% 28.92/29.10     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 28.92/29.10       ( ( v1_funct_1 @ A ) & 
% 28.92/29.10         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 28.92/29.10         ( m1_subset_1 @
% 28.92/29.10           A @ 
% 28.92/29.10           ( k1_zfmisc_1 @
% 28.92/29.10             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 28.92/29.10  thf('35', plain,
% 28.92/29.10      (![X52 : $i]:
% 28.92/29.10         ((m1_subset_1 @ X52 @ 
% 28.92/29.10           (k1_zfmisc_1 @ 
% 28.92/29.10            (k2_zfmisc_1 @ (k1_relat_1 @ X52) @ (k2_relat_1 @ X52))))
% 28.92/29.10          | ~ (v1_funct_1 @ X52)
% 28.92/29.10          | ~ (v1_relat_1 @ X52))),
% 28.92/29.10      inference('cnf', [status(esa)], [t3_funct_2])).
% 28.92/29.10  thf('36', plain,
% 28.92/29.10      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 28.92/29.10      inference('cnf', [status(esa)], [l13_xboole_0])).
% 28.92/29.10  thf('37', plain,
% 28.92/29.10      (![X14 : $i, X15 : $i]:
% 28.92/29.10         (((k2_zfmisc_1 @ X14 @ X15) = (k1_xboole_0))
% 28.92/29.10          | ((X14) != (k1_xboole_0)))),
% 28.92/29.10      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 28.92/29.10  thf('38', plain,
% 28.92/29.10      (![X15 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X15) = (k1_xboole_0))),
% 28.92/29.10      inference('simplify', [status(thm)], ['37'])).
% 28.92/29.10  thf('39', plain,
% 28.92/29.10      (![X40 : $i, X41 : $i, X42 : $i]:
% 28.92/29.10         (~ (v1_xboole_0 @ X40)
% 28.92/29.10          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X42)))
% 28.92/29.10          | (v1_xboole_0 @ X41))),
% 28.92/29.10      inference('cnf', [status(esa)], [cc3_relset_1])).
% 28.92/29.10  thf('40', plain,
% 28.92/29.10      (![X1 : $i]:
% 28.92/29.10         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 28.92/29.10          | (v1_xboole_0 @ X1)
% 28.92/29.10          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 28.92/29.10      inference('sup-', [status(thm)], ['38', '39'])).
% 28.92/29.10  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 28.92/29.10  thf('41', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 28.92/29.10      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 28.92/29.10  thf('42', plain,
% 28.92/29.10      (![X1 : $i]:
% 28.92/29.10         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 28.92/29.10          | (v1_xboole_0 @ X1))),
% 28.92/29.10      inference('demod', [status(thm)], ['40', '41'])).
% 28.92/29.10  thf('43', plain,
% 28.92/29.10      (![X0 : $i, X1 : $i]:
% 28.92/29.10         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 28.92/29.10          | ~ (v1_xboole_0 @ X0)
% 28.92/29.10          | (v1_xboole_0 @ X1))),
% 28.92/29.10      inference('sup-', [status(thm)], ['36', '42'])).
% 28.92/29.10  thf('44', plain,
% 28.92/29.10      (![X0 : $i]:
% 28.92/29.10         (~ (v1_relat_1 @ X0)
% 28.92/29.10          | ~ (v1_funct_1 @ X0)
% 28.92/29.10          | (v1_xboole_0 @ X0)
% 28.92/29.10          | ~ (v1_xboole_0 @ 
% 28.92/29.10               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 28.92/29.10      inference('sup-', [status(thm)], ['35', '43'])).
% 28.92/29.10  thf('45', plain,
% 28.92/29.10      (![X0 : $i]:
% 28.92/29.10         (~ (v1_xboole_0 @ k1_xboole_0)
% 28.92/29.10          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 28.92/29.10          | (v1_xboole_0 @ X0)
% 28.92/29.10          | ~ (v1_funct_1 @ X0)
% 28.92/29.10          | ~ (v1_relat_1 @ X0))),
% 28.92/29.10      inference('sup-', [status(thm)], ['34', '44'])).
% 28.92/29.10  thf('46', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 28.92/29.10      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 28.92/29.10  thf('47', plain,
% 28.92/29.10      (![X0 : $i]:
% 28.92/29.10         (~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 28.92/29.10          | (v1_xboole_0 @ X0)
% 28.92/29.10          | ~ (v1_funct_1 @ X0)
% 28.92/29.10          | ~ (v1_relat_1 @ X0))),
% 28.92/29.10      inference('demod', [status(thm)], ['45', '46'])).
% 28.92/29.10  thf('48', plain,
% 28.92/29.10      (![X0 : $i]:
% 28.92/29.10         (~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 28.92/29.10          | ~ (v1_relat_1 @ X0)
% 28.92/29.10          | ~ (v1_funct_1 @ X0)
% 28.92/29.10          | ~ (v2_funct_1 @ X0)
% 28.92/29.10          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 28.92/29.10          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 28.92/29.10          | (v1_xboole_0 @ (k2_funct_1 @ X0)))),
% 28.92/29.10      inference('sup-', [status(thm)], ['30', '47'])).
% 28.92/29.10  thf('49', plain,
% 28.92/29.10      (![X0 : $i]:
% 28.92/29.10         (~ (v1_relat_1 @ X0)
% 28.92/29.10          | ~ (v1_funct_1 @ X0)
% 28.92/29.10          | (v1_xboole_0 @ (k2_funct_1 @ X0))
% 28.92/29.10          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 28.92/29.10          | ~ (v2_funct_1 @ X0)
% 28.92/29.10          | ~ (v1_funct_1 @ X0)
% 28.92/29.10          | ~ (v1_relat_1 @ X0)
% 28.92/29.10          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 28.92/29.10      inference('sup-', [status(thm)], ['29', '48'])).
% 28.92/29.10  thf('50', plain,
% 28.92/29.10      (![X0 : $i]:
% 28.92/29.10         (~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 28.92/29.10          | ~ (v2_funct_1 @ X0)
% 28.92/29.10          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 28.92/29.10          | (v1_xboole_0 @ (k2_funct_1 @ X0))
% 28.92/29.10          | ~ (v1_funct_1 @ X0)
% 28.92/29.10          | ~ (v1_relat_1 @ X0))),
% 28.92/29.10      inference('simplify', [status(thm)], ['49'])).
% 28.92/29.10  thf('51', plain,
% 28.92/29.10      (![X0 : $i]:
% 28.92/29.10         (~ (v1_relat_1 @ X0)
% 28.92/29.10          | ~ (v1_funct_1 @ X0)
% 28.92/29.10          | ~ (v1_relat_1 @ X0)
% 28.92/29.10          | ~ (v1_funct_1 @ X0)
% 28.92/29.10          | (v1_xboole_0 @ (k2_funct_1 @ X0))
% 28.92/29.10          | ~ (v2_funct_1 @ X0)
% 28.92/29.10          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 28.92/29.10      inference('sup-', [status(thm)], ['28', '50'])).
% 28.92/29.10  thf('52', plain,
% 28.92/29.10      (![X0 : $i]:
% 28.92/29.10         (~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 28.92/29.10          | ~ (v2_funct_1 @ X0)
% 28.92/29.10          | (v1_xboole_0 @ (k2_funct_1 @ X0))
% 28.92/29.10          | ~ (v1_funct_1 @ X0)
% 28.92/29.10          | ~ (v1_relat_1 @ X0))),
% 28.92/29.10      inference('simplify', [status(thm)], ['51'])).
% 28.92/29.10  thf('53', plain,
% 28.92/29.10      (![X0 : $i]:
% 28.92/29.10         (~ (v1_xboole_0 @ X0)
% 28.92/29.10          | ~ (v1_relat_1 @ X0)
% 28.92/29.10          | ~ (v1_funct_1 @ X0)
% 28.92/29.10          | (v1_xboole_0 @ (k2_funct_1 @ X0))
% 28.92/29.10          | ~ (v2_funct_1 @ X0))),
% 28.92/29.10      inference('sup-', [status(thm)], ['27', '52'])).
% 28.92/29.10  thf(d3_tarski, axiom,
% 28.92/29.10    (![A:$i,B:$i]:
% 28.92/29.10     ( ( r1_tarski @ A @ B ) <=>
% 28.92/29.10       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 28.92/29.10  thf('54', plain,
% 28.92/29.10      (![X4 : $i, X6 : $i]:
% 28.92/29.10         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 28.92/29.10      inference('cnf', [status(esa)], [d3_tarski])).
% 28.92/29.10  thf('55', plain,
% 28.92/29.10      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 28.92/29.10      inference('cnf', [status(esa)], [d1_xboole_0])).
% 28.92/29.10  thf('56', plain,
% 28.92/29.10      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 28.92/29.10      inference('sup-', [status(thm)], ['54', '55'])).
% 28.92/29.10  thf('57', plain,
% 28.92/29.10      (![X16 : $i, X18 : $i]:
% 28.92/29.10         ((m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X18)) | ~ (r1_tarski @ X16 @ X18))),
% 28.92/29.10      inference('cnf', [status(esa)], [t3_subset])).
% 28.92/29.10  thf('58', plain,
% 28.92/29.10      (![X0 : $i, X1 : $i]:
% 28.92/29.10         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 28.92/29.10      inference('sup-', [status(thm)], ['56', '57'])).
% 28.92/29.10  thf(t31_funct_2, conjecture,
% 28.92/29.10    (![A:$i,B:$i,C:$i]:
% 28.92/29.10     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 28.92/29.10         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 28.92/29.10       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 28.92/29.10         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 28.92/29.10           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 28.92/29.10           ( m1_subset_1 @
% 28.92/29.10             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 28.92/29.10  thf(zf_stmt_0, negated_conjecture,
% 28.92/29.10    (~( ![A:$i,B:$i,C:$i]:
% 28.92/29.10        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 28.92/29.10            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 28.92/29.10          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 28.92/29.10            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 28.92/29.10              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 28.92/29.10              ( m1_subset_1 @
% 28.92/29.10                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 28.92/29.10    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 28.92/29.10  thf('59', plain,
% 28.92/29.10      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 28.92/29.10        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)
% 28.92/29.10        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 28.92/29.10             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))),
% 28.92/29.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.92/29.10  thf('60', plain,
% 28.92/29.10      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 28.92/29.10           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))
% 28.92/29.10         <= (~
% 28.92/29.10             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 28.92/29.10               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 28.92/29.10      inference('split', [status(esa)], ['59'])).
% 28.92/29.10  thf('61', plain,
% 28.92/29.10      ((~ (v1_xboole_0 @ (k2_funct_1 @ sk_C_1)))
% 28.92/29.10         <= (~
% 28.92/29.10             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 28.92/29.10               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 28.92/29.10      inference('sup-', [status(thm)], ['58', '60'])).
% 28.92/29.10  thf('62', plain,
% 28.92/29.10      (((~ (v2_funct_1 @ sk_C_1)
% 28.92/29.10         | ~ (v1_funct_1 @ sk_C_1)
% 28.92/29.10         | ~ (v1_relat_1 @ sk_C_1)
% 28.92/29.10         | ~ (v1_xboole_0 @ sk_C_1)))
% 28.92/29.10         <= (~
% 28.92/29.10             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 28.92/29.10               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 28.92/29.10      inference('sup-', [status(thm)], ['53', '61'])).
% 28.92/29.10  thf('63', plain, ((v2_funct_1 @ sk_C_1)),
% 28.92/29.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.92/29.10  thf('64', plain, ((v1_funct_1 @ sk_C_1)),
% 28.92/29.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.92/29.10  thf('65', plain,
% 28.92/29.10      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 28.92/29.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.92/29.10  thf('66', plain,
% 28.92/29.10      (![X34 : $i, X35 : $i, X36 : $i]:
% 28.92/29.10         ((v1_relat_1 @ X34)
% 28.92/29.10          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 28.92/29.10      inference('cnf', [status(esa)], [cc1_relset_1])).
% 28.92/29.10  thf('67', plain, ((v1_relat_1 @ sk_C_1)),
% 28.92/29.10      inference('sup-', [status(thm)], ['65', '66'])).
% 28.92/29.10  thf('68', plain,
% 28.92/29.10      ((~ (v1_xboole_0 @ sk_C_1))
% 28.92/29.10         <= (~
% 28.92/29.10             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 28.92/29.10               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 28.92/29.10      inference('demod', [status(thm)], ['62', '63', '64', '67'])).
% 28.92/29.10  thf('69', plain, ((v1_relat_1 @ sk_C_1)),
% 28.92/29.10      inference('sup-', [status(thm)], ['65', '66'])).
% 28.92/29.10  thf('70', plain,
% 28.92/29.10      (![X30 : $i]:
% 28.92/29.10         ((v1_funct_1 @ (k2_funct_1 @ X30))
% 28.92/29.10          | ~ (v1_funct_1 @ X30)
% 28.92/29.10          | ~ (v1_relat_1 @ X30))),
% 28.92/29.10      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 28.92/29.10  thf('71', plain,
% 28.92/29.10      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1)))
% 28.92/29.10         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 28.92/29.10      inference('split', [status(esa)], ['59'])).
% 28.92/29.10  thf('72', plain,
% 28.92/29.10      (((~ (v1_relat_1 @ sk_C_1) | ~ (v1_funct_1 @ sk_C_1)))
% 28.92/29.10         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 28.92/29.10      inference('sup-', [status(thm)], ['70', '71'])).
% 28.92/29.10  thf('73', plain, ((v1_funct_1 @ sk_C_1)),
% 28.92/29.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.92/29.10  thf('74', plain,
% 28.92/29.10      ((~ (v1_relat_1 @ sk_C_1)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 28.92/29.10      inference('demod', [status(thm)], ['72', '73'])).
% 28.92/29.10  thf('75', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 28.92/29.10      inference('sup-', [status(thm)], ['69', '74'])).
% 28.92/29.10  thf('76', plain,
% 28.92/29.10      (![X0 : $i, X1 : $i]:
% 28.92/29.10         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 28.92/29.10      inference('sup-', [status(thm)], ['56', '57'])).
% 28.92/29.10  thf(cc1_partfun1, axiom,
% 28.92/29.10    (![A:$i,B:$i]:
% 28.92/29.10     ( ( v1_xboole_0 @ A ) =>
% 28.92/29.10       ( ![C:$i]:
% 28.92/29.10         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 28.92/29.10           ( v1_partfun1 @ C @ A ) ) ) ))).
% 28.92/29.10  thf('77', plain,
% 28.92/29.10      (![X49 : $i, X50 : $i, X51 : $i]:
% 28.92/29.10         (~ (v1_xboole_0 @ X49)
% 28.92/29.10          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X51)))
% 28.92/29.10          | (v1_partfun1 @ X50 @ X49))),
% 28.92/29.10      inference('cnf', [status(esa)], [cc1_partfun1])).
% 28.92/29.10  thf('78', plain,
% 28.92/29.10      (![X1 : $i, X2 : $i]:
% 28.92/29.10         (~ (v1_xboole_0 @ X2) | (v1_partfun1 @ X2 @ X1) | ~ (v1_xboole_0 @ X1))),
% 28.92/29.10      inference('sup-', [status(thm)], ['76', '77'])).
% 28.92/29.10  thf('79', plain,
% 28.92/29.10      (![X0 : $i, X1 : $i]:
% 28.92/29.10         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 28.92/29.10      inference('sup-', [status(thm)], ['56', '57'])).
% 28.92/29.10  thf(cc1_funct_2, axiom,
% 28.92/29.10    (![A:$i,B:$i,C:$i]:
% 28.92/29.10     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 28.92/29.10       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 28.92/29.10         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 28.92/29.10  thf('80', plain,
% 28.92/29.10      (![X46 : $i, X47 : $i, X48 : $i]:
% 28.92/29.10         (~ (v1_funct_1 @ X46)
% 28.92/29.10          | ~ (v1_partfun1 @ X46 @ X47)
% 28.92/29.10          | (v1_funct_2 @ X46 @ X47 @ X48)
% 28.92/29.10          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48))))),
% 28.92/29.10      inference('cnf', [status(esa)], [cc1_funct_2])).
% 28.92/29.10  thf('81', plain,
% 28.92/29.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 28.92/29.10         (~ (v1_xboole_0 @ X2)
% 28.92/29.10          | (v1_funct_2 @ X2 @ X1 @ X0)
% 28.92/29.10          | ~ (v1_partfun1 @ X2 @ X1)
% 28.92/29.10          | ~ (v1_funct_1 @ X2))),
% 28.92/29.10      inference('sup-', [status(thm)], ['79', '80'])).
% 28.92/29.10  thf('82', plain,
% 28.92/29.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 28.92/29.10         (~ (v1_xboole_0 @ X0)
% 28.92/29.10          | ~ (v1_xboole_0 @ X1)
% 28.92/29.10          | ~ (v1_funct_1 @ X1)
% 28.92/29.10          | (v1_funct_2 @ X1 @ X0 @ X2)
% 28.92/29.10          | ~ (v1_xboole_0 @ X1))),
% 28.92/29.10      inference('sup-', [status(thm)], ['78', '81'])).
% 28.92/29.10  thf('83', plain,
% 28.92/29.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 28.92/29.10         ((v1_funct_2 @ X1 @ X0 @ X2)
% 28.92/29.10          | ~ (v1_funct_1 @ X1)
% 28.92/29.10          | ~ (v1_xboole_0 @ X1)
% 28.92/29.10          | ~ (v1_xboole_0 @ X0))),
% 28.92/29.10      inference('simplify', [status(thm)], ['82'])).
% 28.92/29.10  thf('84', plain,
% 28.92/29.10      (![X0 : $i]:
% 28.92/29.10         (~ (v1_xboole_0 @ X0)
% 28.92/29.10          | ~ (v1_relat_1 @ X0)
% 28.92/29.10          | ~ (v1_funct_1 @ X0)
% 28.92/29.10          | (v1_xboole_0 @ (k2_funct_1 @ X0))
% 28.92/29.10          | ~ (v2_funct_1 @ X0))),
% 28.92/29.10      inference('sup-', [status(thm)], ['27', '52'])).
% 28.92/29.10  thf('85', plain,
% 28.92/29.10      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 28.92/29.10      inference('cnf', [status(esa)], [l13_xboole_0])).
% 28.92/29.10  thf('86', plain,
% 28.92/29.10      (![X0 : $i]:
% 28.92/29.10         (~ (v2_funct_1 @ X0)
% 28.92/29.10          | ~ (v1_funct_1 @ X0)
% 28.92/29.10          | ~ (v1_relat_1 @ X0)
% 28.92/29.10          | ~ (v1_xboole_0 @ X0)
% 28.92/29.10          | ((k2_funct_1 @ X0) = (k1_xboole_0)))),
% 28.92/29.10      inference('sup-', [status(thm)], ['84', '85'])).
% 28.92/29.10  thf('87', plain,
% 28.92/29.10      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A))
% 28.92/29.10         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 28.92/29.10      inference('split', [status(esa)], ['59'])).
% 28.92/29.10  thf('88', plain,
% 28.92/29.10      (((~ (v1_funct_2 @ k1_xboole_0 @ sk_B_1 @ sk_A)
% 28.92/29.10         | ~ (v1_xboole_0 @ sk_C_1)
% 28.92/29.10         | ~ (v1_relat_1 @ sk_C_1)
% 28.92/29.10         | ~ (v1_funct_1 @ sk_C_1)
% 28.92/29.10         | ~ (v2_funct_1 @ sk_C_1)))
% 28.92/29.10         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 28.92/29.10      inference('sup-', [status(thm)], ['86', '87'])).
% 28.92/29.10  thf('89', plain, ((v1_relat_1 @ sk_C_1)),
% 28.92/29.10      inference('sup-', [status(thm)], ['65', '66'])).
% 28.92/29.10  thf('90', plain, ((v1_funct_1 @ sk_C_1)),
% 28.92/29.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.92/29.10  thf('91', plain, ((v2_funct_1 @ sk_C_1)),
% 28.92/29.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.92/29.10  thf('92', plain,
% 28.92/29.10      (((~ (v1_funct_2 @ k1_xboole_0 @ sk_B_1 @ sk_A)
% 28.92/29.10         | ~ (v1_xboole_0 @ sk_C_1)))
% 28.92/29.10         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 28.92/29.10      inference('demod', [status(thm)], ['88', '89', '90', '91'])).
% 28.92/29.10  thf('93', plain,
% 28.92/29.10      (((~ (v1_xboole_0 @ sk_B_1)
% 28.92/29.10         | ~ (v1_xboole_0 @ k1_xboole_0)
% 28.92/29.10         | ~ (v1_funct_1 @ k1_xboole_0)
% 28.92/29.10         | ~ (v1_xboole_0 @ sk_C_1)))
% 28.92/29.10         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 28.92/29.10      inference('sup-', [status(thm)], ['83', '92'])).
% 28.92/29.10  thf('94', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 28.92/29.10      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 28.92/29.10  thf('95', plain,
% 28.92/29.10      (((~ (v1_xboole_0 @ sk_B_1)
% 28.92/29.10         | ~ (v1_funct_1 @ k1_xboole_0)
% 28.92/29.10         | ~ (v1_xboole_0 @ sk_C_1)))
% 28.92/29.10         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 28.92/29.10      inference('demod', [status(thm)], ['93', '94'])).
% 28.92/29.10  thf('96', plain,
% 28.92/29.10      (![X0 : $i]:
% 28.92/29.10         (~ (v1_xboole_0 @ X0)
% 28.92/29.10          | ~ (v1_relat_1 @ X0)
% 28.92/29.10          | ~ (v1_funct_1 @ X0)
% 28.92/29.10          | (v1_xboole_0 @ (k2_funct_1 @ X0))
% 28.92/29.10          | ~ (v2_funct_1 @ X0))),
% 28.92/29.10      inference('sup-', [status(thm)], ['27', '52'])).
% 28.92/29.10  thf('97', plain,
% 28.92/29.10      (![X33 : $i]:
% 28.92/29.10         (~ (v2_funct_1 @ X33)
% 28.92/29.10          | ((k2_relat_1 @ X33) = (k1_relat_1 @ (k2_funct_1 @ X33)))
% 28.92/29.10          | ~ (v1_funct_1 @ X33)
% 28.92/29.10          | ~ (v1_relat_1 @ X33))),
% 28.92/29.10      inference('cnf', [status(esa)], [t55_funct_1])).
% 28.92/29.10  thf('98', plain,
% 28.92/29.10      (![X30 : $i]:
% 28.92/29.10         ((v1_relat_1 @ (k2_funct_1 @ X30))
% 28.92/29.10          | ~ (v1_funct_1 @ X30)
% 28.92/29.10          | ~ (v1_relat_1 @ X30))),
% 28.92/29.10      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 28.92/29.10  thf('99', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 28.92/29.10      inference('simplify', [status(thm)], ['1'])).
% 28.92/29.10  thf('100', plain,
% 28.92/29.10      (![X30 : $i]:
% 28.92/29.10         ((v1_relat_1 @ (k2_funct_1 @ X30))
% 28.92/29.10          | ~ (v1_funct_1 @ X30)
% 28.92/29.10          | ~ (v1_relat_1 @ X30))),
% 28.92/29.10      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 28.92/29.10  thf('101', plain,
% 28.92/29.10      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 28.92/29.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.92/29.10  thf(redefinition_k2_relset_1, axiom,
% 28.92/29.10    (![A:$i,B:$i,C:$i]:
% 28.92/29.10     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 28.92/29.10       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 28.92/29.10  thf('102', plain,
% 28.92/29.10      (![X43 : $i, X44 : $i, X45 : $i]:
% 28.92/29.10         (((k2_relset_1 @ X44 @ X45 @ X43) = (k2_relat_1 @ X43))
% 28.92/29.10          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45))))),
% 28.92/29.10      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 28.92/29.10  thf('103', plain,
% 28.92/29.10      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 28.92/29.10      inference('sup-', [status(thm)], ['101', '102'])).
% 28.92/29.10  thf('104', plain, (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (sk_B_1))),
% 28.92/29.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.92/29.10  thf('105', plain, (((k2_relat_1 @ sk_C_1) = (sk_B_1))),
% 28.92/29.10      inference('sup+', [status(thm)], ['103', '104'])).
% 28.92/29.10  thf('106', plain,
% 28.92/29.10      (![X33 : $i]:
% 28.92/29.10         (~ (v2_funct_1 @ X33)
% 28.92/29.10          | ((k2_relat_1 @ X33) = (k1_relat_1 @ (k2_funct_1 @ X33)))
% 28.92/29.10          | ~ (v1_funct_1 @ X33)
% 28.92/29.10          | ~ (v1_relat_1 @ X33))),
% 28.92/29.10      inference('cnf', [status(esa)], [t55_funct_1])).
% 28.92/29.10  thf('107', plain,
% 28.92/29.10      (![X22 : $i, X23 : $i]:
% 28.92/29.10         (~ (r1_tarski @ (k1_relat_1 @ X22) @ X23)
% 28.92/29.10          | (v4_relat_1 @ X22 @ X23)
% 28.92/29.10          | ~ (v1_relat_1 @ X22))),
% 28.92/29.10      inference('cnf', [status(esa)], [d18_relat_1])).
% 28.92/29.10  thf('108', plain,
% 28.92/29.10      (![X0 : $i, X1 : $i]:
% 28.92/29.10         (~ (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 28.92/29.10          | ~ (v1_relat_1 @ X0)
% 28.92/29.10          | ~ (v1_funct_1 @ X0)
% 28.92/29.10          | ~ (v2_funct_1 @ X0)
% 28.92/29.10          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 28.92/29.10          | (v4_relat_1 @ (k2_funct_1 @ X0) @ X1))),
% 28.92/29.10      inference('sup-', [status(thm)], ['106', '107'])).
% 28.92/29.10  thf('109', plain,
% 28.92/29.10      (![X0 : $i]:
% 28.92/29.10         (~ (r1_tarski @ sk_B_1 @ X0)
% 28.92/29.10          | (v4_relat_1 @ (k2_funct_1 @ sk_C_1) @ X0)
% 28.92/29.10          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 28.92/29.10          | ~ (v2_funct_1 @ sk_C_1)
% 28.92/29.10          | ~ (v1_funct_1 @ sk_C_1)
% 28.92/29.10          | ~ (v1_relat_1 @ sk_C_1))),
% 28.92/29.10      inference('sup-', [status(thm)], ['105', '108'])).
% 28.92/29.10  thf('110', plain, ((v2_funct_1 @ sk_C_1)),
% 28.92/29.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.92/29.10  thf('111', plain, ((v1_funct_1 @ sk_C_1)),
% 28.92/29.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.92/29.10  thf('112', plain, ((v1_relat_1 @ sk_C_1)),
% 28.92/29.10      inference('sup-', [status(thm)], ['65', '66'])).
% 28.92/29.10  thf('113', plain,
% 28.92/29.10      (![X0 : $i]:
% 28.92/29.10         (~ (r1_tarski @ sk_B_1 @ X0)
% 28.92/29.10          | (v4_relat_1 @ (k2_funct_1 @ sk_C_1) @ X0)
% 28.92/29.10          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 28.92/29.10      inference('demod', [status(thm)], ['109', '110', '111', '112'])).
% 28.92/29.10  thf('114', plain,
% 28.92/29.10      (![X0 : $i]:
% 28.92/29.10         (~ (v1_relat_1 @ sk_C_1)
% 28.92/29.10          | ~ (v1_funct_1 @ sk_C_1)
% 28.92/29.10          | (v4_relat_1 @ (k2_funct_1 @ sk_C_1) @ X0)
% 28.92/29.10          | ~ (r1_tarski @ sk_B_1 @ X0))),
% 28.92/29.10      inference('sup-', [status(thm)], ['100', '113'])).
% 28.92/29.10  thf('115', plain, ((v1_relat_1 @ sk_C_1)),
% 28.92/29.10      inference('sup-', [status(thm)], ['65', '66'])).
% 28.92/29.10  thf('116', plain, ((v1_funct_1 @ sk_C_1)),
% 28.92/29.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.92/29.10  thf('117', plain,
% 28.92/29.10      (![X0 : $i]:
% 28.92/29.10         ((v4_relat_1 @ (k2_funct_1 @ sk_C_1) @ X0)
% 28.92/29.10          | ~ (r1_tarski @ sk_B_1 @ X0))),
% 28.92/29.10      inference('demod', [status(thm)], ['114', '115', '116'])).
% 28.92/29.10  thf('118', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C_1) @ sk_B_1)),
% 28.92/29.10      inference('sup-', [status(thm)], ['99', '117'])).
% 28.92/29.10  thf('119', plain,
% 28.92/29.10      (![X22 : $i, X23 : $i]:
% 28.92/29.10         (~ (v4_relat_1 @ X22 @ X23)
% 28.92/29.10          | (r1_tarski @ (k1_relat_1 @ X22) @ X23)
% 28.92/29.10          | ~ (v1_relat_1 @ X22))),
% 28.92/29.10      inference('cnf', [status(esa)], [d18_relat_1])).
% 28.92/29.10  thf('120', plain,
% 28.92/29.10      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 28.92/29.10        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C_1)) @ sk_B_1))),
% 28.92/29.10      inference('sup-', [status(thm)], ['118', '119'])).
% 28.92/29.10  thf('121', plain,
% 28.92/29.10      ((~ (v1_relat_1 @ sk_C_1)
% 28.92/29.10        | ~ (v1_funct_1 @ sk_C_1)
% 28.92/29.10        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C_1)) @ sk_B_1))),
% 28.92/29.10      inference('sup-', [status(thm)], ['98', '120'])).
% 28.92/29.10  thf('122', plain, ((v1_relat_1 @ sk_C_1)),
% 28.92/29.10      inference('sup-', [status(thm)], ['65', '66'])).
% 28.92/29.10  thf('123', plain, ((v1_funct_1 @ sk_C_1)),
% 28.92/29.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.92/29.10  thf('124', plain,
% 28.92/29.10      ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C_1)) @ sk_B_1)),
% 28.92/29.10      inference('demod', [status(thm)], ['121', '122', '123'])).
% 28.92/29.10  thf('125', plain,
% 28.92/29.10      (![X8 : $i, X10 : $i]:
% 28.92/29.10         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 28.92/29.10      inference('cnf', [status(esa)], [d10_xboole_0])).
% 28.92/29.10  thf('126', plain,
% 28.92/29.10      ((~ (r1_tarski @ sk_B_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))
% 28.92/29.10        | ((sk_B_1) = (k1_relat_1 @ (k2_funct_1 @ sk_C_1))))),
% 28.92/29.10      inference('sup-', [status(thm)], ['124', '125'])).
% 28.92/29.10  thf('127', plain,
% 28.92/29.10      ((~ (r1_tarski @ sk_B_1 @ (k2_relat_1 @ sk_C_1))
% 28.92/29.10        | ~ (v1_relat_1 @ sk_C_1)
% 28.92/29.10        | ~ (v1_funct_1 @ sk_C_1)
% 28.92/29.10        | ~ (v2_funct_1 @ sk_C_1)
% 28.92/29.10        | ((sk_B_1) = (k1_relat_1 @ (k2_funct_1 @ sk_C_1))))),
% 28.92/29.10      inference('sup-', [status(thm)], ['97', '126'])).
% 28.92/29.10  thf('128', plain, (((k2_relat_1 @ sk_C_1) = (sk_B_1))),
% 28.92/29.10      inference('sup+', [status(thm)], ['103', '104'])).
% 28.92/29.10  thf('129', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 28.92/29.10      inference('simplify', [status(thm)], ['1'])).
% 28.92/29.10  thf('130', plain, ((v1_relat_1 @ sk_C_1)),
% 28.92/29.10      inference('sup-', [status(thm)], ['65', '66'])).
% 28.92/29.10  thf('131', plain, ((v1_funct_1 @ sk_C_1)),
% 28.92/29.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.92/29.10  thf('132', plain, ((v2_funct_1 @ sk_C_1)),
% 28.92/29.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.92/29.10  thf('133', plain, (((sk_B_1) = (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 28.92/29.10      inference('demod', [status(thm)],
% 28.92/29.10                ['127', '128', '129', '130', '131', '132'])).
% 28.92/29.10  thf('134', plain,
% 28.92/29.10      (![X0 : $i]: ((v1_xboole_0 @ (k1_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 28.92/29.10      inference('sup-', [status(thm)], ['0', '26'])).
% 28.92/29.10  thf('135', plain,
% 28.92/29.10      (((v1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ (k2_funct_1 @ sk_C_1)))),
% 28.92/29.10      inference('sup+', [status(thm)], ['133', '134'])).
% 28.92/29.10  thf('136', plain,
% 28.92/29.10      ((~ (v2_funct_1 @ sk_C_1)
% 28.92/29.10        | ~ (v1_funct_1 @ sk_C_1)
% 28.92/29.10        | ~ (v1_relat_1 @ sk_C_1)
% 28.92/29.10        | ~ (v1_xboole_0 @ sk_C_1)
% 28.92/29.10        | (v1_xboole_0 @ sk_B_1))),
% 28.92/29.10      inference('sup-', [status(thm)], ['96', '135'])).
% 28.92/29.10  thf('137', plain, ((v2_funct_1 @ sk_C_1)),
% 28.92/29.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.92/29.10  thf('138', plain, ((v1_funct_1 @ sk_C_1)),
% 28.92/29.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.92/29.10  thf('139', plain, ((v1_relat_1 @ sk_C_1)),
% 28.92/29.10      inference('sup-', [status(thm)], ['65', '66'])).
% 28.92/29.10  thf('140', plain, ((~ (v1_xboole_0 @ sk_C_1) | (v1_xboole_0 @ sk_B_1))),
% 28.92/29.10      inference('demod', [status(thm)], ['136', '137', '138', '139'])).
% 28.92/29.10  thf('141', plain,
% 28.92/29.10      (((~ (v1_xboole_0 @ sk_C_1) | ~ (v1_funct_1 @ k1_xboole_0)))
% 28.92/29.10         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 28.92/29.10      inference('clc', [status(thm)], ['95', '140'])).
% 28.92/29.10  thf('142', plain, ((v1_funct_1 @ sk_C_1)),
% 28.92/29.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.92/29.10  thf('143', plain,
% 28.92/29.10      (![X0 : $i]:
% 28.92/29.10         (~ (v2_funct_1 @ X0)
% 28.92/29.10          | ~ (v1_funct_1 @ X0)
% 28.92/29.10          | ~ (v1_relat_1 @ X0)
% 28.92/29.10          | ~ (v1_xboole_0 @ X0)
% 28.92/29.10          | ((k2_funct_1 @ X0) = (k1_xboole_0)))),
% 28.92/29.10      inference('sup-', [status(thm)], ['84', '85'])).
% 28.92/29.10  thf('144', plain,
% 28.92/29.10      (![X30 : $i]:
% 28.92/29.10         ((v1_funct_1 @ (k2_funct_1 @ X30))
% 28.92/29.10          | ~ (v1_funct_1 @ X30)
% 28.92/29.10          | ~ (v1_relat_1 @ X30))),
% 28.92/29.10      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 28.92/29.10  thf('145', plain,
% 28.92/29.10      (![X0 : $i]:
% 28.92/29.10         ((v1_funct_1 @ k1_xboole_0)
% 28.92/29.10          | ~ (v1_xboole_0 @ X0)
% 28.92/29.10          | ~ (v1_relat_1 @ X0)
% 28.92/29.10          | ~ (v1_funct_1 @ X0)
% 28.92/29.10          | ~ (v2_funct_1 @ X0)
% 28.92/29.10          | ~ (v1_relat_1 @ X0)
% 28.92/29.10          | ~ (v1_funct_1 @ X0))),
% 28.92/29.10      inference('sup+', [status(thm)], ['143', '144'])).
% 28.92/29.10  thf('146', plain,
% 28.92/29.10      (![X0 : $i]:
% 28.92/29.10         (~ (v2_funct_1 @ X0)
% 28.92/29.10          | ~ (v1_funct_1 @ X0)
% 28.92/29.10          | ~ (v1_relat_1 @ X0)
% 28.92/29.10          | ~ (v1_xboole_0 @ X0)
% 28.92/29.10          | (v1_funct_1 @ k1_xboole_0))),
% 28.92/29.10      inference('simplify', [status(thm)], ['145'])).
% 28.92/29.10  thf('147', plain,
% 28.92/29.10      (((v1_funct_1 @ k1_xboole_0)
% 28.92/29.10        | ~ (v1_xboole_0 @ sk_C_1)
% 28.92/29.10        | ~ (v1_relat_1 @ sk_C_1)
% 28.92/29.10        | ~ (v2_funct_1 @ sk_C_1))),
% 28.92/29.10      inference('sup-', [status(thm)], ['142', '146'])).
% 28.92/29.10  thf('148', plain, ((v1_relat_1 @ sk_C_1)),
% 28.92/29.10      inference('sup-', [status(thm)], ['65', '66'])).
% 28.92/29.10  thf('149', plain, ((v2_funct_1 @ sk_C_1)),
% 28.92/29.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.92/29.10  thf('150', plain, (((v1_funct_1 @ k1_xboole_0) | ~ (v1_xboole_0 @ sk_C_1))),
% 28.92/29.10      inference('demod', [status(thm)], ['147', '148', '149'])).
% 28.92/29.10  thf('151', plain,
% 28.92/29.10      ((~ (v1_xboole_0 @ sk_C_1))
% 28.92/29.10         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 28.92/29.10      inference('clc', [status(thm)], ['141', '150'])).
% 28.92/29.10  thf('152', plain,
% 28.92/29.10      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 28.92/29.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.92/29.10  thf('153', plain,
% 28.92/29.10      (![X37 : $i, X38 : $i, X39 : $i]:
% 28.92/29.10         ((v4_relat_1 @ X37 @ X38)
% 28.92/29.10          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 28.92/29.10      inference('cnf', [status(esa)], [cc2_relset_1])).
% 28.92/29.10  thf('154', plain, ((v4_relat_1 @ sk_C_1 @ sk_A)),
% 28.92/29.10      inference('sup-', [status(thm)], ['152', '153'])).
% 28.92/29.10  thf('155', plain,
% 28.92/29.10      (![X22 : $i, X23 : $i]:
% 28.92/29.10         (~ (v4_relat_1 @ X22 @ X23)
% 28.92/29.10          | (r1_tarski @ (k1_relat_1 @ X22) @ X23)
% 28.92/29.10          | ~ (v1_relat_1 @ X22))),
% 28.92/29.10      inference('cnf', [status(esa)], [d18_relat_1])).
% 28.92/29.10  thf('156', plain,
% 28.92/29.10      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_A))),
% 28.92/29.10      inference('sup-', [status(thm)], ['154', '155'])).
% 28.92/29.10  thf('157', plain, ((v1_relat_1 @ sk_C_1)),
% 28.92/29.10      inference('sup-', [status(thm)], ['65', '66'])).
% 28.92/29.10  thf('158', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_A)),
% 28.92/29.10      inference('demod', [status(thm)], ['156', '157'])).
% 28.92/29.10  thf('159', plain,
% 28.92/29.10      (![X30 : $i]:
% 28.92/29.10         ((v1_funct_1 @ (k2_funct_1 @ X30))
% 28.92/29.10          | ~ (v1_funct_1 @ X30)
% 28.92/29.10          | ~ (v1_relat_1 @ X30))),
% 28.92/29.10      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 28.92/29.10  thf('160', plain,
% 28.92/29.10      (![X33 : $i]:
% 28.92/29.10         (~ (v2_funct_1 @ X33)
% 28.92/29.10          | ((k1_relat_1 @ X33) = (k2_relat_1 @ (k2_funct_1 @ X33)))
% 28.92/29.10          | ~ (v1_funct_1 @ X33)
% 28.92/29.10          | ~ (v1_relat_1 @ X33))),
% 28.92/29.10      inference('cnf', [status(esa)], [t55_funct_1])).
% 28.92/29.10  thf('161', plain,
% 28.92/29.10      (![X30 : $i]:
% 28.92/29.10         ((v1_funct_1 @ (k2_funct_1 @ X30))
% 28.92/29.10          | ~ (v1_funct_1 @ X30)
% 28.92/29.10          | ~ (v1_relat_1 @ X30))),
% 28.92/29.10      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 28.92/29.10  thf('162', plain,
% 28.92/29.10      (![X30 : $i]:
% 28.92/29.10         ((v1_relat_1 @ (k2_funct_1 @ X30))
% 28.92/29.10          | ~ (v1_funct_1 @ X30)
% 28.92/29.10          | ~ (v1_relat_1 @ X30))),
% 28.92/29.10      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 28.92/29.10  thf('163', plain, (((sk_B_1) = (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 28.92/29.10      inference('demod', [status(thm)],
% 28.92/29.10                ['127', '128', '129', '130', '131', '132'])).
% 28.92/29.10  thf('164', plain,
% 28.92/29.10      (![X52 : $i]:
% 28.92/29.10         ((m1_subset_1 @ X52 @ 
% 28.92/29.10           (k1_zfmisc_1 @ 
% 28.92/29.10            (k2_zfmisc_1 @ (k1_relat_1 @ X52) @ (k2_relat_1 @ X52))))
% 28.92/29.10          | ~ (v1_funct_1 @ X52)
% 28.92/29.10          | ~ (v1_relat_1 @ X52))),
% 28.92/29.10      inference('cnf', [status(esa)], [t3_funct_2])).
% 28.92/29.10  thf('165', plain,
% 28.92/29.10      (((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 28.92/29.10         (k1_zfmisc_1 @ 
% 28.92/29.10          (k2_zfmisc_1 @ sk_B_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))))
% 28.92/29.10        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 28.92/29.10        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 28.92/29.10      inference('sup+', [status(thm)], ['163', '164'])).
% 28.92/29.10  thf('166', plain,
% 28.92/29.10      ((~ (v1_relat_1 @ sk_C_1)
% 28.92/29.10        | ~ (v1_funct_1 @ sk_C_1)
% 28.92/29.10        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 28.92/29.10        | (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 28.92/29.10           (k1_zfmisc_1 @ 
% 28.92/29.10            (k2_zfmisc_1 @ sk_B_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C_1))))))),
% 28.92/29.10      inference('sup-', [status(thm)], ['162', '165'])).
% 28.92/29.10  thf('167', plain, ((v1_relat_1 @ sk_C_1)),
% 28.92/29.10      inference('sup-', [status(thm)], ['65', '66'])).
% 28.92/29.10  thf('168', plain, ((v1_funct_1 @ sk_C_1)),
% 28.92/29.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.92/29.10  thf('169', plain,
% 28.92/29.10      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 28.92/29.10        | (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 28.92/29.10           (k1_zfmisc_1 @ 
% 28.92/29.10            (k2_zfmisc_1 @ sk_B_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C_1))))))),
% 28.92/29.10      inference('demod', [status(thm)], ['166', '167', '168'])).
% 28.92/29.10  thf('170', plain,
% 28.92/29.10      ((~ (v1_relat_1 @ sk_C_1)
% 28.92/29.10        | ~ (v1_funct_1 @ sk_C_1)
% 28.92/29.10        | (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 28.92/29.10           (k1_zfmisc_1 @ 
% 28.92/29.10            (k2_zfmisc_1 @ sk_B_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C_1))))))),
% 28.92/29.10      inference('sup-', [status(thm)], ['161', '169'])).
% 28.92/29.10  thf('171', plain, ((v1_relat_1 @ sk_C_1)),
% 28.92/29.10      inference('sup-', [status(thm)], ['65', '66'])).
% 28.92/29.10  thf('172', plain, ((v1_funct_1 @ sk_C_1)),
% 28.92/29.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.92/29.10  thf('173', plain,
% 28.92/29.10      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 28.92/29.10        (k1_zfmisc_1 @ 
% 28.92/29.10         (k2_zfmisc_1 @ sk_B_1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))))),
% 28.92/29.10      inference('demod', [status(thm)], ['170', '171', '172'])).
% 28.92/29.10  thf('174', plain,
% 28.92/29.10      (((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 28.92/29.10         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ (k1_relat_1 @ sk_C_1))))
% 28.92/29.10        | ~ (v1_relat_1 @ sk_C_1)
% 28.92/29.10        | ~ (v1_funct_1 @ sk_C_1)
% 28.92/29.10        | ~ (v2_funct_1 @ sk_C_1))),
% 28.92/29.10      inference('sup+', [status(thm)], ['160', '173'])).
% 28.92/29.10  thf('175', plain, ((v1_relat_1 @ sk_C_1)),
% 28.92/29.10      inference('sup-', [status(thm)], ['65', '66'])).
% 28.92/29.10  thf('176', plain, ((v1_funct_1 @ sk_C_1)),
% 28.92/29.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.92/29.10  thf('177', plain, ((v2_funct_1 @ sk_C_1)),
% 28.92/29.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.92/29.10  thf('178', plain,
% 28.92/29.10      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 28.92/29.10        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ (k1_relat_1 @ sk_C_1))))),
% 28.92/29.10      inference('demod', [status(thm)], ['174', '175', '176', '177'])).
% 28.92/29.10  thf(t9_funct_2, axiom,
% 28.92/29.10    (![A:$i,B:$i,C:$i,D:$i]:
% 28.92/29.10     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 28.92/29.10         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 28.92/29.10       ( ( r1_tarski @ B @ C ) =>
% 28.92/29.10         ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 28.92/29.10             ( v1_funct_2 @ D @ A @ C ) & ( v1_funct_1 @ D ) ) | 
% 28.92/29.10           ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 28.92/29.10  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 28.92/29.10  thf(zf_stmt_2, axiom,
% 28.92/29.10    (![B:$i,A:$i]:
% 28.92/29.10     ( ( zip_tseitin_1 @ B @ A ) =>
% 28.92/29.10       ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) ))).
% 28.92/29.10  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $i > $o).
% 28.92/29.10  thf(zf_stmt_4, axiom,
% 28.92/29.10    (![D:$i,C:$i,A:$i]:
% 28.92/29.10     ( ( zip_tseitin_0 @ D @ C @ A ) =>
% 28.92/29.10       ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 28.92/29.10         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ))).
% 28.92/29.10  thf(zf_stmt_5, axiom,
% 28.92/29.10    (![A:$i,B:$i,C:$i,D:$i]:
% 28.92/29.10     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 28.92/29.10         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 28.92/29.10       ( ( r1_tarski @ B @ C ) =>
% 28.92/29.10         ( ( zip_tseitin_1 @ B @ A ) | ( zip_tseitin_0 @ D @ C @ A ) ) ) ))).
% 28.92/29.10  thf('179', plain,
% 28.92/29.10      (![X58 : $i, X59 : $i, X60 : $i, X61 : $i]:
% 28.92/29.10         (~ (r1_tarski @ X58 @ X59)
% 28.92/29.10          | (zip_tseitin_1 @ X58 @ X60)
% 28.92/29.10          | ~ (v1_funct_1 @ X61)
% 28.92/29.10          | ~ (v1_funct_2 @ X61 @ X60 @ X58)
% 28.92/29.10          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X60 @ X58)))
% 28.92/29.10          | (zip_tseitin_0 @ X61 @ X59 @ X60))),
% 28.92/29.10      inference('cnf', [status(esa)], [zf_stmt_5])).
% 28.92/29.10  thf('180', plain,
% 28.92/29.10      (![X0 : $i]:
% 28.92/29.10         ((zip_tseitin_0 @ (k2_funct_1 @ sk_C_1) @ X0 @ sk_B_1)
% 28.92/29.10          | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ 
% 28.92/29.10               (k1_relat_1 @ sk_C_1))
% 28.92/29.10          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 28.92/29.10          | (zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B_1)
% 28.92/29.10          | ~ (r1_tarski @ (k1_relat_1 @ sk_C_1) @ X0))),
% 28.92/29.10      inference('sup-', [status(thm)], ['178', '179'])).
% 28.92/29.10  thf('181', plain,
% 28.92/29.10      (![X33 : $i]:
% 28.92/29.10         (~ (v2_funct_1 @ X33)
% 28.92/29.10          | ((k1_relat_1 @ X33) = (k2_relat_1 @ (k2_funct_1 @ X33)))
% 28.92/29.10          | ~ (v1_funct_1 @ X33)
% 28.92/29.10          | ~ (v1_relat_1 @ X33))),
% 28.92/29.10      inference('cnf', [status(esa)], [t55_funct_1])).
% 28.92/29.10  thf('182', plain,
% 28.92/29.10      (![X30 : $i]:
% 28.92/29.10         ((v1_funct_1 @ (k2_funct_1 @ X30))
% 28.92/29.10          | ~ (v1_funct_1 @ X30)
% 28.92/29.10          | ~ (v1_relat_1 @ X30))),
% 28.92/29.10      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 28.92/29.10  thf('183', plain,
% 28.92/29.10      (![X30 : $i]:
% 28.92/29.10         ((v1_relat_1 @ (k2_funct_1 @ X30))
% 28.92/29.10          | ~ (v1_funct_1 @ X30)
% 28.92/29.10          | ~ (v1_relat_1 @ X30))),
% 28.92/29.10      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 28.92/29.10  thf('184', plain, (((sk_B_1) = (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 28.92/29.10      inference('demod', [status(thm)],
% 28.92/29.10                ['127', '128', '129', '130', '131', '132'])).
% 28.92/29.10  thf('185', plain,
% 28.92/29.10      (![X52 : $i]:
% 28.92/29.10         ((v1_funct_2 @ X52 @ (k1_relat_1 @ X52) @ (k2_relat_1 @ X52))
% 28.92/29.10          | ~ (v1_funct_1 @ X52)
% 28.92/29.10          | ~ (v1_relat_1 @ X52))),
% 28.92/29.10      inference('cnf', [status(esa)], [t3_funct_2])).
% 28.92/29.10  thf('186', plain,
% 28.92/29.10      (((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ 
% 28.92/29.10         (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))
% 28.92/29.10        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 28.92/29.10        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 28.92/29.10      inference('sup+', [status(thm)], ['184', '185'])).
% 28.92/29.10  thf('187', plain,
% 28.92/29.10      ((~ (v1_relat_1 @ sk_C_1)
% 28.92/29.10        | ~ (v1_funct_1 @ sk_C_1)
% 28.92/29.10        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 28.92/29.10        | (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ 
% 28.92/29.10           (k2_relat_1 @ (k2_funct_1 @ sk_C_1))))),
% 28.92/29.10      inference('sup-', [status(thm)], ['183', '186'])).
% 28.92/29.10  thf('188', plain, ((v1_relat_1 @ sk_C_1)),
% 28.92/29.10      inference('sup-', [status(thm)], ['65', '66'])).
% 28.92/29.10  thf('189', plain, ((v1_funct_1 @ sk_C_1)),
% 28.92/29.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.92/29.10  thf('190', plain,
% 28.92/29.10      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 28.92/29.10        | (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ 
% 28.92/29.10           (k2_relat_1 @ (k2_funct_1 @ sk_C_1))))),
% 28.92/29.10      inference('demod', [status(thm)], ['187', '188', '189'])).
% 28.92/29.10  thf('191', plain,
% 28.92/29.10      ((~ (v1_relat_1 @ sk_C_1)
% 28.92/29.10        | ~ (v1_funct_1 @ sk_C_1)
% 28.92/29.10        | (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ 
% 28.92/29.10           (k2_relat_1 @ (k2_funct_1 @ sk_C_1))))),
% 28.92/29.10      inference('sup-', [status(thm)], ['182', '190'])).
% 28.92/29.10  thf('192', plain, ((v1_relat_1 @ sk_C_1)),
% 28.92/29.10      inference('sup-', [status(thm)], ['65', '66'])).
% 28.92/29.10  thf('193', plain, ((v1_funct_1 @ sk_C_1)),
% 28.92/29.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.92/29.10  thf('194', plain,
% 28.92/29.10      ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ 
% 28.92/29.10        (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 28.92/29.10      inference('demod', [status(thm)], ['191', '192', '193'])).
% 28.92/29.10  thf('195', plain,
% 28.92/29.10      (((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ (k1_relat_1 @ sk_C_1))
% 28.92/29.10        | ~ (v1_relat_1 @ sk_C_1)
% 28.92/29.10        | ~ (v1_funct_1 @ sk_C_1)
% 28.92/29.10        | ~ (v2_funct_1 @ sk_C_1))),
% 28.92/29.10      inference('sup+', [status(thm)], ['181', '194'])).
% 28.92/29.10  thf('196', plain, ((v1_relat_1 @ sk_C_1)),
% 28.92/29.10      inference('sup-', [status(thm)], ['65', '66'])).
% 28.92/29.10  thf('197', plain, ((v1_funct_1 @ sk_C_1)),
% 28.92/29.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.92/29.10  thf('198', plain, ((v2_funct_1 @ sk_C_1)),
% 28.92/29.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.92/29.10  thf('199', plain,
% 28.92/29.10      ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ (k1_relat_1 @ sk_C_1))),
% 28.92/29.10      inference('demod', [status(thm)], ['195', '196', '197', '198'])).
% 28.92/29.10  thf('200', plain,
% 28.92/29.10      (![X0 : $i]:
% 28.92/29.10         ((zip_tseitin_0 @ (k2_funct_1 @ sk_C_1) @ X0 @ sk_B_1)
% 28.92/29.10          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 28.92/29.10          | (zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B_1)
% 28.92/29.10          | ~ (r1_tarski @ (k1_relat_1 @ sk_C_1) @ X0))),
% 28.92/29.10      inference('demod', [status(thm)], ['180', '199'])).
% 28.92/29.10  thf('201', plain,
% 28.92/29.10      (![X0 : $i]:
% 28.92/29.10         (~ (v1_relat_1 @ sk_C_1)
% 28.92/29.10          | ~ (v1_funct_1 @ sk_C_1)
% 28.92/29.10          | ~ (r1_tarski @ (k1_relat_1 @ sk_C_1) @ X0)
% 28.92/29.10          | (zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B_1)
% 28.92/29.10          | (zip_tseitin_0 @ (k2_funct_1 @ sk_C_1) @ X0 @ sk_B_1))),
% 28.92/29.10      inference('sup-', [status(thm)], ['159', '200'])).
% 28.92/29.10  thf('202', plain, ((v1_relat_1 @ sk_C_1)),
% 28.92/29.10      inference('sup-', [status(thm)], ['65', '66'])).
% 28.92/29.10  thf('203', plain, ((v1_funct_1 @ sk_C_1)),
% 28.92/29.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.92/29.10  thf('204', plain,
% 28.92/29.10      (![X0 : $i]:
% 28.92/29.10         (~ (r1_tarski @ (k1_relat_1 @ sk_C_1) @ X0)
% 28.92/29.10          | (zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B_1)
% 28.92/29.10          | (zip_tseitin_0 @ (k2_funct_1 @ sk_C_1) @ X0 @ sk_B_1))),
% 28.92/29.10      inference('demod', [status(thm)], ['201', '202', '203'])).
% 28.92/29.10  thf('205', plain,
% 28.92/29.10      (((zip_tseitin_0 @ (k2_funct_1 @ sk_C_1) @ sk_A @ sk_B_1)
% 28.92/29.10        | (zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B_1))),
% 28.92/29.10      inference('sup-', [status(thm)], ['158', '204'])).
% 28.92/29.10  thf('206', plain,
% 28.92/29.10      (![X53 : $i, X54 : $i, X55 : $i]:
% 28.92/29.10         ((v1_funct_2 @ X53 @ X55 @ X54) | ~ (zip_tseitin_0 @ X53 @ X54 @ X55))),
% 28.92/29.10      inference('cnf', [status(esa)], [zf_stmt_4])).
% 28.92/29.10  thf('207', plain,
% 28.92/29.10      (((zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B_1)
% 28.92/29.10        | (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A))),
% 28.92/29.10      inference('sup-', [status(thm)], ['205', '206'])).
% 28.92/29.10  thf('208', plain,
% 28.92/29.10      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A))
% 28.92/29.10         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 28.92/29.10      inference('split', [status(esa)], ['59'])).
% 28.92/29.10  thf('209', plain,
% 28.92/29.10      (((zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B_1))
% 28.92/29.10         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 28.92/29.10      inference('sup-', [status(thm)], ['207', '208'])).
% 28.92/29.10  thf('210', plain,
% 28.92/29.10      (![X56 : $i, X57 : $i]:
% 28.92/29.10         (((X56) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X56 @ X57))),
% 28.92/29.10      inference('cnf', [status(esa)], [zf_stmt_2])).
% 28.92/29.10  thf('211', plain,
% 28.92/29.10      ((((k1_relat_1 @ sk_C_1) = (k1_xboole_0)))
% 28.92/29.10         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 28.92/29.10      inference('sup-', [status(thm)], ['209', '210'])).
% 28.92/29.10  thf('212', plain,
% 28.92/29.10      (![X52 : $i]:
% 28.92/29.10         ((m1_subset_1 @ X52 @ 
% 28.92/29.10           (k1_zfmisc_1 @ 
% 28.92/29.10            (k2_zfmisc_1 @ (k1_relat_1 @ X52) @ (k2_relat_1 @ X52))))
% 28.92/29.10          | ~ (v1_funct_1 @ X52)
% 28.92/29.10          | ~ (v1_relat_1 @ X52))),
% 28.92/29.10      inference('cnf', [status(esa)], [t3_funct_2])).
% 28.92/29.10  thf('213', plain,
% 28.92/29.10      (![X16 : $i, X17 : $i]:
% 28.92/29.10         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 28.92/29.10      inference('cnf', [status(esa)], [t3_subset])).
% 28.92/29.10  thf('214', plain,
% 28.92/29.10      (![X0 : $i]:
% 28.92/29.10         (~ (v1_relat_1 @ X0)
% 28.92/29.10          | ~ (v1_funct_1 @ X0)
% 28.92/29.10          | (r1_tarski @ X0 @ 
% 28.92/29.10             (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 28.92/29.10      inference('sup-', [status(thm)], ['212', '213'])).
% 28.92/29.10  thf('215', plain,
% 28.92/29.10      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 28.92/29.10      inference('cnf', [status(esa)], [l13_xboole_0])).
% 28.92/29.10  thf('216', plain,
% 28.92/29.10      (![X14 : $i]: ((k2_zfmisc_1 @ X14 @ k1_xboole_0) = (k1_xboole_0))),
% 28.92/29.10      inference('simplify', [status(thm)], ['32'])).
% 28.92/29.10  thf('217', plain,
% 28.92/29.10      (![X0 : $i, X1 : $i]: (v4_relat_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X1)),
% 28.92/29.10      inference('sup-', [status(thm)], ['11', '12'])).
% 28.92/29.10  thf('218', plain, (![X0 : $i]: (v4_relat_1 @ k1_xboole_0 @ X0)),
% 28.92/29.10      inference('sup+', [status(thm)], ['216', '217'])).
% 28.92/29.10  thf('219', plain,
% 28.92/29.10      (![X22 : $i, X23 : $i]:
% 28.92/29.10         (~ (v4_relat_1 @ X22 @ X23)
% 28.92/29.10          | (r1_tarski @ (k1_relat_1 @ X22) @ X23)
% 28.92/29.10          | ~ (v1_relat_1 @ X22))),
% 28.92/29.10      inference('cnf', [status(esa)], [d18_relat_1])).
% 28.92/29.10  thf('220', plain,
% 28.92/29.10      (![X0 : $i]:
% 28.92/29.10         (~ (v1_relat_1 @ k1_xboole_0)
% 28.92/29.10          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 28.92/29.10      inference('sup-', [status(thm)], ['218', '219'])).
% 28.92/29.10  thf('221', plain,
% 28.92/29.10      (![X14 : $i]: ((k2_zfmisc_1 @ X14 @ k1_xboole_0) = (k1_xboole_0))),
% 28.92/29.10      inference('simplify', [status(thm)], ['32'])).
% 28.92/29.10  thf('222', plain,
% 28.92/29.10      (![X0 : $i, X1 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))),
% 28.92/29.10      inference('sup-', [status(thm)], ['16', '17'])).
% 28.92/29.10  thf('223', plain, ((v1_relat_1 @ k1_xboole_0)),
% 28.92/29.10      inference('sup+', [status(thm)], ['221', '222'])).
% 28.92/29.10  thf('224', plain,
% 28.92/29.10      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 28.92/29.10      inference('demod', [status(thm)], ['220', '223'])).
% 28.92/29.10  thf('225', plain,
% 28.92/29.10      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 28.92/29.10      inference('demod', [status(thm)], ['220', '223'])).
% 28.92/29.10  thf('226', plain,
% 28.92/29.10      (![X16 : $i, X18 : $i]:
% 28.92/29.10         ((m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X18)) | ~ (r1_tarski @ X16 @ X18))),
% 28.92/29.10      inference('cnf', [status(esa)], [t3_subset])).
% 28.92/29.10  thf('227', plain,
% 28.92/29.10      (![X0 : $i]:
% 28.92/29.10         (m1_subset_1 @ (k1_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 28.92/29.10      inference('sup-', [status(thm)], ['225', '226'])).
% 28.92/29.10  thf('228', plain,
% 28.92/29.10      (![X1 : $i]:
% 28.92/29.10         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 28.92/29.10          | (v1_xboole_0 @ X1))),
% 28.92/29.10      inference('demod', [status(thm)], ['40', '41'])).
% 28.92/29.10  thf('229', plain, ((v1_xboole_0 @ (k1_relat_1 @ k1_xboole_0))),
% 28.92/29.10      inference('sup-', [status(thm)], ['227', '228'])).
% 28.92/29.10  thf('230', plain,
% 28.92/29.10      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 28.92/29.10      inference('cnf', [status(esa)], [l13_xboole_0])).
% 28.92/29.10  thf('231', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 28.92/29.10      inference('sup-', [status(thm)], ['229', '230'])).
% 28.92/29.10  thf('232', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 28.92/29.10      inference('demod', [status(thm)], ['224', '231'])).
% 28.92/29.10  thf('233', plain,
% 28.92/29.10      (![X8 : $i, X10 : $i]:
% 28.92/29.10         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 28.92/29.10      inference('cnf', [status(esa)], [d10_xboole_0])).
% 28.92/29.10  thf('234', plain,
% 28.92/29.10      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 28.92/29.10      inference('sup-', [status(thm)], ['232', '233'])).
% 28.92/29.10  thf('235', plain,
% 28.92/29.10      (![X0 : $i, X1 : $i]:
% 28.92/29.10         (~ (r1_tarski @ X1 @ X0)
% 28.92/29.10          | ~ (v1_xboole_0 @ X0)
% 28.92/29.10          | ((X1) = (k1_xboole_0)))),
% 28.92/29.10      inference('sup-', [status(thm)], ['215', '234'])).
% 28.92/29.10  thf('236', plain,
% 28.92/29.10      (![X0 : $i]:
% 28.92/29.10         (~ (v1_funct_1 @ X0)
% 28.92/29.10          | ~ (v1_relat_1 @ X0)
% 28.92/29.10          | ((X0) = (k1_xboole_0))
% 28.92/29.10          | ~ (v1_xboole_0 @ 
% 28.92/29.10               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 28.92/29.10      inference('sup-', [status(thm)], ['214', '235'])).
% 28.92/29.10  thf('237', plain,
% 28.92/29.10      (((~ (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ (k2_relat_1 @ sk_C_1)))
% 28.92/29.10         | ((sk_C_1) = (k1_xboole_0))
% 28.92/29.10         | ~ (v1_relat_1 @ sk_C_1)
% 28.92/29.10         | ~ (v1_funct_1 @ sk_C_1)))
% 28.92/29.10         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 28.92/29.10      inference('sup-', [status(thm)], ['211', '236'])).
% 28.92/29.10  thf('238', plain, (((k2_relat_1 @ sk_C_1) = (sk_B_1))),
% 28.92/29.10      inference('sup+', [status(thm)], ['103', '104'])).
% 28.92/29.10  thf('239', plain,
% 28.92/29.10      (![X15 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X15) = (k1_xboole_0))),
% 28.92/29.10      inference('simplify', [status(thm)], ['37'])).
% 28.92/29.10  thf('240', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 28.92/29.10      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 28.92/29.10  thf('241', plain, ((v1_relat_1 @ sk_C_1)),
% 28.92/29.10      inference('sup-', [status(thm)], ['65', '66'])).
% 28.92/29.10  thf('242', plain, ((v1_funct_1 @ sk_C_1)),
% 28.92/29.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.92/29.10  thf('243', plain,
% 28.92/29.10      ((((sk_C_1) = (k1_xboole_0)))
% 28.92/29.10         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)))),
% 28.92/29.10      inference('demod', [status(thm)],
% 28.92/29.10                ['237', '238', '239', '240', '241', '242'])).
% 28.92/29.10  thf('244', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 28.92/29.10      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 28.92/29.10  thf('245', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A))),
% 28.92/29.10      inference('demod', [status(thm)], ['151', '243', '244'])).
% 28.92/29.10  thf('246', plain,
% 28.92/29.10      (~
% 28.92/29.10       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 28.92/29.10         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))) | 
% 28.92/29.10       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B_1 @ sk_A)) | 
% 28.92/29.10       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 28.92/29.10      inference('split', [status(esa)], ['59'])).
% 28.92/29.10  thf('247', plain,
% 28.92/29.10      (~
% 28.92/29.10       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 28.92/29.10         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))),
% 28.92/29.10      inference('sat_resolution*', [status(thm)], ['75', '245', '246'])).
% 28.92/29.10  thf('248', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 28.92/29.10      inference('simpl_trail', [status(thm)], ['68', '247'])).
% 28.92/29.10  thf('249', plain, (((k2_relat_1 @ sk_C_1) = (sk_B_1))),
% 28.92/29.10      inference('sup+', [status(thm)], ['103', '104'])).
% 28.92/29.10  thf('250', plain,
% 28.92/29.10      (![X52 : $i]:
% 28.92/29.10         ((m1_subset_1 @ X52 @ 
% 28.92/29.10           (k1_zfmisc_1 @ 
% 28.92/29.10            (k2_zfmisc_1 @ (k1_relat_1 @ X52) @ (k2_relat_1 @ X52))))
% 28.92/29.10          | ~ (v1_funct_1 @ X52)
% 28.92/29.10          | ~ (v1_relat_1 @ X52))),
% 28.92/29.10      inference('cnf', [status(esa)], [t3_funct_2])).
% 28.92/29.10  thf('251', plain,
% 28.92/29.10      (((m1_subset_1 @ sk_C_1 @ 
% 28.92/29.10         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ sk_B_1)))
% 28.92/29.10        | ~ (v1_relat_1 @ sk_C_1)
% 28.92/29.10        | ~ (v1_funct_1 @ sk_C_1))),
% 28.92/29.10      inference('sup+', [status(thm)], ['249', '250'])).
% 28.92/29.10  thf('252', plain, ((v1_relat_1 @ sk_C_1)),
% 28.92/29.10      inference('sup-', [status(thm)], ['65', '66'])).
% 28.92/29.10  thf('253', plain, ((v1_funct_1 @ sk_C_1)),
% 28.92/29.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 28.92/29.10  thf('254', plain,
% 28.92/29.10      ((m1_subset_1 @ sk_C_1 @ 
% 28.92/29.10        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ sk_B_1)))),
% 28.92/29.10      inference('demod', [status(thm)], ['251', '252', '253'])).
% 28.92/29.10  thf('255', plain,
% 28.92/29.10      (![X40 : $i, X41 : $i, X42 : $i]:
% 28.92/29.10         (~ (v1_xboole_0 @ X40)
% 28.92/29.10          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X42)))
% 28.92/29.10          | (v1_xboole_0 @ X41))),
% 28.92/29.10      inference('cnf', [status(esa)], [cc3_relset_1])).
% 28.92/29.10  thf('256', plain,
% 28.92/29.10      (((v1_xboole_0 @ sk_C_1) | ~ (v1_xboole_0 @ (k1_relat_1 @ sk_C_1)))),
% 28.92/29.10      inference('sup-', [status(thm)], ['254', '255'])).
% 28.92/29.10  thf('257', plain,
% 28.92/29.10      (((zip_tseitin_0 @ (k2_funct_1 @ sk_C_1) @ sk_A @ sk_B_1)
% 28.92/29.10        | (zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B_1))),
% 28.92/29.10      inference('sup-', [status(thm)], ['158', '204'])).
% 28.92/29.10  thf('258', plain,
% 28.92/29.10      (![X53 : $i, X54 : $i, X55 : $i]:
% 28.92/29.10         ((m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X54)))
% 28.92/29.10          | ~ (zip_tseitin_0 @ X53 @ X54 @ X55))),
% 28.92/29.10      inference('cnf', [status(esa)], [zf_stmt_4])).
% 28.92/29.10  thf('259', plain,
% 28.92/29.10      (((zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B_1)
% 28.92/29.10        | (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 28.92/29.10           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))),
% 28.92/29.10      inference('sup-', [status(thm)], ['257', '258'])).
% 28.92/29.10  thf('260', plain,
% 28.92/29.10      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 28.92/29.10           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))
% 28.92/29.10         <= (~
% 28.92/29.10             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 28.92/29.10               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 28.92/29.10      inference('split', [status(esa)], ['59'])).
% 28.92/29.10  thf('261', plain,
% 28.92/29.10      (~
% 28.92/29.10       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 28.92/29.10         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))),
% 28.92/29.10      inference('sat_resolution*', [status(thm)], ['75', '245', '246'])).
% 28.92/29.10  thf('262', plain,
% 28.92/29.10      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 28.92/29.10          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 28.92/29.10      inference('simpl_trail', [status(thm)], ['260', '261'])).
% 28.92/29.10  thf('263', plain, ((zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B_1)),
% 28.92/29.10      inference('clc', [status(thm)], ['259', '262'])).
% 28.92/29.10  thf('264', plain,
% 28.92/29.10      (![X56 : $i, X57 : $i]:
% 28.92/29.10         (((X56) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X56 @ X57))),
% 28.92/29.10      inference('cnf', [status(esa)], [zf_stmt_2])).
% 28.92/29.10  thf('265', plain, (((k1_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 28.92/29.10      inference('sup-', [status(thm)], ['263', '264'])).
% 28.92/29.10  thf('266', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 28.92/29.10      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 28.92/29.10  thf('267', plain, ((v1_xboole_0 @ sk_C_1)),
% 28.92/29.10      inference('demod', [status(thm)], ['256', '265', '266'])).
% 28.92/29.10  thf('268', plain, ($false), inference('demod', [status(thm)], ['248', '267'])).
% 28.92/29.10  
% 28.92/29.10  % SZS output end Refutation
% 28.92/29.10  
% 28.92/29.11  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
