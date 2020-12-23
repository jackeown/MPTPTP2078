%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iqxTT5vQnA

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:43 EST 2020

% Result     : Theorem 3.97s
% Output     : Refutation 3.97s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 457 expanded)
%              Number of leaves         :   31 ( 149 expanded)
%              Depth                    :   16
%              Number of atoms          :  811 (4163 expanded)
%              Number of equality atoms :   55 ( 177 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t3_funct_2,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ( v1_funct_1 @ A )
          & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
          & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t3_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
   <= ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_A )
   <= ~ ( v1_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('4',plain,(
    v1_funct_1 @ sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X11: $i] :
      ( ( r1_tarski @ X11 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X11 ) @ ( k2_relat_1 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) )
   <= ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_A )
   <= ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('13',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['4','11','12'])).

thf('14',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['1','13'])).

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

thf('15',plain,(
    ! [X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('16',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('17',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X11: $i] :
      ( ( r1_tarski @ X11 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X11 ) @ ( k2_relat_1 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('20',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(rc2_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ( v1_xboole_0 @ B )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('21',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ ( sk_B @ X7 ) @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf('22',plain,(
    ! [X7: $i] :
      ( v1_xboole_0 @ ( sk_B @ X7 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( sk_B @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['19','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','31'])).

thf('33',plain,(
    ! [X7: $i] :
      ( v1_xboole_0 @ ( sk_B @ X7 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( sk_B @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('35',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

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

thf('38',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( zip_tseitin_0 @ X23 @ X24 )
      | ( zip_tseitin_1 @ X25 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0 = k1_xboole_0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('43',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( X20
       != ( k1_relset_1 @ X20 @ X21 @ X22 ) )
      | ( v1_funct_2 @ X22 @ X20 @ X21 )
      | ~ ( zip_tseitin_1 @ X22 @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['1','13'])).

thf('51',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','52'])).

thf('55',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('56',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('59',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X12 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('63',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('65',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','52'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('68',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['63','64'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( X20
       != ( k1_relset_1 @ X20 @ X21 @ X22 ) )
      | ( v1_funct_2 @ X22 @ X20 @ X21 )
      | ~ ( zip_tseitin_1 @ X22 @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 )
      | ( X19 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('74',plain,(
    ! [X18: $i] :
      ( zip_tseitin_0 @ X18 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('76',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( zip_tseitin_0 @ X23 @ X24 )
      | ( zip_tseitin_1 @ X25 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['72','78'])).

thf('80',plain,(
    $false ),
    inference(demod,[status(thm)],['14','53','54','65','66','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iqxTT5vQnA
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:43:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 3.97/4.19  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.97/4.19  % Solved by: fo/fo7.sh
% 3.97/4.19  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.97/4.19  % done 4427 iterations in 3.745s
% 3.97/4.19  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.97/4.19  % SZS output start Refutation
% 3.97/4.19  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.97/4.19  thf(sk_A_type, type, sk_A: $i).
% 3.97/4.19  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 3.97/4.19  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.97/4.19  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.97/4.19  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.97/4.19  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.97/4.19  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.97/4.19  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.97/4.19  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.97/4.19  thf(sk_B_type, type, sk_B: $i > $i).
% 3.97/4.19  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.97/4.19  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.97/4.19  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.97/4.19  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.97/4.19  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.97/4.19  thf(t3_funct_2, conjecture,
% 3.97/4.19    (![A:$i]:
% 3.97/4.19     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.97/4.19       ( ( v1_funct_1 @ A ) & 
% 3.97/4.19         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 3.97/4.19         ( m1_subset_1 @
% 3.97/4.19           A @ 
% 3.97/4.19           ( k1_zfmisc_1 @
% 3.97/4.19             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 3.97/4.19  thf(zf_stmt_0, negated_conjecture,
% 3.97/4.19    (~( ![A:$i]:
% 3.97/4.19        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.97/4.19          ( ( v1_funct_1 @ A ) & 
% 3.97/4.19            ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 3.97/4.19            ( m1_subset_1 @
% 3.97/4.19              A @ 
% 3.97/4.19              ( k1_zfmisc_1 @
% 3.97/4.19                ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )),
% 3.97/4.19    inference('cnf.neg', [status(esa)], [t3_funct_2])).
% 3.97/4.19  thf('0', plain,
% 3.97/4.19      ((~ (v1_funct_1 @ sk_A)
% 3.97/4.19        | ~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 3.97/4.19        | ~ (m1_subset_1 @ sk_A @ 
% 3.97/4.19             (k1_zfmisc_1 @ 
% 3.97/4.19              (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 3.97/4.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.97/4.19  thf('1', plain,
% 3.97/4.19      ((~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))
% 3.97/4.19         <= (~
% 3.97/4.19             ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))),
% 3.97/4.19      inference('split', [status(esa)], ['0'])).
% 3.97/4.19  thf('2', plain, ((v1_funct_1 @ sk_A)),
% 3.97/4.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.97/4.19  thf('3', plain, ((~ (v1_funct_1 @ sk_A)) <= (~ ((v1_funct_1 @ sk_A)))),
% 3.97/4.19      inference('split', [status(esa)], ['0'])).
% 3.97/4.19  thf('4', plain, (((v1_funct_1 @ sk_A))),
% 3.97/4.19      inference('sup-', [status(thm)], ['2', '3'])).
% 3.97/4.19  thf(t21_relat_1, axiom,
% 3.97/4.19    (![A:$i]:
% 3.97/4.19     ( ( v1_relat_1 @ A ) =>
% 3.97/4.19       ( r1_tarski @
% 3.97/4.19         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 3.97/4.19  thf('5', plain,
% 3.97/4.19      (![X11 : $i]:
% 3.97/4.19         ((r1_tarski @ X11 @ 
% 3.97/4.19           (k2_zfmisc_1 @ (k1_relat_1 @ X11) @ (k2_relat_1 @ X11)))
% 3.97/4.19          | ~ (v1_relat_1 @ X11))),
% 3.97/4.19      inference('cnf', [status(esa)], [t21_relat_1])).
% 3.97/4.19  thf(t3_subset, axiom,
% 3.97/4.19    (![A:$i,B:$i]:
% 3.97/4.19     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.97/4.19  thf('6', plain,
% 3.97/4.19      (![X8 : $i, X10 : $i]:
% 3.97/4.19         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 3.97/4.19      inference('cnf', [status(esa)], [t3_subset])).
% 3.97/4.19  thf('7', plain,
% 3.97/4.19      (![X0 : $i]:
% 3.97/4.19         (~ (v1_relat_1 @ X0)
% 3.97/4.19          | (m1_subset_1 @ X0 @ 
% 3.97/4.19             (k1_zfmisc_1 @ 
% 3.97/4.19              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 3.97/4.19      inference('sup-', [status(thm)], ['5', '6'])).
% 3.97/4.19  thf('8', plain,
% 3.97/4.19      ((~ (m1_subset_1 @ sk_A @ 
% 3.97/4.19           (k1_zfmisc_1 @ 
% 3.97/4.19            (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))
% 3.97/4.19         <= (~
% 3.97/4.19             ((m1_subset_1 @ sk_A @ 
% 3.97/4.19               (k1_zfmisc_1 @ 
% 3.97/4.19                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 3.97/4.19      inference('split', [status(esa)], ['0'])).
% 3.97/4.19  thf('9', plain,
% 3.97/4.19      ((~ (v1_relat_1 @ sk_A))
% 3.97/4.19         <= (~
% 3.97/4.19             ((m1_subset_1 @ sk_A @ 
% 3.97/4.19               (k1_zfmisc_1 @ 
% 3.97/4.19                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 3.97/4.19      inference('sup-', [status(thm)], ['7', '8'])).
% 3.97/4.19  thf('10', plain, ((v1_relat_1 @ sk_A)),
% 3.97/4.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.97/4.19  thf('11', plain,
% 3.97/4.19      (((m1_subset_1 @ sk_A @ 
% 3.97/4.19         (k1_zfmisc_1 @ 
% 3.97/4.19          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 3.97/4.19      inference('demod', [status(thm)], ['9', '10'])).
% 3.97/4.19  thf('12', plain,
% 3.97/4.19      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))) | 
% 3.97/4.19       ~
% 3.97/4.19       ((m1_subset_1 @ sk_A @ 
% 3.97/4.19         (k1_zfmisc_1 @ 
% 3.97/4.19          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))) | 
% 3.97/4.19       ~ ((v1_funct_1 @ sk_A))),
% 3.97/4.19      inference('split', [status(esa)], ['0'])).
% 3.97/4.19  thf('13', plain,
% 3.97/4.19      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))),
% 3.97/4.19      inference('sat_resolution*', [status(thm)], ['4', '11', '12'])).
% 3.97/4.19  thf('14', plain,
% 3.97/4.19      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 3.97/4.19      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 3.97/4.19  thf(d1_funct_2, axiom,
% 3.97/4.19    (![A:$i,B:$i,C:$i]:
% 3.97/4.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.97/4.19       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.97/4.19           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 3.97/4.19             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 3.97/4.19         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.97/4.19           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 3.97/4.19             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 3.97/4.19  thf(zf_stmt_1, axiom,
% 3.97/4.19    (![B:$i,A:$i]:
% 3.97/4.19     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.97/4.19       ( zip_tseitin_0 @ B @ A ) ))).
% 3.97/4.19  thf('15', plain,
% 3.97/4.19      (![X18 : $i, X19 : $i]:
% 3.97/4.19         ((zip_tseitin_0 @ X18 @ X19) | ((X18) = (k1_xboole_0)))),
% 3.97/4.19      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.97/4.19  thf(t113_zfmisc_1, axiom,
% 3.97/4.19    (![A:$i,B:$i]:
% 3.97/4.19     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 3.97/4.19       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 3.97/4.19  thf('16', plain,
% 3.97/4.19      (![X5 : $i, X6 : $i]:
% 3.97/4.19         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 3.97/4.19      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.97/4.19  thf('17', plain,
% 3.97/4.19      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 3.97/4.19      inference('simplify', [status(thm)], ['16'])).
% 3.97/4.19  thf('18', plain,
% 3.97/4.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.97/4.19         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 3.97/4.19      inference('sup+', [status(thm)], ['15', '17'])).
% 3.97/4.19  thf('19', plain,
% 3.97/4.19      (![X11 : $i]:
% 3.97/4.19         ((r1_tarski @ X11 @ 
% 3.97/4.19           (k2_zfmisc_1 @ (k1_relat_1 @ X11) @ (k2_relat_1 @ X11)))
% 3.97/4.19          | ~ (v1_relat_1 @ X11))),
% 3.97/4.19      inference('cnf', [status(esa)], [t21_relat_1])).
% 3.97/4.19  thf(l13_xboole_0, axiom,
% 3.97/4.19    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 3.97/4.19  thf('20', plain,
% 3.97/4.19      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.97/4.19      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.97/4.19  thf(rc2_subset_1, axiom,
% 3.97/4.19    (![A:$i]:
% 3.97/4.19     ( ?[B:$i]:
% 3.97/4.19       ( ( v1_xboole_0 @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 3.97/4.19  thf('21', plain,
% 3.97/4.19      (![X7 : $i]: (m1_subset_1 @ (sk_B @ X7) @ (k1_zfmisc_1 @ X7))),
% 3.97/4.19      inference('cnf', [status(esa)], [rc2_subset_1])).
% 3.97/4.19  thf('22', plain, (![X7 : $i]: (v1_xboole_0 @ (sk_B @ X7))),
% 3.97/4.19      inference('cnf', [status(esa)], [rc2_subset_1])).
% 3.97/4.19  thf('23', plain,
% 3.97/4.19      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.97/4.19      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.97/4.19  thf('24', plain, (![X0 : $i]: ((sk_B @ X0) = (k1_xboole_0))),
% 3.97/4.19      inference('sup-', [status(thm)], ['22', '23'])).
% 3.97/4.19  thf('25', plain,
% 3.97/4.19      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 3.97/4.19      inference('demod', [status(thm)], ['21', '24'])).
% 3.97/4.19  thf('26', plain,
% 3.97/4.19      (![X8 : $i, X9 : $i]:
% 3.97/4.19         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 3.97/4.19      inference('cnf', [status(esa)], [t3_subset])).
% 3.97/4.19  thf('27', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 3.97/4.19      inference('sup-', [status(thm)], ['25', '26'])).
% 3.97/4.19  thf(d10_xboole_0, axiom,
% 3.97/4.19    (![A:$i,B:$i]:
% 3.97/4.19     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.97/4.19  thf('28', plain,
% 3.97/4.19      (![X1 : $i, X3 : $i]:
% 3.97/4.19         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 3.97/4.19      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.97/4.19  thf('29', plain,
% 3.97/4.19      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 3.97/4.19      inference('sup-', [status(thm)], ['27', '28'])).
% 3.97/4.19  thf('30', plain,
% 3.97/4.19      (![X0 : $i, X1 : $i]:
% 3.97/4.19         (~ (r1_tarski @ X1 @ X0)
% 3.97/4.19          | ~ (v1_xboole_0 @ X0)
% 3.97/4.19          | ((X1) = (k1_xboole_0)))),
% 3.97/4.19      inference('sup-', [status(thm)], ['20', '29'])).
% 3.97/4.19  thf('31', plain,
% 3.97/4.19      (![X0 : $i]:
% 3.97/4.19         (~ (v1_relat_1 @ X0)
% 3.97/4.19          | ((X0) = (k1_xboole_0))
% 3.97/4.19          | ~ (v1_xboole_0 @ 
% 3.97/4.19               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 3.97/4.19      inference('sup-', [status(thm)], ['19', '30'])).
% 3.97/4.19  thf('32', plain,
% 3.97/4.19      (![X0 : $i, X1 : $i]:
% 3.97/4.19         (~ (v1_xboole_0 @ k1_xboole_0)
% 3.97/4.19          | (zip_tseitin_0 @ (k2_relat_1 @ X0) @ X1)
% 3.97/4.19          | ((X0) = (k1_xboole_0))
% 3.97/4.19          | ~ (v1_relat_1 @ X0))),
% 3.97/4.19      inference('sup-', [status(thm)], ['18', '31'])).
% 3.97/4.19  thf('33', plain, (![X7 : $i]: (v1_xboole_0 @ (sk_B @ X7))),
% 3.97/4.19      inference('cnf', [status(esa)], [rc2_subset_1])).
% 3.97/4.19  thf('34', plain, (![X0 : $i]: ((sk_B @ X0) = (k1_xboole_0))),
% 3.97/4.19      inference('sup-', [status(thm)], ['22', '23'])).
% 3.97/4.19  thf('35', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.97/4.19      inference('demod', [status(thm)], ['33', '34'])).
% 3.97/4.19  thf('36', plain,
% 3.97/4.19      (![X0 : $i, X1 : $i]:
% 3.97/4.19         ((zip_tseitin_0 @ (k2_relat_1 @ X0) @ X1)
% 3.97/4.19          | ((X0) = (k1_xboole_0))
% 3.97/4.19          | ~ (v1_relat_1 @ X0))),
% 3.97/4.19      inference('demod', [status(thm)], ['32', '35'])).
% 3.97/4.19  thf('37', plain,
% 3.97/4.19      (![X0 : $i]:
% 3.97/4.19         (~ (v1_relat_1 @ X0)
% 3.97/4.19          | (m1_subset_1 @ X0 @ 
% 3.97/4.19             (k1_zfmisc_1 @ 
% 3.97/4.19              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 3.97/4.19      inference('sup-', [status(thm)], ['5', '6'])).
% 3.97/4.19  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 3.97/4.19  thf(zf_stmt_3, axiom,
% 3.97/4.19    (![C:$i,B:$i,A:$i]:
% 3.97/4.19     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 3.97/4.19       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.97/4.19  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 3.97/4.19  thf(zf_stmt_5, axiom,
% 3.97/4.19    (![A:$i,B:$i,C:$i]:
% 3.97/4.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.97/4.19       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 3.97/4.19         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.97/4.19           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 3.97/4.19             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 3.97/4.19  thf('38', plain,
% 3.97/4.19      (![X23 : $i, X24 : $i, X25 : $i]:
% 3.97/4.19         (~ (zip_tseitin_0 @ X23 @ X24)
% 3.97/4.19          | (zip_tseitin_1 @ X25 @ X23 @ X24)
% 3.97/4.19          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23))))),
% 3.97/4.19      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.97/4.19  thf('39', plain,
% 3.97/4.19      (![X0 : $i]:
% 3.97/4.19         (~ (v1_relat_1 @ X0)
% 3.97/4.19          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 3.97/4.19          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 3.97/4.19      inference('sup-', [status(thm)], ['37', '38'])).
% 3.97/4.19  thf('40', plain,
% 3.97/4.19      (![X0 : $i]:
% 3.97/4.19         (~ (v1_relat_1 @ X0)
% 3.97/4.19          | ((X0) = (k1_xboole_0))
% 3.97/4.19          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 3.97/4.19          | ~ (v1_relat_1 @ X0))),
% 3.97/4.19      inference('sup-', [status(thm)], ['36', '39'])).
% 3.97/4.19  thf('41', plain,
% 3.97/4.19      (![X0 : $i]:
% 3.97/4.19         ((zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 3.97/4.19          | ((X0) = (k1_xboole_0))
% 3.97/4.19          | ~ (v1_relat_1 @ X0))),
% 3.97/4.19      inference('simplify', [status(thm)], ['40'])).
% 3.97/4.19  thf('42', plain,
% 3.97/4.19      (![X0 : $i]:
% 3.97/4.19         (~ (v1_relat_1 @ X0)
% 3.97/4.19          | (m1_subset_1 @ X0 @ 
% 3.97/4.19             (k1_zfmisc_1 @ 
% 3.97/4.19              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 3.97/4.19      inference('sup-', [status(thm)], ['5', '6'])).
% 3.97/4.19  thf(redefinition_k1_relset_1, axiom,
% 3.97/4.19    (![A:$i,B:$i,C:$i]:
% 3.97/4.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.97/4.19       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 3.97/4.19  thf('43', plain,
% 3.97/4.19      (![X15 : $i, X16 : $i, X17 : $i]:
% 3.97/4.19         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 3.97/4.19          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 3.97/4.19      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.97/4.19  thf('44', plain,
% 3.97/4.19      (![X0 : $i]:
% 3.97/4.19         (~ (v1_relat_1 @ X0)
% 3.97/4.19          | ((k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 3.97/4.19              = (k1_relat_1 @ X0)))),
% 3.97/4.19      inference('sup-', [status(thm)], ['42', '43'])).
% 3.97/4.19  thf('45', plain,
% 3.97/4.19      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.97/4.19         (((X20) != (k1_relset_1 @ X20 @ X21 @ X22))
% 3.97/4.19          | (v1_funct_2 @ X22 @ X20 @ X21)
% 3.97/4.19          | ~ (zip_tseitin_1 @ X22 @ X21 @ X20))),
% 3.97/4.19      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.97/4.19  thf('46', plain,
% 3.97/4.19      (![X0 : $i]:
% 3.97/4.19         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 3.97/4.19          | ~ (v1_relat_1 @ X0)
% 3.97/4.19          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 3.97/4.19          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 3.97/4.19      inference('sup-', [status(thm)], ['44', '45'])).
% 3.97/4.19  thf('47', plain,
% 3.97/4.19      (![X0 : $i]:
% 3.97/4.19         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 3.97/4.19          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 3.97/4.19          | ~ (v1_relat_1 @ X0))),
% 3.97/4.19      inference('simplify', [status(thm)], ['46'])).
% 3.97/4.19  thf('48', plain,
% 3.97/4.19      (![X0 : $i]:
% 3.97/4.19         (~ (v1_relat_1 @ X0)
% 3.97/4.19          | ((X0) = (k1_xboole_0))
% 3.97/4.19          | ~ (v1_relat_1 @ X0)
% 3.97/4.19          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 3.97/4.19      inference('sup-', [status(thm)], ['41', '47'])).
% 3.97/4.19  thf('49', plain,
% 3.97/4.19      (![X0 : $i]:
% 3.97/4.19         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 3.97/4.19          | ((X0) = (k1_xboole_0))
% 3.97/4.19          | ~ (v1_relat_1 @ X0))),
% 3.97/4.19      inference('simplify', [status(thm)], ['48'])).
% 3.97/4.19  thf('50', plain,
% 3.97/4.19      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 3.97/4.19      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 3.97/4.19  thf('51', plain, ((~ (v1_relat_1 @ sk_A) | ((sk_A) = (k1_xboole_0)))),
% 3.97/4.19      inference('sup-', [status(thm)], ['49', '50'])).
% 3.97/4.19  thf('52', plain, ((v1_relat_1 @ sk_A)),
% 3.97/4.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.97/4.19  thf('53', plain, (((sk_A) = (k1_xboole_0))),
% 3.97/4.19      inference('demod', [status(thm)], ['51', '52'])).
% 3.97/4.19  thf('54', plain, (((sk_A) = (k1_xboole_0))),
% 3.97/4.19      inference('demod', [status(thm)], ['51', '52'])).
% 3.97/4.19  thf('55', plain,
% 3.97/4.19      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 3.97/4.19      inference('demod', [status(thm)], ['21', '24'])).
% 3.97/4.19  thf('56', plain,
% 3.97/4.19      (![X15 : $i, X16 : $i, X17 : $i]:
% 3.97/4.19         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 3.97/4.19          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 3.97/4.19      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.97/4.19  thf('57', plain,
% 3.97/4.19      (![X0 : $i, X1 : $i]:
% 3.97/4.19         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 3.97/4.19      inference('sup-', [status(thm)], ['55', '56'])).
% 3.97/4.19  thf('58', plain,
% 3.97/4.19      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 3.97/4.19      inference('demod', [status(thm)], ['21', '24'])).
% 3.97/4.19  thf(dt_k1_relset_1, axiom,
% 3.97/4.19    (![A:$i,B:$i,C:$i]:
% 3.97/4.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.97/4.19       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 3.97/4.19  thf('59', plain,
% 3.97/4.19      (![X12 : $i, X13 : $i, X14 : $i]:
% 3.97/4.19         ((m1_subset_1 @ (k1_relset_1 @ X12 @ X13 @ X14) @ (k1_zfmisc_1 @ X12))
% 3.97/4.19          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 3.97/4.19      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 3.97/4.19  thf('60', plain,
% 3.97/4.19      (![X0 : $i, X1 : $i]:
% 3.97/4.19         (m1_subset_1 @ (k1_relset_1 @ X1 @ X0 @ k1_xboole_0) @ 
% 3.97/4.19          (k1_zfmisc_1 @ X1))),
% 3.97/4.19      inference('sup-', [status(thm)], ['58', '59'])).
% 3.97/4.19  thf('61', plain,
% 3.97/4.19      (![X0 : $i]:
% 3.97/4.19         (m1_subset_1 @ (k1_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 3.97/4.19      inference('sup+', [status(thm)], ['57', '60'])).
% 3.97/4.19  thf('62', plain,
% 3.97/4.19      (![X8 : $i, X9 : $i]:
% 3.97/4.19         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 3.97/4.19      inference('cnf', [status(esa)], [t3_subset])).
% 3.97/4.19  thf('63', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 3.97/4.19      inference('sup-', [status(thm)], ['61', '62'])).
% 3.97/4.19  thf('64', plain,
% 3.97/4.19      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 3.97/4.19      inference('sup-', [status(thm)], ['27', '28'])).
% 3.97/4.19  thf('65', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.97/4.19      inference('sup-', [status(thm)], ['63', '64'])).
% 3.97/4.19  thf('66', plain, (((sk_A) = (k1_xboole_0))),
% 3.97/4.19      inference('demod', [status(thm)], ['51', '52'])).
% 3.97/4.19  thf('67', plain,
% 3.97/4.19      (![X0 : $i, X1 : $i]:
% 3.97/4.19         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 3.97/4.19      inference('sup-', [status(thm)], ['55', '56'])).
% 3.97/4.19  thf('68', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.97/4.19      inference('sup-', [status(thm)], ['63', '64'])).
% 3.97/4.19  thf('69', plain,
% 3.97/4.19      (![X0 : $i, X1 : $i]:
% 3.97/4.19         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 3.97/4.19      inference('demod', [status(thm)], ['67', '68'])).
% 3.97/4.19  thf('70', plain,
% 3.97/4.19      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.97/4.19         (((X20) != (k1_relset_1 @ X20 @ X21 @ X22))
% 3.97/4.19          | (v1_funct_2 @ X22 @ X20 @ X21)
% 3.97/4.19          | ~ (zip_tseitin_1 @ X22 @ X21 @ X20))),
% 3.97/4.19      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.97/4.19  thf('71', plain,
% 3.97/4.19      (![X0 : $i, X1 : $i]:
% 3.97/4.19         (((X1) != (k1_xboole_0))
% 3.97/4.19          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 3.97/4.19          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 3.97/4.19      inference('sup-', [status(thm)], ['69', '70'])).
% 3.97/4.19  thf('72', plain,
% 3.97/4.19      (![X0 : $i]:
% 3.97/4.19         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 3.97/4.19          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 3.97/4.19      inference('simplify', [status(thm)], ['71'])).
% 3.97/4.19  thf('73', plain,
% 3.97/4.19      (![X18 : $i, X19 : $i]:
% 3.97/4.19         ((zip_tseitin_0 @ X18 @ X19) | ((X19) != (k1_xboole_0)))),
% 3.97/4.19      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.97/4.19  thf('74', plain, (![X18 : $i]: (zip_tseitin_0 @ X18 @ k1_xboole_0)),
% 3.97/4.19      inference('simplify', [status(thm)], ['73'])).
% 3.97/4.19  thf('75', plain,
% 3.97/4.19      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 3.97/4.19      inference('demod', [status(thm)], ['21', '24'])).
% 3.97/4.19  thf('76', plain,
% 3.97/4.19      (![X23 : $i, X24 : $i, X25 : $i]:
% 3.97/4.19         (~ (zip_tseitin_0 @ X23 @ X24)
% 3.97/4.19          | (zip_tseitin_1 @ X25 @ X23 @ X24)
% 3.97/4.19          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23))))),
% 3.97/4.19      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.97/4.19  thf('77', plain,
% 3.97/4.19      (![X0 : $i, X1 : $i]:
% 3.97/4.19         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 3.97/4.19      inference('sup-', [status(thm)], ['75', '76'])).
% 3.97/4.19  thf('78', plain,
% 3.97/4.19      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 3.97/4.19      inference('sup-', [status(thm)], ['74', '77'])).
% 3.97/4.19  thf('79', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 3.97/4.19      inference('demod', [status(thm)], ['72', '78'])).
% 3.97/4.19  thf('80', plain, ($false),
% 3.97/4.19      inference('demod', [status(thm)], ['14', '53', '54', '65', '66', '79'])).
% 3.97/4.19  
% 3.97/4.19  % SZS output end Refutation
% 3.97/4.19  
% 3.97/4.20  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
