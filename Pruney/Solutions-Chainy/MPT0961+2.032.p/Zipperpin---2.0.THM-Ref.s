%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WuLHUWjcPM

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:42 EST 2020

% Result     : Theorem 14.01s
% Output     : Refutation 14.01s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 885 expanded)
%              Number of leaves         :   33 ( 274 expanded)
%              Depth                    :   21
%              Number of atoms          : 1034 (7492 expanded)
%              Number of equality atoms :   74 ( 418 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

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
    ! [X16: $i] :
      ( ( r1_tarski @ X16 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X16 ) @ ( k2_relat_1 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
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
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('16',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('17',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X16: $i] :
      ( ( r1_tarski @ X16 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X16 ) @ ( k2_relat_1 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('20',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('21',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('22',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('23',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('25',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('26',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','27'])).

thf('30',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['20','32'])).

thf('34',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('35',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('36',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X17 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_relset_1 @ X1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('40',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('41',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      = ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['38','45'])).

thf('47',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('48',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ k1_xboole_0 ) )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('52',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      = ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_relset_1 @ X1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['52','59'])).

thf('61',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('62',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['60','61'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['50','62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['19','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','66'])).

thf('68',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
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

thf('71',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0 = k1_xboole_0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('76',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( X25
       != ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['74','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['1','13'])).

thf('84',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['84','85'])).

thf('88',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['60','61'])).

thf('89',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['84','85'])).

thf('90',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['51'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      = ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['51'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['60','61'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( X25
       != ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X24 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('101',plain,(
    ! [X23: $i] :
      ( zip_tseitin_0 @ X23 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('103',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['101','104'])).

thf('106',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['51'])).

thf('107',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['99','107'])).

thf('109',plain,(
    $false ),
    inference(demod,[status(thm)],['14','86','87','88','89','108'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WuLHUWjcPM
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:33:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 14.01/14.19  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 14.01/14.19  % Solved by: fo/fo7.sh
% 14.01/14.19  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 14.01/14.19  % done 13015 iterations in 13.723s
% 14.01/14.19  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 14.01/14.19  % SZS output start Refutation
% 14.01/14.19  thf(sk_A_type, type, sk_A: $i).
% 14.01/14.19  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 14.01/14.19  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 14.01/14.19  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 14.01/14.19  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 14.01/14.19  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 14.01/14.19  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 14.01/14.19  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 14.01/14.19  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 14.01/14.19  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 14.01/14.19  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 14.01/14.19  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 14.01/14.19  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 14.01/14.19  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 14.01/14.19  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 14.01/14.19  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 14.01/14.19  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 14.01/14.19  thf(t3_funct_2, conjecture,
% 14.01/14.19    (![A:$i]:
% 14.01/14.19     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 14.01/14.19       ( ( v1_funct_1 @ A ) & 
% 14.01/14.19         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 14.01/14.19         ( m1_subset_1 @
% 14.01/14.19           A @ 
% 14.01/14.19           ( k1_zfmisc_1 @
% 14.01/14.19             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 14.01/14.19  thf(zf_stmt_0, negated_conjecture,
% 14.01/14.19    (~( ![A:$i]:
% 14.01/14.19        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 14.01/14.19          ( ( v1_funct_1 @ A ) & 
% 14.01/14.19            ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 14.01/14.19            ( m1_subset_1 @
% 14.01/14.19              A @ 
% 14.01/14.19              ( k1_zfmisc_1 @
% 14.01/14.19                ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )),
% 14.01/14.19    inference('cnf.neg', [status(esa)], [t3_funct_2])).
% 14.01/14.19  thf('0', plain,
% 14.01/14.19      ((~ (v1_funct_1 @ sk_A)
% 14.01/14.19        | ~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 14.01/14.19        | ~ (m1_subset_1 @ sk_A @ 
% 14.01/14.19             (k1_zfmisc_1 @ 
% 14.01/14.19              (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 14.01/14.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.01/14.19  thf('1', plain,
% 14.01/14.19      ((~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))
% 14.01/14.19         <= (~
% 14.01/14.19             ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))),
% 14.01/14.19      inference('split', [status(esa)], ['0'])).
% 14.01/14.19  thf('2', plain, ((v1_funct_1 @ sk_A)),
% 14.01/14.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.01/14.19  thf('3', plain, ((~ (v1_funct_1 @ sk_A)) <= (~ ((v1_funct_1 @ sk_A)))),
% 14.01/14.19      inference('split', [status(esa)], ['0'])).
% 14.01/14.19  thf('4', plain, (((v1_funct_1 @ sk_A))),
% 14.01/14.19      inference('sup-', [status(thm)], ['2', '3'])).
% 14.01/14.19  thf(t21_relat_1, axiom,
% 14.01/14.19    (![A:$i]:
% 14.01/14.19     ( ( v1_relat_1 @ A ) =>
% 14.01/14.19       ( r1_tarski @
% 14.01/14.19         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 14.01/14.19  thf('5', plain,
% 14.01/14.19      (![X16 : $i]:
% 14.01/14.19         ((r1_tarski @ X16 @ 
% 14.01/14.19           (k2_zfmisc_1 @ (k1_relat_1 @ X16) @ (k2_relat_1 @ X16)))
% 14.01/14.19          | ~ (v1_relat_1 @ X16))),
% 14.01/14.19      inference('cnf', [status(esa)], [t21_relat_1])).
% 14.01/14.19  thf(t3_subset, axiom,
% 14.01/14.19    (![A:$i,B:$i]:
% 14.01/14.19     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 14.01/14.19  thf('6', plain,
% 14.01/14.19      (![X10 : $i, X12 : $i]:
% 14.01/14.19         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 14.01/14.19      inference('cnf', [status(esa)], [t3_subset])).
% 14.01/14.19  thf('7', plain,
% 14.01/14.19      (![X0 : $i]:
% 14.01/14.19         (~ (v1_relat_1 @ X0)
% 14.01/14.19          | (m1_subset_1 @ X0 @ 
% 14.01/14.19             (k1_zfmisc_1 @ 
% 14.01/14.19              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 14.01/14.19      inference('sup-', [status(thm)], ['5', '6'])).
% 14.01/14.19  thf('8', plain,
% 14.01/14.19      ((~ (m1_subset_1 @ sk_A @ 
% 14.01/14.19           (k1_zfmisc_1 @ 
% 14.01/14.19            (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))
% 14.01/14.19         <= (~
% 14.01/14.19             ((m1_subset_1 @ sk_A @ 
% 14.01/14.19               (k1_zfmisc_1 @ 
% 14.01/14.19                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 14.01/14.19      inference('split', [status(esa)], ['0'])).
% 14.01/14.19  thf('9', plain,
% 14.01/14.19      ((~ (v1_relat_1 @ sk_A))
% 14.01/14.19         <= (~
% 14.01/14.19             ((m1_subset_1 @ sk_A @ 
% 14.01/14.19               (k1_zfmisc_1 @ 
% 14.01/14.19                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 14.01/14.19      inference('sup-', [status(thm)], ['7', '8'])).
% 14.01/14.19  thf('10', plain, ((v1_relat_1 @ sk_A)),
% 14.01/14.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.01/14.19  thf('11', plain,
% 14.01/14.19      (((m1_subset_1 @ sk_A @ 
% 14.01/14.19         (k1_zfmisc_1 @ 
% 14.01/14.19          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 14.01/14.19      inference('demod', [status(thm)], ['9', '10'])).
% 14.01/14.19  thf('12', plain,
% 14.01/14.19      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))) | 
% 14.01/14.19       ~
% 14.01/14.19       ((m1_subset_1 @ sk_A @ 
% 14.01/14.19         (k1_zfmisc_1 @ 
% 14.01/14.19          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))) | 
% 14.01/14.19       ~ ((v1_funct_1 @ sk_A))),
% 14.01/14.19      inference('split', [status(esa)], ['0'])).
% 14.01/14.19  thf('13', plain,
% 14.01/14.19      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))),
% 14.01/14.19      inference('sat_resolution*', [status(thm)], ['4', '11', '12'])).
% 14.01/14.19  thf('14', plain,
% 14.01/14.19      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 14.01/14.19      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 14.01/14.19  thf(d1_funct_2, axiom,
% 14.01/14.19    (![A:$i,B:$i,C:$i]:
% 14.01/14.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 14.01/14.19       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 14.01/14.19           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 14.01/14.19             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 14.01/14.19         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 14.01/14.19           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 14.01/14.19             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 14.01/14.19  thf(zf_stmt_1, axiom,
% 14.01/14.19    (![B:$i,A:$i]:
% 14.01/14.19     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 14.01/14.19       ( zip_tseitin_0 @ B @ A ) ))).
% 14.01/14.19  thf('15', plain,
% 14.01/14.19      (![X23 : $i, X24 : $i]:
% 14.01/14.19         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 14.01/14.19      inference('cnf', [status(esa)], [zf_stmt_1])).
% 14.01/14.19  thf(t113_zfmisc_1, axiom,
% 14.01/14.19    (![A:$i,B:$i]:
% 14.01/14.19     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 14.01/14.19       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 14.01/14.19  thf('16', plain,
% 14.01/14.19      (![X8 : $i, X9 : $i]:
% 14.01/14.19         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 14.01/14.19      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 14.01/14.19  thf('17', plain,
% 14.01/14.19      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 14.01/14.19      inference('simplify', [status(thm)], ['16'])).
% 14.01/14.19  thf('18', plain,
% 14.01/14.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.01/14.19         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 14.01/14.19      inference('sup+', [status(thm)], ['15', '17'])).
% 14.01/14.19  thf('19', plain,
% 14.01/14.19      (![X16 : $i]:
% 14.01/14.19         ((r1_tarski @ X16 @ 
% 14.01/14.19           (k2_zfmisc_1 @ (k1_relat_1 @ X16) @ (k2_relat_1 @ X16)))
% 14.01/14.19          | ~ (v1_relat_1 @ X16))),
% 14.01/14.19      inference('cnf', [status(esa)], [t21_relat_1])).
% 14.01/14.19  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 14.01/14.19  thf('20', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 14.01/14.19      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 14.01/14.19  thf(d3_tarski, axiom,
% 14.01/14.19    (![A:$i,B:$i]:
% 14.01/14.19     ( ( r1_tarski @ A @ B ) <=>
% 14.01/14.19       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 14.01/14.19  thf('21', plain,
% 14.01/14.19      (![X1 : $i, X3 : $i]:
% 14.01/14.19         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 14.01/14.19      inference('cnf', [status(esa)], [d3_tarski])).
% 14.01/14.19  thf(d10_xboole_0, axiom,
% 14.01/14.19    (![A:$i,B:$i]:
% 14.01/14.19     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 14.01/14.19  thf('22', plain,
% 14.01/14.19      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 14.01/14.19      inference('cnf', [status(esa)], [d10_xboole_0])).
% 14.01/14.19  thf('23', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 14.01/14.19      inference('simplify', [status(thm)], ['22'])).
% 14.01/14.19  thf('24', plain,
% 14.01/14.19      (![X10 : $i, X12 : $i]:
% 14.01/14.19         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 14.01/14.19      inference('cnf', [status(esa)], [t3_subset])).
% 14.01/14.19  thf('25', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 14.01/14.19      inference('sup-', [status(thm)], ['23', '24'])).
% 14.01/14.19  thf(t5_subset, axiom,
% 14.01/14.19    (![A:$i,B:$i,C:$i]:
% 14.01/14.19     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 14.01/14.19          ( v1_xboole_0 @ C ) ) ))).
% 14.01/14.19  thf('26', plain,
% 14.01/14.19      (![X13 : $i, X14 : $i, X15 : $i]:
% 14.01/14.19         (~ (r2_hidden @ X13 @ X14)
% 14.01/14.19          | ~ (v1_xboole_0 @ X15)
% 14.01/14.19          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 14.01/14.19      inference('cnf', [status(esa)], [t5_subset])).
% 14.01/14.19  thf('27', plain,
% 14.01/14.19      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 14.01/14.19      inference('sup-', [status(thm)], ['25', '26'])).
% 14.01/14.19  thf('28', plain,
% 14.01/14.19      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 14.01/14.19      inference('sup-', [status(thm)], ['21', '27'])).
% 14.01/14.19  thf('29', plain,
% 14.01/14.19      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 14.01/14.19      inference('sup-', [status(thm)], ['21', '27'])).
% 14.01/14.19  thf('30', plain,
% 14.01/14.19      (![X4 : $i, X6 : $i]:
% 14.01/14.19         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 14.01/14.19      inference('cnf', [status(esa)], [d10_xboole_0])).
% 14.01/14.19  thf('31', plain,
% 14.01/14.19      (![X0 : $i, X1 : $i]:
% 14.01/14.19         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 14.01/14.19      inference('sup-', [status(thm)], ['29', '30'])).
% 14.01/14.19  thf('32', plain,
% 14.01/14.19      (![X0 : $i, X1 : $i]:
% 14.01/14.19         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 14.01/14.19      inference('sup-', [status(thm)], ['28', '31'])).
% 14.01/14.19  thf('33', plain,
% 14.01/14.19      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 14.01/14.19      inference('sup-', [status(thm)], ['20', '32'])).
% 14.01/14.19  thf('34', plain,
% 14.01/14.19      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 14.01/14.19      inference('simplify', [status(thm)], ['16'])).
% 14.01/14.19  thf('35', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 14.01/14.19      inference('sup-', [status(thm)], ['23', '24'])).
% 14.01/14.19  thf(dt_k1_relset_1, axiom,
% 14.01/14.19    (![A:$i,B:$i,C:$i]:
% 14.01/14.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 14.01/14.19       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 14.01/14.19  thf('36', plain,
% 14.01/14.19      (![X17 : $i, X18 : $i, X19 : $i]:
% 14.01/14.19         ((m1_subset_1 @ (k1_relset_1 @ X17 @ X18 @ X19) @ (k1_zfmisc_1 @ X17))
% 14.01/14.19          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 14.01/14.19      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 14.01/14.19  thf('37', plain,
% 14.01/14.19      (![X0 : $i, X1 : $i]:
% 14.01/14.19         (m1_subset_1 @ (k1_relset_1 @ X1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0)) @ 
% 14.01/14.19          (k1_zfmisc_1 @ X1))),
% 14.01/14.19      inference('sup-', [status(thm)], ['35', '36'])).
% 14.01/14.19  thf('38', plain,
% 14.01/14.19      (![X0 : $i]:
% 14.01/14.19         (m1_subset_1 @ (k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0) @ 
% 14.01/14.19          (k1_zfmisc_1 @ X0))),
% 14.01/14.19      inference('sup+', [status(thm)], ['34', '37'])).
% 14.01/14.19  thf('39', plain,
% 14.01/14.19      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 14.01/14.19      inference('simplify', [status(thm)], ['16'])).
% 14.01/14.19  thf('40', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 14.01/14.19      inference('sup-', [status(thm)], ['23', '24'])).
% 14.01/14.19  thf(redefinition_k1_relset_1, axiom,
% 14.01/14.19    (![A:$i,B:$i,C:$i]:
% 14.01/14.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 14.01/14.19       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 14.01/14.19  thf('41', plain,
% 14.01/14.19      (![X20 : $i, X21 : $i, X22 : $i]:
% 14.01/14.19         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 14.01/14.19          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 14.01/14.19      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 14.01/14.19  thf('42', plain,
% 14.01/14.19      (![X0 : $i, X1 : $i]:
% 14.01/14.19         ((k1_relset_1 @ X1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0))
% 14.01/14.19           = (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 14.01/14.19      inference('sup-', [status(thm)], ['40', '41'])).
% 14.01/14.19  thf('43', plain,
% 14.01/14.19      (![X0 : $i]:
% 14.01/14.19         ((k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0)
% 14.01/14.19           = (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0)))),
% 14.01/14.19      inference('sup+', [status(thm)], ['39', '42'])).
% 14.01/14.19  thf('44', plain,
% 14.01/14.19      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 14.01/14.19      inference('simplify', [status(thm)], ['16'])).
% 14.01/14.19  thf('45', plain,
% 14.01/14.19      (![X0 : $i]:
% 14.01/14.19         ((k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0)
% 14.01/14.19           = (k1_relat_1 @ k1_xboole_0))),
% 14.01/14.19      inference('demod', [status(thm)], ['43', '44'])).
% 14.01/14.19  thf('46', plain,
% 14.01/14.19      (![X0 : $i]:
% 14.01/14.19         (m1_subset_1 @ (k1_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 14.01/14.19      inference('demod', [status(thm)], ['38', '45'])).
% 14.01/14.19  thf('47', plain,
% 14.01/14.19      (![X10 : $i, X11 : $i]:
% 14.01/14.19         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 14.01/14.19      inference('cnf', [status(esa)], [t3_subset])).
% 14.01/14.19  thf('48', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 14.01/14.19      inference('sup-', [status(thm)], ['46', '47'])).
% 14.01/14.19  thf('49', plain,
% 14.01/14.19      (![X4 : $i, X6 : $i]:
% 14.01/14.19         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 14.01/14.19      inference('cnf', [status(esa)], [d10_xboole_0])).
% 14.01/14.19  thf('50', plain,
% 14.01/14.19      (![X0 : $i]:
% 14.01/14.19         (~ (r1_tarski @ X0 @ (k1_relat_1 @ k1_xboole_0))
% 14.01/14.19          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 14.01/14.19      inference('sup-', [status(thm)], ['48', '49'])).
% 14.01/14.19  thf('51', plain,
% 14.01/14.19      (![X8 : $i, X9 : $i]:
% 14.01/14.19         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X8) != (k1_xboole_0)))),
% 14.01/14.19      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 14.01/14.19  thf('52', plain,
% 14.01/14.19      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 14.01/14.19      inference('simplify', [status(thm)], ['51'])).
% 14.01/14.19  thf('53', plain,
% 14.01/14.19      (![X0 : $i, X1 : $i]:
% 14.01/14.19         ((k1_relset_1 @ X1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0))
% 14.01/14.19           = (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 14.01/14.19      inference('sup-', [status(thm)], ['40', '41'])).
% 14.01/14.19  thf('54', plain,
% 14.01/14.19      (![X0 : $i, X1 : $i]:
% 14.01/14.19         (m1_subset_1 @ (k1_relset_1 @ X1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0)) @ 
% 14.01/14.19          (k1_zfmisc_1 @ X1))),
% 14.01/14.19      inference('sup-', [status(thm)], ['35', '36'])).
% 14.01/14.19  thf('55', plain,
% 14.01/14.19      (![X0 : $i, X1 : $i]:
% 14.01/14.19         (m1_subset_1 @ (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ 
% 14.01/14.19          (k1_zfmisc_1 @ X1))),
% 14.01/14.19      inference('sup+', [status(thm)], ['53', '54'])).
% 14.01/14.19  thf('56', plain,
% 14.01/14.19      (![X10 : $i, X11 : $i]:
% 14.01/14.19         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 14.01/14.19      inference('cnf', [status(esa)], [t3_subset])).
% 14.01/14.19  thf('57', plain,
% 14.01/14.19      (![X0 : $i, X1 : $i]:
% 14.01/14.19         (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) @ X0)),
% 14.01/14.19      inference('sup-', [status(thm)], ['55', '56'])).
% 14.01/14.19  thf('58', plain,
% 14.01/14.19      (![X0 : $i, X1 : $i]:
% 14.01/14.19         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 14.01/14.19      inference('sup-', [status(thm)], ['29', '30'])).
% 14.01/14.19  thf('59', plain,
% 14.01/14.19      (![X0 : $i, X1 : $i]:
% 14.01/14.19         (((k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) = (X0))
% 14.01/14.19          | ~ (v1_xboole_0 @ X0))),
% 14.01/14.19      inference('sup-', [status(thm)], ['57', '58'])).
% 14.01/14.19  thf('60', plain,
% 14.01/14.19      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 14.01/14.19        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 14.01/14.19      inference('sup+', [status(thm)], ['52', '59'])).
% 14.01/14.19  thf('61', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 14.01/14.19      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 14.01/14.19  thf('62', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 14.01/14.19      inference('demod', [status(thm)], ['60', '61'])).
% 14.01/14.19  thf('63', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 14.01/14.19      inference('demod', [status(thm)], ['60', '61'])).
% 14.01/14.19  thf('64', plain,
% 14.01/14.19      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 14.01/14.19      inference('demod', [status(thm)], ['50', '62', '63'])).
% 14.01/14.19  thf('65', plain,
% 14.01/14.19      (![X0 : $i, X1 : $i]:
% 14.01/14.19         (~ (r1_tarski @ X1 @ X0)
% 14.01/14.19          | ~ (v1_xboole_0 @ X0)
% 14.01/14.19          | ((X1) = (k1_xboole_0)))),
% 14.01/14.19      inference('sup-', [status(thm)], ['33', '64'])).
% 14.01/14.19  thf('66', plain,
% 14.01/14.19      (![X0 : $i]:
% 14.01/14.19         (~ (v1_relat_1 @ X0)
% 14.01/14.19          | ((X0) = (k1_xboole_0))
% 14.01/14.19          | ~ (v1_xboole_0 @ 
% 14.01/14.19               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 14.01/14.19      inference('sup-', [status(thm)], ['19', '65'])).
% 14.01/14.19  thf('67', plain,
% 14.01/14.19      (![X0 : $i, X1 : $i]:
% 14.01/14.19         (~ (v1_xboole_0 @ k1_xboole_0)
% 14.01/14.19          | (zip_tseitin_0 @ (k2_relat_1 @ X0) @ X1)
% 14.01/14.19          | ((X0) = (k1_xboole_0))
% 14.01/14.19          | ~ (v1_relat_1 @ X0))),
% 14.01/14.19      inference('sup-', [status(thm)], ['18', '66'])).
% 14.01/14.19  thf('68', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 14.01/14.19      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 14.01/14.19  thf('69', plain,
% 14.01/14.19      (![X0 : $i, X1 : $i]:
% 14.01/14.19         ((zip_tseitin_0 @ (k2_relat_1 @ X0) @ X1)
% 14.01/14.19          | ((X0) = (k1_xboole_0))
% 14.01/14.19          | ~ (v1_relat_1 @ X0))),
% 14.01/14.19      inference('demod', [status(thm)], ['67', '68'])).
% 14.01/14.19  thf('70', plain,
% 14.01/14.19      (![X0 : $i]:
% 14.01/14.19         (~ (v1_relat_1 @ X0)
% 14.01/14.19          | (m1_subset_1 @ X0 @ 
% 14.01/14.19             (k1_zfmisc_1 @ 
% 14.01/14.19              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 14.01/14.19      inference('sup-', [status(thm)], ['5', '6'])).
% 14.01/14.19  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 14.01/14.19  thf(zf_stmt_3, axiom,
% 14.01/14.19    (![C:$i,B:$i,A:$i]:
% 14.01/14.19     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 14.01/14.19       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 14.01/14.19  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 14.01/14.19  thf(zf_stmt_5, axiom,
% 14.01/14.19    (![A:$i,B:$i,C:$i]:
% 14.01/14.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 14.01/14.19       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 14.01/14.19         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 14.01/14.19           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 14.01/14.19             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 14.01/14.19  thf('71', plain,
% 14.01/14.19      (![X28 : $i, X29 : $i, X30 : $i]:
% 14.01/14.19         (~ (zip_tseitin_0 @ X28 @ X29)
% 14.01/14.19          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 14.01/14.19          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 14.01/14.19      inference('cnf', [status(esa)], [zf_stmt_5])).
% 14.01/14.19  thf('72', plain,
% 14.01/14.19      (![X0 : $i]:
% 14.01/14.19         (~ (v1_relat_1 @ X0)
% 14.01/14.19          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 14.01/14.19          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 14.01/14.19      inference('sup-', [status(thm)], ['70', '71'])).
% 14.01/14.19  thf('73', plain,
% 14.01/14.19      (![X0 : $i]:
% 14.01/14.19         (~ (v1_relat_1 @ X0)
% 14.01/14.19          | ((X0) = (k1_xboole_0))
% 14.01/14.19          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 14.01/14.19          | ~ (v1_relat_1 @ X0))),
% 14.01/14.19      inference('sup-', [status(thm)], ['69', '72'])).
% 14.01/14.19  thf('74', plain,
% 14.01/14.19      (![X0 : $i]:
% 14.01/14.19         ((zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 14.01/14.19          | ((X0) = (k1_xboole_0))
% 14.01/14.19          | ~ (v1_relat_1 @ X0))),
% 14.01/14.19      inference('simplify', [status(thm)], ['73'])).
% 14.01/14.19  thf('75', plain,
% 14.01/14.19      (![X0 : $i]:
% 14.01/14.19         (~ (v1_relat_1 @ X0)
% 14.01/14.19          | (m1_subset_1 @ X0 @ 
% 14.01/14.19             (k1_zfmisc_1 @ 
% 14.01/14.19              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 14.01/14.19      inference('sup-', [status(thm)], ['5', '6'])).
% 14.01/14.19  thf('76', plain,
% 14.01/14.19      (![X20 : $i, X21 : $i, X22 : $i]:
% 14.01/14.19         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 14.01/14.19          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 14.01/14.19      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 14.01/14.19  thf('77', plain,
% 14.01/14.19      (![X0 : $i]:
% 14.01/14.19         (~ (v1_relat_1 @ X0)
% 14.01/14.19          | ((k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 14.01/14.19              = (k1_relat_1 @ X0)))),
% 14.01/14.19      inference('sup-', [status(thm)], ['75', '76'])).
% 14.01/14.19  thf('78', plain,
% 14.01/14.19      (![X25 : $i, X26 : $i, X27 : $i]:
% 14.01/14.19         (((X25) != (k1_relset_1 @ X25 @ X26 @ X27))
% 14.01/14.19          | (v1_funct_2 @ X27 @ X25 @ X26)
% 14.01/14.19          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 14.01/14.19      inference('cnf', [status(esa)], [zf_stmt_3])).
% 14.01/14.19  thf('79', plain,
% 14.01/14.19      (![X0 : $i]:
% 14.01/14.19         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 14.01/14.19          | ~ (v1_relat_1 @ X0)
% 14.01/14.19          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 14.01/14.19          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 14.01/14.19      inference('sup-', [status(thm)], ['77', '78'])).
% 14.01/14.19  thf('80', plain,
% 14.01/14.19      (![X0 : $i]:
% 14.01/14.19         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 14.01/14.19          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 14.01/14.19          | ~ (v1_relat_1 @ X0))),
% 14.01/14.19      inference('simplify', [status(thm)], ['79'])).
% 14.01/14.19  thf('81', plain,
% 14.01/14.19      (![X0 : $i]:
% 14.01/14.19         (~ (v1_relat_1 @ X0)
% 14.01/14.19          | ((X0) = (k1_xboole_0))
% 14.01/14.19          | ~ (v1_relat_1 @ X0)
% 14.01/14.19          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 14.01/14.19      inference('sup-', [status(thm)], ['74', '80'])).
% 14.01/14.19  thf('82', plain,
% 14.01/14.19      (![X0 : $i]:
% 14.01/14.19         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 14.01/14.19          | ((X0) = (k1_xboole_0))
% 14.01/14.19          | ~ (v1_relat_1 @ X0))),
% 14.01/14.19      inference('simplify', [status(thm)], ['81'])).
% 14.01/14.19  thf('83', plain,
% 14.01/14.19      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 14.01/14.19      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 14.01/14.19  thf('84', plain, ((~ (v1_relat_1 @ sk_A) | ((sk_A) = (k1_xboole_0)))),
% 14.01/14.19      inference('sup-', [status(thm)], ['82', '83'])).
% 14.01/14.19  thf('85', plain, ((v1_relat_1 @ sk_A)),
% 14.01/14.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.01/14.19  thf('86', plain, (((sk_A) = (k1_xboole_0))),
% 14.01/14.19      inference('demod', [status(thm)], ['84', '85'])).
% 14.01/14.19  thf('87', plain, (((sk_A) = (k1_xboole_0))),
% 14.01/14.19      inference('demod', [status(thm)], ['84', '85'])).
% 14.01/14.19  thf('88', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 14.01/14.19      inference('demod', [status(thm)], ['60', '61'])).
% 14.01/14.19  thf('89', plain, (((sk_A) = (k1_xboole_0))),
% 14.01/14.19      inference('demod', [status(thm)], ['84', '85'])).
% 14.01/14.19  thf('90', plain,
% 14.01/14.19      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 14.01/14.19      inference('simplify', [status(thm)], ['51'])).
% 14.01/14.19  thf('91', plain,
% 14.01/14.19      (![X0 : $i, X1 : $i]:
% 14.01/14.19         ((k1_relset_1 @ X1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0))
% 14.01/14.19           = (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 14.01/14.19      inference('sup-', [status(thm)], ['40', '41'])).
% 14.01/14.19  thf('92', plain,
% 14.01/14.19      (![X0 : $i]:
% 14.01/14.19         ((k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)
% 14.01/14.19           = (k1_relat_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0)))),
% 14.01/14.19      inference('sup+', [status(thm)], ['90', '91'])).
% 14.01/14.19  thf('93', plain,
% 14.01/14.19      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 14.01/14.19      inference('simplify', [status(thm)], ['51'])).
% 14.01/14.19  thf('94', plain,
% 14.01/14.19      (![X0 : $i]:
% 14.01/14.19         ((k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)
% 14.01/14.19           = (k1_relat_1 @ k1_xboole_0))),
% 14.01/14.19      inference('demod', [status(thm)], ['92', '93'])).
% 14.01/14.19  thf('95', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 14.01/14.19      inference('demod', [status(thm)], ['60', '61'])).
% 14.01/14.19  thf('96', plain,
% 14.01/14.19      (![X0 : $i]:
% 14.01/14.19         ((k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 14.01/14.19      inference('demod', [status(thm)], ['94', '95'])).
% 14.01/14.19  thf('97', plain,
% 14.01/14.19      (![X25 : $i, X26 : $i, X27 : $i]:
% 14.01/14.19         (((X25) != (k1_relset_1 @ X25 @ X26 @ X27))
% 14.01/14.19          | (v1_funct_2 @ X27 @ X25 @ X26)
% 14.01/14.19          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 14.01/14.19      inference('cnf', [status(esa)], [zf_stmt_3])).
% 14.01/14.19  thf('98', plain,
% 14.01/14.19      (![X0 : $i]:
% 14.01/14.19         (((k1_xboole_0) != (k1_xboole_0))
% 14.01/14.19          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)
% 14.01/14.19          | (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0))),
% 14.01/14.19      inference('sup-', [status(thm)], ['96', '97'])).
% 14.01/14.19  thf('99', plain,
% 14.01/14.19      (![X0 : $i]:
% 14.01/14.19         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 14.01/14.19          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 14.01/14.19      inference('simplify', [status(thm)], ['98'])).
% 14.01/14.19  thf('100', plain,
% 14.01/14.19      (![X23 : $i, X24 : $i]:
% 14.01/14.19         ((zip_tseitin_0 @ X23 @ X24) | ((X24) != (k1_xboole_0)))),
% 14.01/14.19      inference('cnf', [status(esa)], [zf_stmt_1])).
% 14.01/14.19  thf('101', plain, (![X23 : $i]: (zip_tseitin_0 @ X23 @ k1_xboole_0)),
% 14.01/14.19      inference('simplify', [status(thm)], ['100'])).
% 14.01/14.19  thf('102', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 14.01/14.19      inference('sup-', [status(thm)], ['23', '24'])).
% 14.01/14.19  thf('103', plain,
% 14.01/14.19      (![X28 : $i, X29 : $i, X30 : $i]:
% 14.01/14.19         (~ (zip_tseitin_0 @ X28 @ X29)
% 14.01/14.19          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 14.01/14.19          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 14.01/14.19      inference('cnf', [status(esa)], [zf_stmt_5])).
% 14.01/14.19  thf('104', plain,
% 14.01/14.19      (![X0 : $i, X1 : $i]:
% 14.01/14.19         ((zip_tseitin_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X0 @ X1)
% 14.01/14.19          | ~ (zip_tseitin_0 @ X0 @ X1))),
% 14.01/14.19      inference('sup-', [status(thm)], ['102', '103'])).
% 14.01/14.19  thf('105', plain,
% 14.01/14.19      (![X0 : $i]:
% 14.01/14.19         (zip_tseitin_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0) @ X0 @ k1_xboole_0)),
% 14.01/14.19      inference('sup-', [status(thm)], ['101', '104'])).
% 14.01/14.19  thf('106', plain,
% 14.01/14.19      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 14.01/14.19      inference('simplify', [status(thm)], ['51'])).
% 14.01/14.19  thf('107', plain,
% 14.01/14.19      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 14.01/14.19      inference('demod', [status(thm)], ['105', '106'])).
% 14.01/14.19  thf('108', plain,
% 14.01/14.19      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 14.01/14.19      inference('demod', [status(thm)], ['99', '107'])).
% 14.01/14.19  thf('109', plain, ($false),
% 14.01/14.19      inference('demod', [status(thm)], ['14', '86', '87', '88', '89', '108'])).
% 14.01/14.19  
% 14.01/14.19  % SZS output end Refutation
% 14.01/14.19  
% 14.01/14.20  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
