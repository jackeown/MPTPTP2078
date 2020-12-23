%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hhzkyXwwi2

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:23 EST 2020

% Result     : Theorem 0.56s
% Output     : Refutation 0.56s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 196 expanded)
%              Number of leaves         :   39 (  76 expanded)
%              Depth                    :   20
%              Number of atoms          :  643 (2033 expanded)
%              Number of equality atoms :   34 (  95 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf(t61_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t61_funct_2])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )).

thf('2',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( r2_hidden @ X37 @ X38 )
      | ( X39 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X40 @ X37 ) @ ( k2_relset_1 @ X38 @ X39 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t6_funct_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 @ sk_C_1 ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( sk_B_2 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('5',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k2_relset_1 @ X35 @ X36 @ X34 )
        = ( k2_relat_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('6',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_2 @ sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ ( k2_relat_1 @ sk_C_1 ) )
      | ( sk_B_2 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['3','6','7','8'])).

thf('10',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ ( k2_relat_1 @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v5_relat_1 @ X31 @ X33 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('14',plain,(
    v5_relat_1 @ sk_C_1 @ sk_B_2 ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t56_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ! [B: $i,C: $i] :
            ~ ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
       => ( A = k1_xboole_0 ) ) ) )).

thf('15',plain,(
    ! [X22: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ X22 ) @ ( sk_C @ X22 ) ) @ X22 )
      | ( X22 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t56_relat_1])).

thf('16',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('17',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ( r2_hidden @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ sk_C_1 ) @ ( sk_C @ sk_C_1 ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('21',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v1_relat_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('22',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ sk_C_1 ) @ ( sk_C @ sk_C_1 ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf(t128_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) )
    <=> ( ( A = C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('24',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X12 = X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X12 @ X13 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X11 ) @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t128_zfmisc_1])).

thf('25',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( sk_B_1 @ sk_C_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X22: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ X22 ) @ ( sk_C @ X22 ) ) @ X22 )
      | ( X22 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t56_relat_1])).

thf('27',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_C @ sk_C_1 ) ) @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('29',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_C @ sk_C_1 ) ) @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_C @ sk_C_1 ) ) @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['29'])).

thf(t20_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('31',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X19 @ X20 ) @ X21 )
      | ( r2_hidden @ X19 @ ( k1_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('32',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('34',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(t172_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) )).

thf('35',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X23 @ ( k1_relat_1 @ X24 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X24 @ X23 ) @ X25 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v5_relat_1 @ X24 @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t172_funct_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( sk_C_1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v5_relat_1 @ sk_C_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('38',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( sk_C_1 = k1_xboole_0 )
      | ~ ( v5_relat_1 @ sk_C_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B_2 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','39'])).

thf('41',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['40','41'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('44',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['11','42','43','44'])).

thf('46',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ ( k1_funct_1 @ k1_xboole_0 @ ( sk_B @ ( k1_tarski @ sk_A ) ) ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','45'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('47',plain,(
    ! [X10: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('48',plain,(
    r2_hidden @ ( k1_funct_1 @ k1_xboole_0 @ ( sk_B @ ( k1_tarski @ sk_A ) ) ) @ k1_xboole_0 ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('50',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('51',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('52',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('53',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X26 @ X27 )
      | ~ ( r1_tarski @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['50','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hhzkyXwwi2
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:16:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.56/0.73  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.56/0.73  % Solved by: fo/fo7.sh
% 0.56/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.56/0.73  % done 213 iterations in 0.274s
% 0.56/0.73  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.56/0.73  % SZS output start Refutation
% 0.56/0.73  thf(sk_B_type, type, sk_B: $i > $i).
% 0.56/0.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.56/0.73  thf(sk_C_type, type, sk_C: $i > $i).
% 0.56/0.73  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.56/0.73  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.56/0.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.56/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.56/0.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.56/0.73  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.56/0.73  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.56/0.73  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.56/0.73  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.56/0.73  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.56/0.73  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.56/0.73  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.56/0.73  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.56/0.73  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.56/0.73  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.56/0.73  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.56/0.73  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.56/0.73  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.56/0.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.56/0.73  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.56/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.56/0.73  thf(d1_xboole_0, axiom,
% 0.56/0.73    (![A:$i]:
% 0.56/0.73     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.56/0.73  thf('0', plain,
% 0.56/0.73      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.56/0.73      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.56/0.73  thf(t61_funct_2, conjecture,
% 0.56/0.73    (![A:$i,B:$i,C:$i]:
% 0.56/0.73     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.56/0.73         ( m1_subset_1 @
% 0.56/0.73           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.56/0.73       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.56/0.73         ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ))).
% 0.56/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.56/0.73    (~( ![A:$i,B:$i,C:$i]:
% 0.56/0.73        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.56/0.73            ( m1_subset_1 @
% 0.56/0.73              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.56/0.73          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.56/0.73            ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )),
% 0.56/0.73    inference('cnf.neg', [status(esa)], [t61_funct_2])).
% 0.56/0.73  thf('1', plain,
% 0.56/0.73      ((m1_subset_1 @ sk_C_1 @ 
% 0.56/0.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.56/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.73  thf(t6_funct_2, axiom,
% 0.56/0.73    (![A:$i,B:$i,C:$i,D:$i]:
% 0.56/0.73     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.56/0.73         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.56/0.73       ( ( r2_hidden @ C @ A ) =>
% 0.56/0.73         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.56/0.73           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.56/0.73  thf('2', plain,
% 0.56/0.73      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.56/0.73         (~ (r2_hidden @ X37 @ X38)
% 0.56/0.73          | ((X39) = (k1_xboole_0))
% 0.56/0.73          | ~ (v1_funct_1 @ X40)
% 0.56/0.73          | ~ (v1_funct_2 @ X40 @ X38 @ X39)
% 0.56/0.73          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.56/0.73          | (r2_hidden @ (k1_funct_1 @ X40 @ X37) @ 
% 0.56/0.73             (k2_relset_1 @ X38 @ X39 @ X40)))),
% 0.56/0.73      inference('cnf', [status(esa)], [t6_funct_2])).
% 0.56/0.73  thf('3', plain,
% 0.56/0.73      (![X0 : $i]:
% 0.56/0.73         ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ 
% 0.56/0.73           (k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_2 @ sk_C_1))
% 0.56/0.73          | ~ (v1_funct_2 @ sk_C_1 @ (k1_tarski @ sk_A) @ sk_B_2)
% 0.56/0.73          | ~ (v1_funct_1 @ sk_C_1)
% 0.56/0.73          | ((sk_B_2) = (k1_xboole_0))
% 0.56/0.73          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.56/0.73      inference('sup-', [status(thm)], ['1', '2'])).
% 0.56/0.73  thf('4', plain,
% 0.56/0.73      ((m1_subset_1 @ sk_C_1 @ 
% 0.56/0.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.56/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.73  thf(redefinition_k2_relset_1, axiom,
% 0.56/0.73    (![A:$i,B:$i,C:$i]:
% 0.56/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.56/0.73       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.56/0.73  thf('5', plain,
% 0.56/0.73      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.56/0.73         (((k2_relset_1 @ X35 @ X36 @ X34) = (k2_relat_1 @ X34))
% 0.56/0.73          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.56/0.73      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.56/0.73  thf('6', plain,
% 0.56/0.73      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_2 @ sk_C_1)
% 0.56/0.73         = (k2_relat_1 @ sk_C_1))),
% 0.56/0.73      inference('sup-', [status(thm)], ['4', '5'])).
% 0.56/0.73  thf('7', plain, ((v1_funct_2 @ sk_C_1 @ (k1_tarski @ sk_A) @ sk_B_2)),
% 0.56/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.73  thf('8', plain, ((v1_funct_1 @ sk_C_1)),
% 0.56/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.73  thf('9', plain,
% 0.56/0.73      (![X0 : $i]:
% 0.56/0.73         ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ (k2_relat_1 @ sk_C_1))
% 0.56/0.73          | ((sk_B_2) = (k1_xboole_0))
% 0.56/0.73          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.56/0.73      inference('demod', [status(thm)], ['3', '6', '7', '8'])).
% 0.56/0.73  thf('10', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.56/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.73  thf('11', plain,
% 0.56/0.73      (![X0 : $i]:
% 0.56/0.73         ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ (k2_relat_1 @ sk_C_1))
% 0.56/0.73          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.56/0.73      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.56/0.73  thf('12', plain,
% 0.56/0.73      ((m1_subset_1 @ sk_C_1 @ 
% 0.56/0.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.56/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.73  thf(cc2_relset_1, axiom,
% 0.56/0.73    (![A:$i,B:$i,C:$i]:
% 0.56/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.56/0.73       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.56/0.73  thf('13', plain,
% 0.56/0.73      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.56/0.73         ((v5_relat_1 @ X31 @ X33)
% 0.56/0.73          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.56/0.73      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.56/0.73  thf('14', plain, ((v5_relat_1 @ sk_C_1 @ sk_B_2)),
% 0.56/0.73      inference('sup-', [status(thm)], ['12', '13'])).
% 0.56/0.73  thf(t56_relat_1, axiom,
% 0.56/0.73    (![A:$i]:
% 0.56/0.73     ( ( v1_relat_1 @ A ) =>
% 0.56/0.73       ( ( ![B:$i,C:$i]: ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) =>
% 0.56/0.73         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.56/0.73  thf('15', plain,
% 0.56/0.73      (![X22 : $i]:
% 0.56/0.73         ((r2_hidden @ (k4_tarski @ (sk_B_1 @ X22) @ (sk_C @ X22)) @ X22)
% 0.56/0.73          | ((X22) = (k1_xboole_0))
% 0.56/0.73          | ~ (v1_relat_1 @ X22))),
% 0.56/0.73      inference('cnf', [status(esa)], [t56_relat_1])).
% 0.56/0.73  thf('16', plain,
% 0.56/0.73      ((m1_subset_1 @ sk_C_1 @ 
% 0.56/0.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.56/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.73  thf(l3_subset_1, axiom,
% 0.56/0.73    (![A:$i,B:$i]:
% 0.56/0.73     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.56/0.73       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.56/0.73  thf('17', plain,
% 0.56/0.73      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.56/0.73         (~ (r2_hidden @ X16 @ X17)
% 0.56/0.73          | (r2_hidden @ X16 @ X18)
% 0.56/0.73          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 0.56/0.73      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.56/0.73  thf('18', plain,
% 0.56/0.73      (![X0 : $i]:
% 0.56/0.73         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2))
% 0.56/0.73          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.56/0.73      inference('sup-', [status(thm)], ['16', '17'])).
% 0.56/0.73  thf('19', plain,
% 0.56/0.73      ((~ (v1_relat_1 @ sk_C_1)
% 0.56/0.73        | ((sk_C_1) = (k1_xboole_0))
% 0.56/0.73        | (r2_hidden @ (k4_tarski @ (sk_B_1 @ sk_C_1) @ (sk_C @ sk_C_1)) @ 
% 0.56/0.73           (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.56/0.73      inference('sup-', [status(thm)], ['15', '18'])).
% 0.56/0.73  thf('20', plain,
% 0.56/0.73      ((m1_subset_1 @ sk_C_1 @ 
% 0.56/0.73        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.56/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.73  thf(cc1_relset_1, axiom,
% 0.56/0.73    (![A:$i,B:$i,C:$i]:
% 0.56/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.56/0.73       ( v1_relat_1 @ C ) ))).
% 0.56/0.73  thf('21', plain,
% 0.56/0.73      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.56/0.73         ((v1_relat_1 @ X28)
% 0.56/0.73          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.56/0.73      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.56/0.73  thf('22', plain, ((v1_relat_1 @ sk_C_1)),
% 0.56/0.73      inference('sup-', [status(thm)], ['20', '21'])).
% 0.56/0.73  thf('23', plain,
% 0.56/0.73      ((((sk_C_1) = (k1_xboole_0))
% 0.56/0.73        | (r2_hidden @ (k4_tarski @ (sk_B_1 @ sk_C_1) @ (sk_C @ sk_C_1)) @ 
% 0.56/0.73           (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.56/0.73      inference('demod', [status(thm)], ['19', '22'])).
% 0.56/0.73  thf(t128_zfmisc_1, axiom,
% 0.56/0.73    (![A:$i,B:$i,C:$i,D:$i]:
% 0.56/0.73     ( ( r2_hidden @
% 0.56/0.73         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 0.56/0.73       ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ))).
% 0.56/0.73  thf('24', plain,
% 0.56/0.73      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.56/0.73         (((X12) = (X11))
% 0.56/0.73          | ~ (r2_hidden @ (k4_tarski @ X12 @ X13) @ 
% 0.56/0.73               (k2_zfmisc_1 @ (k1_tarski @ X11) @ X14)))),
% 0.56/0.73      inference('cnf', [status(esa)], [t128_zfmisc_1])).
% 0.56/0.73  thf('25', plain,
% 0.56/0.73      ((((sk_C_1) = (k1_xboole_0)) | ((sk_B_1 @ sk_C_1) = (sk_A)))),
% 0.56/0.73      inference('sup-', [status(thm)], ['23', '24'])).
% 0.56/0.73  thf('26', plain,
% 0.56/0.73      (![X22 : $i]:
% 0.56/0.73         ((r2_hidden @ (k4_tarski @ (sk_B_1 @ X22) @ (sk_C @ X22)) @ X22)
% 0.56/0.73          | ((X22) = (k1_xboole_0))
% 0.56/0.73          | ~ (v1_relat_1 @ X22))),
% 0.56/0.73      inference('cnf', [status(esa)], [t56_relat_1])).
% 0.56/0.73  thf('27', plain,
% 0.56/0.73      (((r2_hidden @ (k4_tarski @ sk_A @ (sk_C @ sk_C_1)) @ sk_C_1)
% 0.56/0.73        | ((sk_C_1) = (k1_xboole_0))
% 0.56/0.73        | ~ (v1_relat_1 @ sk_C_1)
% 0.56/0.73        | ((sk_C_1) = (k1_xboole_0)))),
% 0.56/0.73      inference('sup+', [status(thm)], ['25', '26'])).
% 0.56/0.73  thf('28', plain, ((v1_relat_1 @ sk_C_1)),
% 0.56/0.73      inference('sup-', [status(thm)], ['20', '21'])).
% 0.56/0.73  thf('29', plain,
% 0.56/0.73      (((r2_hidden @ (k4_tarski @ sk_A @ (sk_C @ sk_C_1)) @ sk_C_1)
% 0.56/0.73        | ((sk_C_1) = (k1_xboole_0))
% 0.56/0.73        | ((sk_C_1) = (k1_xboole_0)))),
% 0.56/0.73      inference('demod', [status(thm)], ['27', '28'])).
% 0.56/0.73  thf('30', plain,
% 0.56/0.73      ((((sk_C_1) = (k1_xboole_0))
% 0.56/0.73        | (r2_hidden @ (k4_tarski @ sk_A @ (sk_C @ sk_C_1)) @ sk_C_1))),
% 0.56/0.73      inference('simplify', [status(thm)], ['29'])).
% 0.56/0.73  thf(t20_relat_1, axiom,
% 0.56/0.73    (![A:$i,B:$i,C:$i]:
% 0.56/0.73     ( ( v1_relat_1 @ C ) =>
% 0.56/0.73       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.56/0.73         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.56/0.73           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 0.56/0.73  thf('31', plain,
% 0.56/0.73      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.56/0.73         (~ (r2_hidden @ (k4_tarski @ X19 @ X20) @ X21)
% 0.56/0.73          | (r2_hidden @ X19 @ (k1_relat_1 @ X21))
% 0.56/0.73          | ~ (v1_relat_1 @ X21))),
% 0.56/0.73      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.56/0.73  thf('32', plain,
% 0.56/0.73      ((((sk_C_1) = (k1_xboole_0))
% 0.56/0.73        | ~ (v1_relat_1 @ sk_C_1)
% 0.56/0.73        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1)))),
% 0.56/0.73      inference('sup-', [status(thm)], ['30', '31'])).
% 0.56/0.73  thf('33', plain, ((v1_relat_1 @ sk_C_1)),
% 0.56/0.73      inference('sup-', [status(thm)], ['20', '21'])).
% 0.56/0.73  thf('34', plain,
% 0.56/0.73      ((((sk_C_1) = (k1_xboole_0)) | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1)))),
% 0.56/0.73      inference('demod', [status(thm)], ['32', '33'])).
% 0.56/0.73  thf(t172_funct_1, axiom,
% 0.56/0.73    (![A:$i,B:$i]:
% 0.56/0.73     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 0.56/0.73       ( ![C:$i]:
% 0.56/0.73         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.56/0.73           ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) ))).
% 0.56/0.73  thf('35', plain,
% 0.56/0.73      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.56/0.73         (~ (r2_hidden @ X23 @ (k1_relat_1 @ X24))
% 0.56/0.73          | (r2_hidden @ (k1_funct_1 @ X24 @ X23) @ X25)
% 0.56/0.73          | ~ (v1_funct_1 @ X24)
% 0.56/0.73          | ~ (v5_relat_1 @ X24 @ X25)
% 0.56/0.73          | ~ (v1_relat_1 @ X24))),
% 0.56/0.73      inference('cnf', [status(esa)], [t172_funct_1])).
% 0.56/0.73  thf('36', plain,
% 0.56/0.73      (![X0 : $i]:
% 0.56/0.73         (((sk_C_1) = (k1_xboole_0))
% 0.56/0.73          | ~ (v1_relat_1 @ sk_C_1)
% 0.56/0.73          | ~ (v5_relat_1 @ sk_C_1 @ X0)
% 0.56/0.73          | ~ (v1_funct_1 @ sk_C_1)
% 0.56/0.73          | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ X0))),
% 0.56/0.73      inference('sup-', [status(thm)], ['34', '35'])).
% 0.56/0.73  thf('37', plain, ((v1_relat_1 @ sk_C_1)),
% 0.56/0.73      inference('sup-', [status(thm)], ['20', '21'])).
% 0.56/0.73  thf('38', plain, ((v1_funct_1 @ sk_C_1)),
% 0.56/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.73  thf('39', plain,
% 0.56/0.73      (![X0 : $i]:
% 0.56/0.73         (((sk_C_1) = (k1_xboole_0))
% 0.56/0.73          | ~ (v5_relat_1 @ sk_C_1 @ X0)
% 0.56/0.73          | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ X0))),
% 0.56/0.73      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.56/0.73  thf('40', plain,
% 0.56/0.73      (((r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B_2)
% 0.56/0.73        | ((sk_C_1) = (k1_xboole_0)))),
% 0.56/0.73      inference('sup-', [status(thm)], ['14', '39'])).
% 0.56/0.73  thf('41', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B_2)),
% 0.56/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.73  thf('42', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.56/0.73      inference('clc', [status(thm)], ['40', '41'])).
% 0.56/0.73  thf('43', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.56/0.73      inference('clc', [status(thm)], ['40', '41'])).
% 0.56/0.73  thf(t60_relat_1, axiom,
% 0.56/0.73    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.56/0.73     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.56/0.73  thf('44', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.56/0.73      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.56/0.73  thf('45', plain,
% 0.56/0.73      (![X0 : $i]:
% 0.56/0.73         ((r2_hidden @ (k1_funct_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.56/0.73          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.56/0.73      inference('demod', [status(thm)], ['11', '42', '43', '44'])).
% 0.56/0.73  thf('46', plain,
% 0.56/0.73      (((v1_xboole_0 @ (k1_tarski @ sk_A))
% 0.56/0.73        | (r2_hidden @ 
% 0.56/0.73           (k1_funct_1 @ k1_xboole_0 @ (sk_B @ (k1_tarski @ sk_A))) @ 
% 0.56/0.73           k1_xboole_0))),
% 0.56/0.73      inference('sup-', [status(thm)], ['0', '45'])).
% 0.56/0.73  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.56/0.73  thf('47', plain, (![X10 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X10))),
% 0.56/0.73      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.56/0.73  thf('48', plain,
% 0.56/0.73      ((r2_hidden @ (k1_funct_1 @ k1_xboole_0 @ (sk_B @ (k1_tarski @ sk_A))) @ 
% 0.56/0.73        k1_xboole_0)),
% 0.56/0.73      inference('clc', [status(thm)], ['46', '47'])).
% 0.56/0.73  thf('49', plain,
% 0.56/0.73      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.56/0.73      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.56/0.73  thf('50', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.56/0.73      inference('sup-', [status(thm)], ['48', '49'])).
% 0.56/0.73  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.56/0.73  thf('51', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.56/0.73      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.56/0.73  thf('52', plain,
% 0.56/0.73      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.56/0.73      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.56/0.73  thf(t7_ordinal1, axiom,
% 0.56/0.73    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.56/0.73  thf('53', plain,
% 0.56/0.73      (![X26 : $i, X27 : $i]:
% 0.56/0.73         (~ (r2_hidden @ X26 @ X27) | ~ (r1_tarski @ X27 @ X26))),
% 0.56/0.73      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.56/0.73  thf('54', plain,
% 0.56/0.73      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.56/0.73      inference('sup-', [status(thm)], ['52', '53'])).
% 0.56/0.73  thf('55', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.56/0.73      inference('sup-', [status(thm)], ['51', '54'])).
% 0.56/0.73  thf('56', plain, ($false), inference('demod', [status(thm)], ['50', '55'])).
% 0.56/0.73  
% 0.56/0.73  % SZS output end Refutation
% 0.56/0.73  
% 0.56/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
