%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aHIZKlGu3t

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 222 expanded)
%              Number of leaves         :   34 (  80 expanded)
%              Depth                    :   14
%              Number of atoms          :  655 (2721 expanded)
%              Number of equality atoms :   55 ( 207 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

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

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X13 @ X14 )
      | ~ ( r1_tarski @ ( k2_tarski @ X13 @ X15 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf(t62_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C )
          = ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C )
            = ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_funct_2])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )).

thf('7',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( r2_hidden @ X33 @ X34 )
      | ( X35 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_2 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X36 @ X33 ) @ ( k2_relset_1 @ X34 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t6_funct_2])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C ) )
      | ~ ( v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_C )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('10',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X30 @ X28 )
        = ( k2_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('11',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ ( k2_relat_1 @ sk_C ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['8','11','12','13'])).

thf('15',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ ( k2_relat_1 @ sk_C ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

thf('17',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['5','16'])).

thf('18',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['5','16'])).

thf('19',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X13 @ X15 ) @ X16 )
      | ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r2_hidden @ X13 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C ) )
      | ( r1_tarski @ ( k2_tarski @ X0 @ ( k1_funct_1 @ sk_C @ sk_A ) ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    r1_tarski @ ( k2_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k1_funct_1 @ sk_C @ sk_A ) ) @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('23',plain,(
    r1_tarski @ ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('28',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['25','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('31',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v4_relat_1 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('32',plain,(
    v4_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('33',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v4_relat_1 @ X17 @ X18 )
      | ( r1_tarski @ ( k1_relat_1 @ X17 ) @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('36',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('37',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['34','37'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('39',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X11
        = ( k1_tarski @ X10 ) )
      | ( X11 = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('40',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('41',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k1_relat_1 @ X21 )
       != ( k1_tarski @ X20 ) )
      | ( ( k2_relat_1 @ X21 )
        = ( k1_tarski @ ( k1_funct_1 @ X21 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_C ) )
      | ( ( k1_relat_1 @ sk_C )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['42'])).

thf('44',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['35','36'])).

thf('46',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('48',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['46','47'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('49',plain,(
    ! [X19: $i] :
      ( ( ( k1_relat_1 @ X19 )
       != k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('50',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['35','36'])).

thf('52',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['52'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('54',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('55',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['52'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('56',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('57',plain,(
    $false ),
    inference(demod,[status(thm)],['29','53','54','55','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aHIZKlGu3t
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:14:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 175 iterations in 0.076s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.53  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.53  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.53  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.53  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.53  thf(t69_enumset1, axiom,
% 0.21/0.53    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.53  thf('0', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.21/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.53  thf(d10_xboole_0, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.53  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.53      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.53  thf(t38_zfmisc_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.21/0.53       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.53         ((r2_hidden @ X13 @ X14)
% 0.21/0.53          | ~ (r1_tarski @ (k2_tarski @ X13 @ X15) @ X14))),
% 0.21/0.53      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.53  thf('5', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['0', '4'])).
% 0.21/0.53  thf(t62_funct_2, conjecture,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.21/0.53         ( m1_subset_1 @
% 0.21/0.53           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.21/0.53       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.21/0.53         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.21/0.53           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.53        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.21/0.53            ( m1_subset_1 @
% 0.21/0.53              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.21/0.53          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.21/0.53            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.21/0.53              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_C @ 
% 0.21/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t6_funct_2, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.53     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.53         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.53       ( ( r2_hidden @ C @ A ) =>
% 0.21/0.53         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.53           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.21/0.53  thf('7', plain,
% 0.21/0.53      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X33 @ X34)
% 0.21/0.53          | ((X35) = (k1_xboole_0))
% 0.21/0.53          | ~ (v1_funct_1 @ X36)
% 0.21/0.53          | ~ (v1_funct_2 @ X36 @ X34 @ X35)
% 0.21/0.53          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.21/0.53          | (r2_hidden @ (k1_funct_1 @ X36 @ X33) @ 
% 0.21/0.53             (k2_relset_1 @ X34 @ X35 @ X36)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t6_funct_2])).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ 
% 0.21/0.53           (k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C))
% 0.21/0.53          | ~ (v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.21/0.53          | ~ (v1_funct_1 @ sk_C)
% 0.21/0.53          | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.53          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_C @ 
% 0.21/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.53       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.53  thf('10', plain,
% 0.21/0.53      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.21/0.53         (((k2_relset_1 @ X29 @ X30 @ X28) = (k2_relat_1 @ X28))
% 0.21/0.53          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.21/0.53      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 0.21/0.53         = (k2_relat_1 @ sk_C))),
% 0.21/0.53      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.53  thf('12', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ (k2_relat_1 @ sk_C))
% 0.21/0.53          | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.53          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['8', '11', '12', '13'])).
% 0.21/0.53  thf('15', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ (k2_relat_1 @ sk_C))
% 0.21/0.53          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.21/0.53      inference('sup-', [status(thm)], ['5', '16'])).
% 0.21/0.53  thf('18', plain,
% 0.21/0.53      ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.21/0.53      inference('sup-', [status(thm)], ['5', '16'])).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.21/0.53         ((r1_tarski @ (k2_tarski @ X13 @ X15) @ X16)
% 0.21/0.53          | ~ (r2_hidden @ X15 @ X16)
% 0.21/0.53          | ~ (r2_hidden @ X13 @ X16))),
% 0.21/0.53      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C))
% 0.21/0.53          | (r1_tarski @ (k2_tarski @ X0 @ (k1_funct_1 @ sk_C @ sk_A)) @ 
% 0.21/0.53             (k2_relat_1 @ sk_C)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.53  thf('21', plain,
% 0.21/0.53      ((r1_tarski @ 
% 0.21/0.53        (k2_tarski @ (k1_funct_1 @ sk_C @ sk_A) @ (k1_funct_1 @ sk_C @ sk_A)) @ 
% 0.21/0.53        (k2_relat_1 @ sk_C))),
% 0.21/0.53      inference('sup-', [status(thm)], ['17', '20'])).
% 0.21/0.53  thf('22', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.21/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      ((r1_tarski @ (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)) @ 
% 0.21/0.53        (k2_relat_1 @ sk_C))),
% 0.21/0.53      inference('demod', [status(thm)], ['21', '22'])).
% 0.21/0.53  thf('24', plain,
% 0.21/0.53      (![X0 : $i, X2 : $i]:
% 0.21/0.53         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.53  thf('25', plain,
% 0.21/0.53      ((~ (r1_tarski @ (k2_relat_1 @ sk_C) @ 
% 0.21/0.53           (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 0.21/0.53        | ((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.53  thf('26', plain,
% 0.21/0.53      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 0.21/0.53         != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('27', plain,
% 0.21/0.53      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 0.21/0.53         = (k2_relat_1 @ sk_C))),
% 0.21/0.53      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.53  thf('28', plain,
% 0.21/0.53      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.53  thf('29', plain,
% 0.21/0.53      (~ (r1_tarski @ (k2_relat_1 @ sk_C) @ 
% 0.21/0.53          (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['25', '28'])).
% 0.21/0.53  thf('30', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_C @ 
% 0.21/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(cc2_relset_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.53       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.53  thf('31', plain,
% 0.21/0.53      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.21/0.53         ((v4_relat_1 @ X25 @ X26)
% 0.21/0.53          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.21/0.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.53  thf('32', plain, ((v4_relat_1 @ sk_C @ (k1_tarski @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.53  thf(d18_relat_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ B ) =>
% 0.21/0.53       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.53  thf('33', plain,
% 0.21/0.53      (![X17 : $i, X18 : $i]:
% 0.21/0.53         (~ (v4_relat_1 @ X17 @ X18)
% 0.21/0.53          | (r1_tarski @ (k1_relat_1 @ X17) @ X18)
% 0.21/0.53          | ~ (v1_relat_1 @ X17))),
% 0.21/0.53      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.21/0.53  thf('34', plain,
% 0.21/0.53      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.53        | (r1_tarski @ (k1_relat_1 @ sk_C) @ (k1_tarski @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.53  thf('35', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_C @ 
% 0.21/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(cc1_relset_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.53       ( v1_relat_1 @ C ) ))).
% 0.21/0.53  thf('36', plain,
% 0.21/0.53      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.53         ((v1_relat_1 @ X22)
% 0.21/0.53          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.21/0.53      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.53  thf('37', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.53      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.53  thf('38', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ (k1_tarski @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['34', '37'])).
% 0.21/0.53  thf(l3_zfmisc_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.21/0.53       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.21/0.53  thf('39', plain,
% 0.21/0.53      (![X10 : $i, X11 : $i]:
% 0.21/0.53         (((X11) = (k1_tarski @ X10))
% 0.21/0.53          | ((X11) = (k1_xboole_0))
% 0.21/0.53          | ~ (r1_tarski @ X11 @ (k1_tarski @ X10)))),
% 0.21/0.53      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.21/0.53  thf('40', plain,
% 0.21/0.53      ((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 0.21/0.53        | ((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.53  thf(t14_funct_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.53       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.21/0.53         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.21/0.53  thf('41', plain,
% 0.21/0.53      (![X20 : $i, X21 : $i]:
% 0.21/0.53         (((k1_relat_1 @ X21) != (k1_tarski @ X20))
% 0.21/0.53          | ((k2_relat_1 @ X21) = (k1_tarski @ (k1_funct_1 @ X21 @ X20)))
% 0.21/0.53          | ~ (v1_funct_1 @ X21)
% 0.21/0.53          | ~ (v1_relat_1 @ X21))),
% 0.21/0.53      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.21/0.53  thf('42', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_C))
% 0.21/0.53          | ((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 0.21/0.53          | ~ (v1_relat_1 @ X0)
% 0.21/0.53          | ~ (v1_funct_1 @ X0)
% 0.21/0.53          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.53  thf('43', plain,
% 0.21/0.53      ((((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 0.21/0.53        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.53        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.53        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.21/0.53      inference('eq_res', [status(thm)], ['42'])).
% 0.21/0.53  thf('44', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('45', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.53      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.53  thf('46', plain,
% 0.21/0.53      ((((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 0.21/0.53        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.21/0.53      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.21/0.53  thf('47', plain,
% 0.21/0.53      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.53  thf('48', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['46', '47'])).
% 0.21/0.53  thf(t64_relat_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ A ) =>
% 0.21/0.53       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.53           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.53         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.53  thf('49', plain,
% 0.21/0.53      (![X19 : $i]:
% 0.21/0.53         (((k1_relat_1 @ X19) != (k1_xboole_0))
% 0.21/0.53          | ((X19) = (k1_xboole_0))
% 0.21/0.53          | ~ (v1_relat_1 @ X19))),
% 0.21/0.53      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.21/0.53  thf('50', plain,
% 0.21/0.53      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.53        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.53        | ((sk_C) = (k1_xboole_0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['48', '49'])).
% 0.21/0.53  thf('51', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.53      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.53  thf('52', plain,
% 0.21/0.53      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.21/0.53      inference('demod', [status(thm)], ['50', '51'])).
% 0.21/0.53  thf('53', plain, (((sk_C) = (k1_xboole_0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['52'])).
% 0.21/0.53  thf(t60_relat_1, axiom,
% 0.21/0.53    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.53     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.53  thf('54', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.53  thf('55', plain, (((sk_C) = (k1_xboole_0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['52'])).
% 0.21/0.53  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.53  thf('56', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.21/0.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.53  thf('57', plain, ($false),
% 0.21/0.53      inference('demod', [status(thm)], ['29', '53', '54', '55', '56'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
