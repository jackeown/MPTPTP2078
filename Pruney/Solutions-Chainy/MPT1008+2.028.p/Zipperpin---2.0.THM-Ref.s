%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SYXzmAQNC3

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 426 expanded)
%              Number of leaves         :   37 ( 141 expanded)
%              Depth                    :   20
%              Number of atoms          :  765 (5142 expanded)
%              Number of equality atoms :   74 ( 420 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

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

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
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
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( r2_hidden @ X41 @ X42 )
      | ( X43 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_2 @ X44 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X44 @ X41 ) @ ( k2_relset_1 @ X42 @ X43 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t6_funct_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_B )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('5',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( ( k2_relset_1 @ X39 @ X40 @ X38 )
        = ( k2_relat_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('6',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_2 @ sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ ( k2_relat_1 @ sk_C_1 ) )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['3','6','7','8'])).

thf('10',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ ( k2_relat_1 @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ ( sk_C @ X0 @ ( k1_tarski @ sk_A ) ) ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['0','11'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('13',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X30 @ X31 )
      | ~ ( r1_tarski @ X31 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ ( k1_funct_1 @ sk_C_1 @ ( sk_C @ X0 @ ( k1_tarski @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('16',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( v4_relat_1 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('17',plain,(
    v4_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X23: $i,X24: $i] :
      ( ( X23
        = ( k7_relat_1 @ X23 @ X24 ) )
      | ~ ( v4_relat_1 @ X23 @ X24 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1
      = ( k7_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('21',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v1_relat_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('22',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( sk_C_1
    = ( k7_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('24',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X26 @ X27 ) ) @ X27 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('25',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_tarski @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('27',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('28',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X14
        = ( k1_tarski @ X13 ) )
      | ( X14 = k1_xboole_0 )
      | ~ ( r1_tarski @ X14 @ ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('29',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('30',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k1_relat_1 @ X29 )
       != ( k1_tarski @ X28 ) )
      | ( ( k2_relat_1 @ X29 )
        = ( k1_tarski @ ( k1_funct_1 @ X29 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_C_1 ) )
      | ( ( k1_relat_1 @ sk_C_1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['31'])).

thf('33',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('35',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('38',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['35','38'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('40',plain,(
    ! [X25: $i] :
      ( ( ( k1_relat_1 @ X25 )
       != k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('41',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('43',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['43'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('45',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('46',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['43'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('47',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('48',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('49',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 ) ),
    inference(demod,[status(thm)],['14','44','45','46','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('52',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('56',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k1_relat_1 @ X29 )
       != ( k1_tarski @ X28 ) )
      | ( ( k2_relat_1 @ X29 )
        = ( k1_tarski @ ( k1_funct_1 @ X29 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('59',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v1_relat_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('60',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['57','60','61'])).

thf('63',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['43'])).

thf('65',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ( k1_xboole_0
        = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['62','65'])).

thf('67',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['54','66'])).

thf('68',plain,
    ( k1_xboole_0
    = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('70',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['43'])).

thf('71',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('72',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['43'])).

thf('73',plain,(
    k1_xboole_0
 != ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70','71','72'])).

thf('74',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['68','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SYXzmAQNC3
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:12:48 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.59  % Solved by: fo/fo7.sh
% 0.20/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.59  % done 249 iterations in 0.133s
% 0.20/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.59  % SZS output start Refutation
% 0.20/0.59  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.59  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.59  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.59  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.59  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.59  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.59  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.59  thf(d3_tarski, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.59       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.59  thf('0', plain,
% 0.20/0.59      (![X1 : $i, X3 : $i]:
% 0.20/0.59         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.59      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.59  thf(t62_funct_2, conjecture,
% 0.20/0.59    (![A:$i,B:$i,C:$i]:
% 0.20/0.59     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.20/0.59         ( m1_subset_1 @
% 0.20/0.59           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.20/0.59       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.59         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.20/0.59           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.20/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.59    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.59        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.20/0.59            ( m1_subset_1 @
% 0.20/0.59              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.20/0.59          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.59            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.20/0.59              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 0.20/0.59    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 0.20/0.59  thf('1', plain,
% 0.20/0.59      ((m1_subset_1 @ sk_C_1 @ 
% 0.20/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf(t6_funct_2, axiom,
% 0.20/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.59     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.59         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.59       ( ( r2_hidden @ C @ A ) =>
% 0.20/0.59         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.59           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.20/0.59  thf('2', plain,
% 0.20/0.59      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.20/0.59         (~ (r2_hidden @ X41 @ X42)
% 0.20/0.59          | ((X43) = (k1_xboole_0))
% 0.20/0.59          | ~ (v1_funct_1 @ X44)
% 0.20/0.59          | ~ (v1_funct_2 @ X44 @ X42 @ X43)
% 0.20/0.59          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 0.20/0.59          | (r2_hidden @ (k1_funct_1 @ X44 @ X41) @ 
% 0.20/0.59             (k2_relset_1 @ X42 @ X43 @ X44)))),
% 0.20/0.59      inference('cnf', [status(esa)], [t6_funct_2])).
% 0.20/0.59  thf('3', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ 
% 0.20/0.59           (k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1))
% 0.20/0.59          | ~ (v1_funct_2 @ sk_C_1 @ (k1_tarski @ sk_A) @ sk_B)
% 0.20/0.59          | ~ (v1_funct_1 @ sk_C_1)
% 0.20/0.59          | ((sk_B) = (k1_xboole_0))
% 0.20/0.59          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.59  thf('4', plain,
% 0.20/0.59      ((m1_subset_1 @ sk_C_1 @ 
% 0.20/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.59    (![A:$i,B:$i,C:$i]:
% 0.20/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.59       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.59  thf('5', plain,
% 0.20/0.59      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.20/0.59         (((k2_relset_1 @ X39 @ X40 @ X38) = (k2_relat_1 @ X38))
% 0.20/0.59          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40))))),
% 0.20/0.59      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.59  thf('6', plain,
% 0.20/0.59      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1)
% 0.20/0.59         = (k2_relat_1 @ sk_C_1))),
% 0.20/0.59      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.59  thf('7', plain, ((v1_funct_2 @ sk_C_1 @ (k1_tarski @ sk_A) @ sk_B)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('8', plain, ((v1_funct_1 @ sk_C_1)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('9', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ (k2_relat_1 @ sk_C_1))
% 0.20/0.59          | ((sk_B) = (k1_xboole_0))
% 0.20/0.59          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.20/0.59      inference('demod', [status(thm)], ['3', '6', '7', '8'])).
% 0.20/0.59  thf('10', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('11', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ (k2_relat_1 @ sk_C_1))
% 0.20/0.59          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.20/0.59      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.20/0.59  thf('12', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         ((r1_tarski @ (k1_tarski @ sk_A) @ X0)
% 0.20/0.59          | (r2_hidden @ 
% 0.20/0.59             (k1_funct_1 @ sk_C_1 @ (sk_C @ X0 @ (k1_tarski @ sk_A))) @ 
% 0.20/0.59             (k2_relat_1 @ sk_C_1)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['0', '11'])).
% 0.20/0.59  thf(t7_ordinal1, axiom,
% 0.20/0.59    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.59  thf('13', plain,
% 0.20/0.59      (![X30 : $i, X31 : $i]:
% 0.20/0.59         (~ (r2_hidden @ X30 @ X31) | ~ (r1_tarski @ X31 @ X30))),
% 0.20/0.59      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.20/0.59  thf('14', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         ((r1_tarski @ (k1_tarski @ sk_A) @ X0)
% 0.20/0.59          | ~ (r1_tarski @ (k2_relat_1 @ sk_C_1) @ 
% 0.20/0.59               (k1_funct_1 @ sk_C_1 @ (sk_C @ X0 @ (k1_tarski @ sk_A)))))),
% 0.20/0.59      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.59  thf('15', plain,
% 0.20/0.59      ((m1_subset_1 @ sk_C_1 @ 
% 0.20/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf(cc2_relset_1, axiom,
% 0.20/0.59    (![A:$i,B:$i,C:$i]:
% 0.20/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.59       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.59  thf('16', plain,
% 0.20/0.59      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.20/0.59         ((v4_relat_1 @ X35 @ X36)
% 0.20/0.59          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 0.20/0.59      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.59  thf('17', plain, ((v4_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A))),
% 0.20/0.59      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.59  thf(t209_relat_1, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.20/0.59       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.20/0.59  thf('18', plain,
% 0.20/0.59      (![X23 : $i, X24 : $i]:
% 0.20/0.59         (((X23) = (k7_relat_1 @ X23 @ X24))
% 0.20/0.59          | ~ (v4_relat_1 @ X23 @ X24)
% 0.20/0.59          | ~ (v1_relat_1 @ X23))),
% 0.20/0.59      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.20/0.59  thf('19', plain,
% 0.20/0.59      ((~ (v1_relat_1 @ sk_C_1)
% 0.20/0.59        | ((sk_C_1) = (k7_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A))))),
% 0.20/0.59      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.59  thf('20', plain,
% 0.20/0.59      ((m1_subset_1 @ sk_C_1 @ 
% 0.20/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf(cc1_relset_1, axiom,
% 0.20/0.59    (![A:$i,B:$i,C:$i]:
% 0.20/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.59       ( v1_relat_1 @ C ) ))).
% 0.20/0.59  thf('21', plain,
% 0.20/0.59      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.20/0.59         ((v1_relat_1 @ X32)
% 0.20/0.59          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.20/0.59      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.59  thf('22', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.59      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.59  thf('23', plain, (((sk_C_1) = (k7_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A)))),
% 0.20/0.59      inference('demod', [status(thm)], ['19', '22'])).
% 0.20/0.59  thf(t87_relat_1, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( v1_relat_1 @ B ) =>
% 0.20/0.59       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.20/0.59  thf('24', plain,
% 0.20/0.59      (![X26 : $i, X27 : $i]:
% 0.20/0.59         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X26 @ X27)) @ X27)
% 0.20/0.59          | ~ (v1_relat_1 @ X26))),
% 0.20/0.59      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.20/0.59  thf('25', plain,
% 0.20/0.59      (((r1_tarski @ (k1_relat_1 @ sk_C_1) @ (k1_tarski @ sk_A))
% 0.20/0.59        | ~ (v1_relat_1 @ sk_C_1))),
% 0.20/0.59      inference('sup+', [status(thm)], ['23', '24'])).
% 0.20/0.59  thf('26', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.59      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.59  thf('27', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ (k1_tarski @ sk_A))),
% 0.20/0.59      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.59  thf(l3_zfmisc_1, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.20/0.59       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.20/0.59  thf('28', plain,
% 0.20/0.59      (![X13 : $i, X14 : $i]:
% 0.20/0.59         (((X14) = (k1_tarski @ X13))
% 0.20/0.59          | ((X14) = (k1_xboole_0))
% 0.20/0.59          | ~ (r1_tarski @ X14 @ (k1_tarski @ X13)))),
% 0.20/0.59      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.20/0.59  thf('29', plain,
% 0.20/0.59      ((((k1_relat_1 @ sk_C_1) = (k1_xboole_0))
% 0.20/0.59        | ((k1_relat_1 @ sk_C_1) = (k1_tarski @ sk_A)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.59  thf(t14_funct_1, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.59       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.20/0.59         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.20/0.59  thf('30', plain,
% 0.20/0.59      (![X28 : $i, X29 : $i]:
% 0.20/0.59         (((k1_relat_1 @ X29) != (k1_tarski @ X28))
% 0.20/0.59          | ((k2_relat_1 @ X29) = (k1_tarski @ (k1_funct_1 @ X29 @ X28)))
% 0.20/0.59          | ~ (v1_funct_1 @ X29)
% 0.20/0.59          | ~ (v1_relat_1 @ X29))),
% 0.20/0.59      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.20/0.59  thf('31', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_C_1))
% 0.20/0.59          | ((k1_relat_1 @ sk_C_1) = (k1_xboole_0))
% 0.20/0.59          | ~ (v1_relat_1 @ X0)
% 0.20/0.59          | ~ (v1_funct_1 @ X0)
% 0.20/0.59          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.20/0.59      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.59  thf('32', plain,
% 0.20/0.59      ((((k2_relat_1 @ sk_C_1) = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))
% 0.20/0.59        | ~ (v1_funct_1 @ sk_C_1)
% 0.20/0.59        | ~ (v1_relat_1 @ sk_C_1)
% 0.20/0.59        | ((k1_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 0.20/0.59      inference('eq_res', [status(thm)], ['31'])).
% 0.20/0.59  thf('33', plain, ((v1_funct_1 @ sk_C_1)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('34', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.59      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.59  thf('35', plain,
% 0.20/0.59      ((((k2_relat_1 @ sk_C_1) = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))
% 0.20/0.59        | ((k1_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 0.20/0.59      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.20/0.59  thf('36', plain,
% 0.20/0.59      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1)
% 0.20/0.59         != (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('37', plain,
% 0.20/0.59      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1)
% 0.20/0.59         = (k2_relat_1 @ sk_C_1))),
% 0.20/0.59      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.59  thf('38', plain,
% 0.20/0.59      (((k2_relat_1 @ sk_C_1) != (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.20/0.59      inference('demod', [status(thm)], ['36', '37'])).
% 0.20/0.59  thf('39', plain, (((k1_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 0.20/0.59      inference('simplify_reflect-', [status(thm)], ['35', '38'])).
% 0.20/0.59  thf(t64_relat_1, axiom,
% 0.20/0.59    (![A:$i]:
% 0.20/0.59     ( ( v1_relat_1 @ A ) =>
% 0.20/0.59       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.59           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.59         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.59  thf('40', plain,
% 0.20/0.59      (![X25 : $i]:
% 0.20/0.59         (((k1_relat_1 @ X25) != (k1_xboole_0))
% 0.20/0.59          | ((X25) = (k1_xboole_0))
% 0.20/0.59          | ~ (v1_relat_1 @ X25))),
% 0.20/0.59      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.20/0.59  thf('41', plain,
% 0.20/0.59      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.59        | ~ (v1_relat_1 @ sk_C_1)
% 0.20/0.59        | ((sk_C_1) = (k1_xboole_0)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.59  thf('42', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.59      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.59  thf('43', plain,
% 0.20/0.59      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C_1) = (k1_xboole_0)))),
% 0.20/0.59      inference('demod', [status(thm)], ['41', '42'])).
% 0.20/0.59  thf('44', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.20/0.59      inference('simplify', [status(thm)], ['43'])).
% 0.20/0.59  thf(t60_relat_1, axiom,
% 0.20/0.59    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.20/0.59     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.59  thf('45', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.59      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.59  thf('46', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.20/0.59      inference('simplify', [status(thm)], ['43'])).
% 0.20/0.59  thf(t4_subset_1, axiom,
% 0.20/0.59    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.59  thf('47', plain,
% 0.20/0.59      (![X16 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X16))),
% 0.20/0.59      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.59  thf(t3_subset, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.59  thf('48', plain,
% 0.20/0.59      (![X17 : $i, X18 : $i]:
% 0.20/0.59         ((r1_tarski @ X17 @ X18) | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 0.20/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.59  thf('49', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.59      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.59  thf('50', plain, (![X0 : $i]: (r1_tarski @ (k1_tarski @ sk_A) @ X0)),
% 0.20/0.59      inference('demod', [status(thm)], ['14', '44', '45', '46', '49'])).
% 0.20/0.59  thf('51', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.59      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.59  thf(d10_xboole_0, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.59  thf('52', plain,
% 0.20/0.59      (![X4 : $i, X6 : $i]:
% 0.20/0.59         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.20/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.59  thf('53', plain,
% 0.20/0.59      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.59  thf('54', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.20/0.59      inference('sup-', [status(thm)], ['50', '53'])).
% 0.20/0.59  thf('55', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.59      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.59  thf('56', plain,
% 0.20/0.59      (![X28 : $i, X29 : $i]:
% 0.20/0.59         (((k1_relat_1 @ X29) != (k1_tarski @ X28))
% 0.20/0.59          | ((k2_relat_1 @ X29) = (k1_tarski @ (k1_funct_1 @ X29 @ X28)))
% 0.20/0.59          | ~ (v1_funct_1 @ X29)
% 0.20/0.59          | ~ (v1_relat_1 @ X29))),
% 0.20/0.59      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.20/0.59  thf('57', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.20/0.59          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.59          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.20/0.59          | ((k2_relat_1 @ k1_xboole_0)
% 0.20/0.59              = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0))))),
% 0.20/0.59      inference('sup-', [status(thm)], ['55', '56'])).
% 0.20/0.59  thf('58', plain,
% 0.20/0.59      (![X16 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X16))),
% 0.20/0.59      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.59  thf('59', plain,
% 0.20/0.59      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.20/0.59         ((v1_relat_1 @ X32)
% 0.20/0.59          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.20/0.59      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.59  thf('60', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.59      inference('sup-', [status(thm)], ['58', '59'])).
% 0.20/0.59  thf('61', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.59      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.59  thf('62', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.20/0.59          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.20/0.59          | ((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0))))),
% 0.20/0.59      inference('demod', [status(thm)], ['57', '60', '61'])).
% 0.20/0.59  thf('63', plain, ((v1_funct_1 @ sk_C_1)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('64', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.20/0.59      inference('simplify', [status(thm)], ['43'])).
% 0.20/0.59  thf('65', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.20/0.59      inference('demod', [status(thm)], ['63', '64'])).
% 0.20/0.59  thf('66', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.20/0.59          | ((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0))))),
% 0.20/0.59      inference('demod', [status(thm)], ['62', '65'])).
% 0.20/0.59  thf('67', plain,
% 0.20/0.59      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.59        | ((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A))))),
% 0.20/0.59      inference('sup-', [status(thm)], ['54', '66'])).
% 0.20/0.59  thf('68', plain,
% 0.20/0.59      (((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A)))),
% 0.20/0.59      inference('simplify', [status(thm)], ['67'])).
% 0.20/0.59  thf('69', plain,
% 0.20/0.59      (((k2_relat_1 @ sk_C_1) != (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.20/0.59      inference('demod', [status(thm)], ['36', '37'])).
% 0.20/0.59  thf('70', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.20/0.59      inference('simplify', [status(thm)], ['43'])).
% 0.20/0.59  thf('71', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.59      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.59  thf('72', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.20/0.59      inference('simplify', [status(thm)], ['43'])).
% 0.20/0.59  thf('73', plain,
% 0.20/0.59      (((k1_xboole_0) != (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A)))),
% 0.20/0.59      inference('demod', [status(thm)], ['69', '70', '71', '72'])).
% 0.20/0.59  thf('74', plain, ($false),
% 0.20/0.59      inference('simplify_reflect-', [status(thm)], ['68', '73'])).
% 0.20/0.59  
% 0.20/0.59  % SZS output end Refutation
% 0.20/0.59  
% 0.40/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
