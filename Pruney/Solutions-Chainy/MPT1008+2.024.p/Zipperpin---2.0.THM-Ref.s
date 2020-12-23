%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CQsrQgmYq7

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:34 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 552 expanded)
%              Number of leaves         :   39 ( 177 expanded)
%              Depth                    :   28
%              Number of atoms          : 1160 (7232 expanded)
%              Number of equality atoms :  129 ( 730 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

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

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('15',plain,(
    ! [X7: $i] :
      ( ( k2_tarski @ X7 @ X7 )
      = ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X8 @ X8 @ X9 )
      = ( k2_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('17',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('19',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( v4_relat_1 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('20',plain,(
    v4_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('21',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v4_relat_1 @ X25 @ X26 )
      | ( r1_tarski @ ( k1_relat_1 @ X25 ) @ X26 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('24',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v1_relat_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('25',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_C_1 ) ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['17','28'])).

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

thf('30',plain,(
    ! [X13: $i,X14: $i,X15: $i,X17: $i] :
      ( ( r1_tarski @ X17 @ ( k1_enumset1 @ X13 @ X14 @ X15 ) )
      | ( X17
       != ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t142_zfmisc_1])).

thf('31',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( r1_tarski @ ( k1_tarski @ X13 ) @ ( k1_enumset1 @ X13 @ X14 @ X15 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X3 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_C_1 ) ) @ ( k1_enumset1 @ sk_A @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['29','33'])).

thf('35',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_enumset1 @ sk_A @ X1 @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_enumset1 @ sk_A @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_enumset1 @ sk_A @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ ( k2_tarski @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','37'])).

thf('39',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X8 @ X8 @ X9 )
      = ( k2_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('40',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X16
        = ( k1_enumset1 @ X13 @ X14 @ X15 ) )
      | ( X16
        = ( k2_tarski @ X13 @ X15 ) )
      | ( X16
        = ( k2_tarski @ X14 @ X15 ) )
      | ( X16
        = ( k2_tarski @ X13 @ X14 ) )
      | ( X16
        = ( k1_tarski @ X15 ) )
      | ( X16
        = ( k1_tarski @ X14 ) )
      | ( X16
        = ( k1_tarski @ X13 ) )
      | ( X16 = k1_xboole_0 )
      | ~ ( r1_tarski @ X16 @ ( k1_enumset1 @ X13 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t142_zfmisc_1])).

thf('41',plain,(
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
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k1_enumset1 @ X8 @ X8 @ X9 )
      = ( k2_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('43',plain,(
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
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
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
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_C_1 )
        = k1_xboole_0 )
      | ( ( k1_relat_1 @ sk_C_1 )
        = ( k1_tarski @ sk_A ) )
      | ( ( k1_relat_1 @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k1_relat_1 @ sk_C_1 )
        = ( k2_tarski @ sk_A @ sk_A ) )
      | ( ( k1_relat_1 @ sk_C_1 )
        = ( k2_tarski @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','44'])).

thf('46',plain,(
    ! [X7: $i] :
      ( ( k2_tarski @ X7 @ X7 )
      = ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_C_1 )
        = k1_xboole_0 )
      | ( ( k1_relat_1 @ sk_C_1 )
        = ( k1_tarski @ sk_A ) )
      | ( ( k1_relat_1 @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k1_relat_1 @ sk_C_1 )
        = ( k1_tarski @ sk_A ) )
      | ( ( k1_relat_1 @ sk_C_1 )
        = ( k2_tarski @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_C_1 )
        = ( k2_tarski @ sk_A @ X0 ) )
      | ( ( k1_relat_1 @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( k1_relat_1 @ sk_C_1 )
        = ( k1_tarski @ sk_A ) )
      | ( ( k1_relat_1 @ sk_C_1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['15','48'])).

thf('50',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('51',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k1_relat_1 @ X29 )
       != ( k1_tarski @ X28 ) )
      | ( ( k2_relat_1 @ X29 )
        = ( k1_tarski @ ( k1_funct_1 @ X29 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_C_1 ) )
      | ( ( k1_relat_1 @ sk_C_1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['52'])).

thf('54',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['23','24'])).

thf('56',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('59',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['56','59'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('61',plain,(
    ! [X27: $i] :
      ( ( ( k1_relat_1 @ X27 )
       != k1_xboole_0 )
      | ( X27 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('62',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['23','24'])).

thf('64',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['64'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('66',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('67',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['64'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('68',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('69',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('70',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 ) ),
    inference(demod,[status(thm)],['14','65','66','67','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('73',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['71','74'])).

thf('76',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('77',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k1_relat_1 @ X29 )
       != ( k1_tarski @ X28 ) )
      | ( ( k2_relat_1 @ X29 )
        = ( k1_tarski @ ( k1_funct_1 @ X29 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('80',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v1_relat_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('81',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['78','81','82'])).

thf('84',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['64'])).

thf('86',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ( k1_xboole_0
        = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['83','86'])).

thf('88',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['75','87'])).

thf('89',plain,
    ( k1_xboole_0
    = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('91',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['64'])).

thf('92',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('93',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['64'])).

thf('94',plain,(
    k1_xboole_0
 != ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','91','92','93'])).

thf('95',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['89','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CQsrQgmYq7
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:55:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.58/0.81  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.58/0.81  % Solved by: fo/fo7.sh
% 0.58/0.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.81  % done 876 iterations in 0.350s
% 0.58/0.81  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.58/0.81  % SZS output start Refutation
% 0.58/0.81  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.58/0.81  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.81  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.58/0.81  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.58/0.81  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.58/0.81  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.58/0.81  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.58/0.81  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.81  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.58/0.81  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.58/0.81  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.81  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.58/0.81  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.58/0.81  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.58/0.81  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.58/0.81  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.58/0.81  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.81  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.58/0.81  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.58/0.81  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.58/0.81  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.81  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.58/0.81  thf(d3_tarski, axiom,
% 0.58/0.81    (![A:$i,B:$i]:
% 0.58/0.81     ( ( r1_tarski @ A @ B ) <=>
% 0.58/0.81       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.58/0.81  thf('0', plain,
% 0.58/0.81      (![X1 : $i, X3 : $i]:
% 0.58/0.81         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.58/0.81      inference('cnf', [status(esa)], [d3_tarski])).
% 0.58/0.81  thf(t62_funct_2, conjecture,
% 0.58/0.81    (![A:$i,B:$i,C:$i]:
% 0.58/0.81     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.58/0.81         ( m1_subset_1 @
% 0.58/0.81           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.58/0.81       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.58/0.81         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.58/0.81           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.58/0.81  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.81    (~( ![A:$i,B:$i,C:$i]:
% 0.58/0.81        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.58/0.81            ( m1_subset_1 @
% 0.58/0.81              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.58/0.81          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.58/0.81            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.58/0.81              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 0.58/0.81    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 0.58/0.81  thf('1', plain,
% 0.58/0.81      ((m1_subset_1 @ sk_C_1 @ 
% 0.58/0.81        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf(t6_funct_2, axiom,
% 0.58/0.81    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.81     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.58/0.81         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.58/0.81       ( ( r2_hidden @ C @ A ) =>
% 0.58/0.81         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.58/0.81           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.58/0.81  thf('2', plain,
% 0.58/0.81      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.58/0.81         (~ (r2_hidden @ X41 @ X42)
% 0.58/0.81          | ((X43) = (k1_xboole_0))
% 0.58/0.81          | ~ (v1_funct_1 @ X44)
% 0.58/0.81          | ~ (v1_funct_2 @ X44 @ X42 @ X43)
% 0.58/0.81          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 0.58/0.81          | (r2_hidden @ (k1_funct_1 @ X44 @ X41) @ 
% 0.58/0.81             (k2_relset_1 @ X42 @ X43 @ X44)))),
% 0.58/0.81      inference('cnf', [status(esa)], [t6_funct_2])).
% 0.58/0.81  thf('3', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ 
% 0.58/0.81           (k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1))
% 0.58/0.81          | ~ (v1_funct_2 @ sk_C_1 @ (k1_tarski @ sk_A) @ sk_B)
% 0.58/0.81          | ~ (v1_funct_1 @ sk_C_1)
% 0.58/0.81          | ((sk_B) = (k1_xboole_0))
% 0.58/0.81          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['1', '2'])).
% 0.58/0.81  thf('4', plain,
% 0.58/0.81      ((m1_subset_1 @ sk_C_1 @ 
% 0.58/0.81        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf(redefinition_k2_relset_1, axiom,
% 0.58/0.81    (![A:$i,B:$i,C:$i]:
% 0.58/0.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.81       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.58/0.81  thf('5', plain,
% 0.58/0.81      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.58/0.81         (((k2_relset_1 @ X39 @ X40 @ X38) = (k2_relat_1 @ X38))
% 0.58/0.81          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40))))),
% 0.58/0.81      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.58/0.81  thf('6', plain,
% 0.58/0.81      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1)
% 0.58/0.81         = (k2_relat_1 @ sk_C_1))),
% 0.58/0.81      inference('sup-', [status(thm)], ['4', '5'])).
% 0.58/0.81  thf('7', plain, ((v1_funct_2 @ sk_C_1 @ (k1_tarski @ sk_A) @ sk_B)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('8', plain, ((v1_funct_1 @ sk_C_1)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('9', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ (k2_relat_1 @ sk_C_1))
% 0.58/0.81          | ((sk_B) = (k1_xboole_0))
% 0.58/0.81          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.58/0.81      inference('demod', [status(thm)], ['3', '6', '7', '8'])).
% 0.58/0.81  thf('10', plain, (((sk_B) != (k1_xboole_0))),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('11', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ (k2_relat_1 @ sk_C_1))
% 0.58/0.81          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.58/0.81      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.58/0.81  thf('12', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         ((r1_tarski @ (k1_tarski @ sk_A) @ X0)
% 0.58/0.81          | (r2_hidden @ 
% 0.58/0.81             (k1_funct_1 @ sk_C_1 @ (sk_C @ X0 @ (k1_tarski @ sk_A))) @ 
% 0.58/0.81             (k2_relat_1 @ sk_C_1)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['0', '11'])).
% 0.58/0.81  thf(t7_ordinal1, axiom,
% 0.58/0.81    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.58/0.81  thf('13', plain,
% 0.58/0.81      (![X30 : $i, X31 : $i]:
% 0.58/0.81         (~ (r2_hidden @ X30 @ X31) | ~ (r1_tarski @ X31 @ X30))),
% 0.58/0.81      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.58/0.81  thf('14', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         ((r1_tarski @ (k1_tarski @ sk_A) @ X0)
% 0.58/0.81          | ~ (r1_tarski @ (k2_relat_1 @ sk_C_1) @ 
% 0.58/0.81               (k1_funct_1 @ sk_C_1 @ (sk_C @ X0 @ (k1_tarski @ sk_A)))))),
% 0.58/0.81      inference('sup-', [status(thm)], ['12', '13'])).
% 0.58/0.81  thf(t69_enumset1, axiom,
% 0.58/0.81    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.58/0.81  thf('15', plain, (![X7 : $i]: ((k2_tarski @ X7 @ X7) = (k1_tarski @ X7))),
% 0.58/0.81      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.58/0.81  thf(t70_enumset1, axiom,
% 0.58/0.81    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.58/0.81  thf('16', plain,
% 0.58/0.81      (![X8 : $i, X9 : $i]:
% 0.58/0.81         ((k1_enumset1 @ X8 @ X8 @ X9) = (k2_tarski @ X8 @ X9))),
% 0.58/0.81      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.58/0.81  thf('17', plain,
% 0.58/0.81      (![X1 : $i, X3 : $i]:
% 0.58/0.81         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.58/0.81      inference('cnf', [status(esa)], [d3_tarski])).
% 0.58/0.81  thf('18', plain,
% 0.58/0.81      ((m1_subset_1 @ sk_C_1 @ 
% 0.58/0.81        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf(cc2_relset_1, axiom,
% 0.58/0.81    (![A:$i,B:$i,C:$i]:
% 0.58/0.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.81       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.58/0.81  thf('19', plain,
% 0.58/0.81      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.58/0.81         ((v4_relat_1 @ X35 @ X36)
% 0.58/0.81          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 0.58/0.81      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.58/0.81  thf('20', plain, ((v4_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A))),
% 0.58/0.81      inference('sup-', [status(thm)], ['18', '19'])).
% 0.58/0.81  thf(d18_relat_1, axiom,
% 0.58/0.81    (![A:$i,B:$i]:
% 0.58/0.81     ( ( v1_relat_1 @ B ) =>
% 0.58/0.81       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.58/0.81  thf('21', plain,
% 0.58/0.81      (![X25 : $i, X26 : $i]:
% 0.58/0.81         (~ (v4_relat_1 @ X25 @ X26)
% 0.58/0.81          | (r1_tarski @ (k1_relat_1 @ X25) @ X26)
% 0.58/0.81          | ~ (v1_relat_1 @ X25))),
% 0.58/0.81      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.58/0.81  thf('22', plain,
% 0.58/0.81      ((~ (v1_relat_1 @ sk_C_1)
% 0.58/0.81        | (r1_tarski @ (k1_relat_1 @ sk_C_1) @ (k1_tarski @ sk_A)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['20', '21'])).
% 0.58/0.81  thf('23', plain,
% 0.58/0.81      ((m1_subset_1 @ sk_C_1 @ 
% 0.58/0.81        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf(cc1_relset_1, axiom,
% 0.58/0.81    (![A:$i,B:$i,C:$i]:
% 0.58/0.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.81       ( v1_relat_1 @ C ) ))).
% 0.58/0.81  thf('24', plain,
% 0.58/0.81      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.58/0.81         ((v1_relat_1 @ X32)
% 0.58/0.81          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.58/0.81      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.58/0.81  thf('25', plain, ((v1_relat_1 @ sk_C_1)),
% 0.58/0.81      inference('sup-', [status(thm)], ['23', '24'])).
% 0.58/0.81  thf('26', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ (k1_tarski @ sk_A))),
% 0.58/0.81      inference('demod', [status(thm)], ['22', '25'])).
% 0.58/0.81  thf('27', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.81         (~ (r2_hidden @ X0 @ X1)
% 0.58/0.81          | (r2_hidden @ X0 @ X2)
% 0.58/0.81          | ~ (r1_tarski @ X1 @ X2))),
% 0.58/0.81      inference('cnf', [status(esa)], [d3_tarski])).
% 0.58/0.81  thf('28', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         ((r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.58/0.81          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['26', '27'])).
% 0.58/0.81  thf('29', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ X0)
% 0.58/0.81          | (r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ sk_C_1)) @ 
% 0.58/0.81             (k1_tarski @ sk_A)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['17', '28'])).
% 0.58/0.81  thf(t142_zfmisc_1, axiom,
% 0.58/0.81    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.81     ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.58/0.81       ( ~( ( ( D ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_tarski @ A ) ) & 
% 0.58/0.81            ( ( D ) != ( k1_tarski @ B ) ) & ( ( D ) != ( k1_tarski @ C ) ) & 
% 0.58/0.81            ( ( D ) != ( k2_tarski @ A @ B ) ) & 
% 0.58/0.81            ( ( D ) != ( k2_tarski @ B @ C ) ) & 
% 0.58/0.81            ( ( D ) != ( k2_tarski @ A @ C ) ) & 
% 0.58/0.81            ( ( D ) != ( k1_enumset1 @ A @ B @ C ) ) ) ) ))).
% 0.58/0.81  thf('30', plain,
% 0.58/0.81      (![X13 : $i, X14 : $i, X15 : $i, X17 : $i]:
% 0.58/0.81         ((r1_tarski @ X17 @ (k1_enumset1 @ X13 @ X14 @ X15))
% 0.58/0.81          | ((X17) != (k1_tarski @ X13)))),
% 0.58/0.81      inference('cnf', [status(esa)], [t142_zfmisc_1])).
% 0.58/0.81  thf('31', plain,
% 0.58/0.81      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.58/0.81         (r1_tarski @ (k1_tarski @ X13) @ (k1_enumset1 @ X13 @ X14 @ X15))),
% 0.58/0.81      inference('simplify', [status(thm)], ['30'])).
% 0.58/0.81  thf('32', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.81         (~ (r2_hidden @ X0 @ X1)
% 0.58/0.81          | (r2_hidden @ X0 @ X2)
% 0.58/0.81          | ~ (r1_tarski @ X1 @ X2))),
% 0.58/0.81      inference('cnf', [status(esa)], [d3_tarski])).
% 0.58/0.81  thf('33', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.58/0.81         ((r2_hidden @ X3 @ (k1_enumset1 @ X2 @ X1 @ X0))
% 0.58/0.81          | ~ (r2_hidden @ X3 @ (k1_tarski @ X2)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['31', '32'])).
% 0.58/0.81  thf('34', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.81         ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ X0)
% 0.58/0.81          | (r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ sk_C_1)) @ 
% 0.58/0.81             (k1_enumset1 @ sk_A @ X2 @ X1)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['29', '33'])).
% 0.58/0.81  thf('35', plain,
% 0.58/0.81      (![X1 : $i, X3 : $i]:
% 0.58/0.81         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.58/0.81      inference('cnf', [status(esa)], [d3_tarski])).
% 0.58/0.81  thf('36', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i]:
% 0.58/0.81         ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ (k1_enumset1 @ sk_A @ X1 @ X0))
% 0.58/0.81          | (r1_tarski @ (k1_relat_1 @ sk_C_1) @ (k1_enumset1 @ sk_A @ X1 @ X0)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['34', '35'])).
% 0.58/0.81  thf('37', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i]:
% 0.58/0.81         (r1_tarski @ (k1_relat_1 @ sk_C_1) @ (k1_enumset1 @ sk_A @ X1 @ X0))),
% 0.58/0.81      inference('simplify', [status(thm)], ['36'])).
% 0.58/0.81  thf('38', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (r1_tarski @ (k1_relat_1 @ sk_C_1) @ (k2_tarski @ sk_A @ X0))),
% 0.58/0.81      inference('sup+', [status(thm)], ['16', '37'])).
% 0.58/0.81  thf('39', plain,
% 0.58/0.81      (![X8 : $i, X9 : $i]:
% 0.58/0.81         ((k1_enumset1 @ X8 @ X8 @ X9) = (k2_tarski @ X8 @ X9))),
% 0.58/0.81      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.58/0.81  thf('40', plain,
% 0.58/0.81      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.58/0.81         (((X16) = (k1_enumset1 @ X13 @ X14 @ X15))
% 0.58/0.81          | ((X16) = (k2_tarski @ X13 @ X15))
% 0.58/0.81          | ((X16) = (k2_tarski @ X14 @ X15))
% 0.58/0.81          | ((X16) = (k2_tarski @ X13 @ X14))
% 0.58/0.81          | ((X16) = (k1_tarski @ X15))
% 0.58/0.81          | ((X16) = (k1_tarski @ X14))
% 0.58/0.81          | ((X16) = (k1_tarski @ X13))
% 0.58/0.81          | ((X16) = (k1_xboole_0))
% 0.58/0.81          | ~ (r1_tarski @ X16 @ (k1_enumset1 @ X13 @ X14 @ X15)))),
% 0.58/0.81      inference('cnf', [status(esa)], [t142_zfmisc_1])).
% 0.58/0.81  thf('41', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.81         (~ (r1_tarski @ X2 @ (k2_tarski @ X1 @ X0))
% 0.58/0.81          | ((X2) = (k1_xboole_0))
% 0.58/0.81          | ((X2) = (k1_tarski @ X1))
% 0.58/0.81          | ((X2) = (k1_tarski @ X1))
% 0.58/0.81          | ((X2) = (k1_tarski @ X0))
% 0.58/0.81          | ((X2) = (k2_tarski @ X1 @ X1))
% 0.58/0.81          | ((X2) = (k2_tarski @ X1 @ X0))
% 0.58/0.81          | ((X2) = (k2_tarski @ X1 @ X0))
% 0.58/0.81          | ((X2) = (k1_enumset1 @ X1 @ X1 @ X0)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['39', '40'])).
% 0.58/0.81  thf('42', plain,
% 0.58/0.81      (![X8 : $i, X9 : $i]:
% 0.58/0.81         ((k1_enumset1 @ X8 @ X8 @ X9) = (k2_tarski @ X8 @ X9))),
% 0.58/0.81      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.58/0.81  thf('43', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.81         (~ (r1_tarski @ X2 @ (k2_tarski @ X1 @ X0))
% 0.58/0.81          | ((X2) = (k1_xboole_0))
% 0.58/0.81          | ((X2) = (k1_tarski @ X1))
% 0.58/0.81          | ((X2) = (k1_tarski @ X1))
% 0.58/0.81          | ((X2) = (k1_tarski @ X0))
% 0.58/0.81          | ((X2) = (k2_tarski @ X1 @ X1))
% 0.58/0.81          | ((X2) = (k2_tarski @ X1 @ X0))
% 0.58/0.81          | ((X2) = (k2_tarski @ X1 @ X0))
% 0.58/0.81          | ((X2) = (k2_tarski @ X1 @ X0)))),
% 0.58/0.81      inference('demod', [status(thm)], ['41', '42'])).
% 0.58/0.81  thf('44', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.81         (((X2) = (k2_tarski @ X1 @ X0))
% 0.58/0.81          | ((X2) = (k2_tarski @ X1 @ X1))
% 0.58/0.81          | ((X2) = (k1_tarski @ X0))
% 0.58/0.81          | ((X2) = (k1_tarski @ X1))
% 0.58/0.81          | ((X2) = (k1_xboole_0))
% 0.58/0.81          | ~ (r1_tarski @ X2 @ (k2_tarski @ X1 @ X0)))),
% 0.58/0.81      inference('simplify', [status(thm)], ['43'])).
% 0.58/0.81  thf('45', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (((k1_relat_1 @ sk_C_1) = (k1_xboole_0))
% 0.58/0.81          | ((k1_relat_1 @ sk_C_1) = (k1_tarski @ sk_A))
% 0.58/0.81          | ((k1_relat_1 @ sk_C_1) = (k1_tarski @ X0))
% 0.58/0.81          | ((k1_relat_1 @ sk_C_1) = (k2_tarski @ sk_A @ sk_A))
% 0.58/0.81          | ((k1_relat_1 @ sk_C_1) = (k2_tarski @ sk_A @ X0)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['38', '44'])).
% 0.58/0.81  thf('46', plain, (![X7 : $i]: ((k2_tarski @ X7 @ X7) = (k1_tarski @ X7))),
% 0.58/0.81      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.58/0.81  thf('47', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (((k1_relat_1 @ sk_C_1) = (k1_xboole_0))
% 0.58/0.81          | ((k1_relat_1 @ sk_C_1) = (k1_tarski @ sk_A))
% 0.58/0.81          | ((k1_relat_1 @ sk_C_1) = (k1_tarski @ X0))
% 0.58/0.81          | ((k1_relat_1 @ sk_C_1) = (k1_tarski @ sk_A))
% 0.58/0.81          | ((k1_relat_1 @ sk_C_1) = (k2_tarski @ sk_A @ X0)))),
% 0.58/0.81      inference('demod', [status(thm)], ['45', '46'])).
% 0.58/0.81  thf('48', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (((k1_relat_1 @ sk_C_1) = (k2_tarski @ sk_A @ X0))
% 0.58/0.81          | ((k1_relat_1 @ sk_C_1) = (k1_tarski @ X0))
% 0.58/0.81          | ((k1_relat_1 @ sk_C_1) = (k1_tarski @ sk_A))
% 0.58/0.81          | ((k1_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 0.58/0.81      inference('simplify', [status(thm)], ['47'])).
% 0.58/0.81  thf('49', plain,
% 0.58/0.81      ((((k1_relat_1 @ sk_C_1) = (k1_tarski @ sk_A))
% 0.58/0.81        | ((k1_relat_1 @ sk_C_1) = (k1_xboole_0))
% 0.58/0.81        | ((k1_relat_1 @ sk_C_1) = (k1_tarski @ sk_A))
% 0.58/0.81        | ((k1_relat_1 @ sk_C_1) = (k1_tarski @ sk_A)))),
% 0.58/0.81      inference('sup+', [status(thm)], ['15', '48'])).
% 0.58/0.81  thf('50', plain,
% 0.58/0.81      ((((k1_relat_1 @ sk_C_1) = (k1_xboole_0))
% 0.58/0.81        | ((k1_relat_1 @ sk_C_1) = (k1_tarski @ sk_A)))),
% 0.58/0.81      inference('simplify', [status(thm)], ['49'])).
% 0.58/0.81  thf(t14_funct_1, axiom,
% 0.58/0.81    (![A:$i,B:$i]:
% 0.58/0.81     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.58/0.81       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.58/0.81         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.58/0.81  thf('51', plain,
% 0.58/0.81      (![X28 : $i, X29 : $i]:
% 0.58/0.81         (((k1_relat_1 @ X29) != (k1_tarski @ X28))
% 0.58/0.81          | ((k2_relat_1 @ X29) = (k1_tarski @ (k1_funct_1 @ X29 @ X28)))
% 0.58/0.81          | ~ (v1_funct_1 @ X29)
% 0.58/0.81          | ~ (v1_relat_1 @ X29))),
% 0.58/0.81      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.58/0.81  thf('52', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_C_1))
% 0.58/0.81          | ((k1_relat_1 @ sk_C_1) = (k1_xboole_0))
% 0.58/0.81          | ~ (v1_relat_1 @ X0)
% 0.58/0.81          | ~ (v1_funct_1 @ X0)
% 0.58/0.81          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.58/0.81      inference('sup-', [status(thm)], ['50', '51'])).
% 0.58/0.81  thf('53', plain,
% 0.58/0.81      ((((k2_relat_1 @ sk_C_1) = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))
% 0.58/0.81        | ~ (v1_funct_1 @ sk_C_1)
% 0.58/0.81        | ~ (v1_relat_1 @ sk_C_1)
% 0.58/0.81        | ((k1_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 0.58/0.81      inference('eq_res', [status(thm)], ['52'])).
% 0.58/0.81  thf('54', plain, ((v1_funct_1 @ sk_C_1)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('55', plain, ((v1_relat_1 @ sk_C_1)),
% 0.58/0.81      inference('sup-', [status(thm)], ['23', '24'])).
% 0.58/0.81  thf('56', plain,
% 0.58/0.81      ((((k2_relat_1 @ sk_C_1) = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))
% 0.58/0.81        | ((k1_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 0.58/0.81      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.58/0.81  thf('57', plain,
% 0.58/0.81      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1)
% 0.58/0.81         != (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('58', plain,
% 0.58/0.81      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1)
% 0.58/0.81         = (k2_relat_1 @ sk_C_1))),
% 0.58/0.81      inference('sup-', [status(thm)], ['4', '5'])).
% 0.58/0.81  thf('59', plain,
% 0.58/0.81      (((k2_relat_1 @ sk_C_1) != (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.58/0.81      inference('demod', [status(thm)], ['57', '58'])).
% 0.58/0.81  thf('60', plain, (((k1_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 0.58/0.81      inference('simplify_reflect-', [status(thm)], ['56', '59'])).
% 0.58/0.81  thf(t64_relat_1, axiom,
% 0.58/0.81    (![A:$i]:
% 0.58/0.81     ( ( v1_relat_1 @ A ) =>
% 0.58/0.81       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.58/0.81           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.58/0.81         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.58/0.81  thf('61', plain,
% 0.58/0.81      (![X27 : $i]:
% 0.58/0.81         (((k1_relat_1 @ X27) != (k1_xboole_0))
% 0.58/0.81          | ((X27) = (k1_xboole_0))
% 0.58/0.81          | ~ (v1_relat_1 @ X27))),
% 0.58/0.81      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.58/0.81  thf('62', plain,
% 0.58/0.81      ((((k1_xboole_0) != (k1_xboole_0))
% 0.58/0.81        | ~ (v1_relat_1 @ sk_C_1)
% 0.58/0.81        | ((sk_C_1) = (k1_xboole_0)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['60', '61'])).
% 0.58/0.81  thf('63', plain, ((v1_relat_1 @ sk_C_1)),
% 0.58/0.81      inference('sup-', [status(thm)], ['23', '24'])).
% 0.58/0.81  thf('64', plain,
% 0.58/0.81      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C_1) = (k1_xboole_0)))),
% 0.58/0.81      inference('demod', [status(thm)], ['62', '63'])).
% 0.58/0.81  thf('65', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.58/0.81      inference('simplify', [status(thm)], ['64'])).
% 0.58/0.81  thf(t60_relat_1, axiom,
% 0.58/0.81    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.58/0.81     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.58/0.81  thf('66', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.81      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.58/0.81  thf('67', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.58/0.81      inference('simplify', [status(thm)], ['64'])).
% 0.58/0.81  thf(t4_subset_1, axiom,
% 0.58/0.81    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.58/0.81  thf('68', plain,
% 0.58/0.81      (![X18 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X18))),
% 0.58/0.81      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.58/0.81  thf(t3_subset, axiom,
% 0.58/0.81    (![A:$i,B:$i]:
% 0.58/0.81     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.58/0.81  thf('69', plain,
% 0.58/0.81      (![X19 : $i, X20 : $i]:
% 0.58/0.81         ((r1_tarski @ X19 @ X20) | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 0.58/0.81      inference('cnf', [status(esa)], [t3_subset])).
% 0.58/0.81  thf('70', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.58/0.81      inference('sup-', [status(thm)], ['68', '69'])).
% 0.58/0.81  thf('71', plain, (![X0 : $i]: (r1_tarski @ (k1_tarski @ sk_A) @ X0)),
% 0.58/0.81      inference('demod', [status(thm)], ['14', '65', '66', '67', '70'])).
% 0.58/0.81  thf('72', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.58/0.81      inference('sup-', [status(thm)], ['68', '69'])).
% 0.58/0.81  thf(d10_xboole_0, axiom,
% 0.58/0.81    (![A:$i,B:$i]:
% 0.58/0.81     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.58/0.81  thf('73', plain,
% 0.58/0.81      (![X4 : $i, X6 : $i]:
% 0.58/0.81         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.58/0.81      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.58/0.81  thf('74', plain,
% 0.58/0.81      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['72', '73'])).
% 0.58/0.81  thf('75', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.58/0.81      inference('sup-', [status(thm)], ['71', '74'])).
% 0.58/0.81  thf('76', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.81      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.58/0.81  thf('77', plain,
% 0.58/0.81      (![X28 : $i, X29 : $i]:
% 0.58/0.81         (((k1_relat_1 @ X29) != (k1_tarski @ X28))
% 0.58/0.81          | ((k2_relat_1 @ X29) = (k1_tarski @ (k1_funct_1 @ X29 @ X28)))
% 0.58/0.81          | ~ (v1_funct_1 @ X29)
% 0.58/0.81          | ~ (v1_relat_1 @ X29))),
% 0.58/0.81      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.58/0.81  thf('78', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.58/0.81          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.58/0.81          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.58/0.81          | ((k2_relat_1 @ k1_xboole_0)
% 0.58/0.81              = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0))))),
% 0.58/0.81      inference('sup-', [status(thm)], ['76', '77'])).
% 0.58/0.81  thf('79', plain,
% 0.58/0.81      (![X18 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X18))),
% 0.58/0.81      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.58/0.81  thf('80', plain,
% 0.58/0.81      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.58/0.81         ((v1_relat_1 @ X32)
% 0.58/0.81          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.58/0.81      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.58/0.81  thf('81', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.58/0.81      inference('sup-', [status(thm)], ['79', '80'])).
% 0.58/0.81  thf('82', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.81      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.58/0.81  thf('83', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.58/0.81          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.58/0.81          | ((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0))))),
% 0.58/0.81      inference('demod', [status(thm)], ['78', '81', '82'])).
% 0.58/0.81  thf('84', plain, ((v1_funct_1 @ sk_C_1)),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf('85', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.58/0.81      inference('simplify', [status(thm)], ['64'])).
% 0.58/0.81  thf('86', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.58/0.81      inference('demod', [status(thm)], ['84', '85'])).
% 0.58/0.81  thf('87', plain,
% 0.58/0.81      (![X0 : $i]:
% 0.58/0.81         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.58/0.81          | ((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0))))),
% 0.58/0.81      inference('demod', [status(thm)], ['83', '86'])).
% 0.58/0.81  thf('88', plain,
% 0.58/0.81      ((((k1_xboole_0) != (k1_xboole_0))
% 0.58/0.81        | ((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A))))),
% 0.58/0.81      inference('sup-', [status(thm)], ['75', '87'])).
% 0.58/0.81  thf('89', plain,
% 0.58/0.81      (((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A)))),
% 0.58/0.81      inference('simplify', [status(thm)], ['88'])).
% 0.58/0.81  thf('90', plain,
% 0.58/0.81      (((k2_relat_1 @ sk_C_1) != (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.58/0.81      inference('demod', [status(thm)], ['57', '58'])).
% 0.58/0.81  thf('91', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.58/0.81      inference('simplify', [status(thm)], ['64'])).
% 0.58/0.81  thf('92', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.81      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.58/0.81  thf('93', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.58/0.81      inference('simplify', [status(thm)], ['64'])).
% 0.58/0.81  thf('94', plain,
% 0.58/0.81      (((k1_xboole_0) != (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A)))),
% 0.58/0.81      inference('demod', [status(thm)], ['90', '91', '92', '93'])).
% 0.58/0.81  thf('95', plain, ($false),
% 0.58/0.81      inference('simplify_reflect-', [status(thm)], ['89', '94'])).
% 0.58/0.81  
% 0.58/0.81  % SZS output end Refutation
% 0.58/0.81  
% 0.58/0.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
