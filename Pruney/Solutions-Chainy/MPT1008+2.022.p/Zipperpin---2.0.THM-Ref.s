%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FROyNUpgsi

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 322 expanded)
%              Number of leaves         :   37 ( 111 expanded)
%              Depth                    :   18
%              Number of atoms          :  757 (3859 expanded)
%              Number of equality atoms :   77 ( 330 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
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
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( r2_hidden @ X39 @ X40 )
      | ( X41 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_2 @ X42 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X42 @ X39 ) @ ( k2_relset_1 @ X40 @ X41 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t6_funct_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C_1 ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
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
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_2 @ sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ ( k2_relat_1 @ sk_C_1 ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['3','6','7','8'])).

thf('10',plain,(
    sk_B_1 != k1_xboole_0 ),
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
    ! [X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X26 @ X27 )
      | ~ ( r1_tarski @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ ( k1_funct_1 @ sk_C_1 @ ( sk_C @ X0 @ ( k1_tarski @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('16',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v4_relat_1 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('17',plain,(
    v4_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('18',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v4_relat_1 @ X21 @ X22 )
      | ( r1_tarski @ ( k1_relat_1 @ X21 ) @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
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

thf('23',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['19','22'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('24',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X15
        = ( k1_tarski @ X14 ) )
      | ( X15 = k1_xboole_0 )
      | ~ ( r1_tarski @ X15 @ ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('25',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('26',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k1_relat_1 @ X25 )
       != ( k1_tarski @ X24 ) )
      | ( ( k2_relat_1 @ X25 )
        = ( k1_tarski @ ( k1_funct_1 @ X25 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_C_1 ) )
      | ( ( k1_relat_1 @ sk_C_1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['27'])).

thf('29',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('31',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C_1 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('34',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['31','34'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('36',plain,(
    ! [X23: $i] :
      ( ( ( k1_relat_1 @ X23 )
       != k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('37',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('39',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['39'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('41',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('42',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['39'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('43',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 ) ),
    inference(demod,[status(thm)],['14','40','41','42','43'])).

thf('45',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('46',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('50',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k1_relat_1 @ X25 )
       != ( k1_tarski @ X24 ) )
      | ( ( k2_relat_1 @ X25 )
        = ( k1_tarski @ ( k1_funct_1 @ X25 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('52',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('53',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v1_relat_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('54',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['52','53'])).

thf(s3_funct_1__e15_31__wellord2,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ B @ C )
            = ( k1_tarski @ C ) ) )
      & ( ( k1_relat_1 @ B )
        = A )
      & ( v1_funct_1 @ B )
      & ( v1_relat_1 @ B ) ) )).

thf('55',plain,(
    ! [X37: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X37 ) )
      = X37 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e15_31__wellord2])).

thf('56',plain,(
    ! [X23: $i] :
      ( ( ( k1_relat_1 @ X23 )
       != k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) )
      | ( ( sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X37: $i] :
      ( v1_relat_1 @ ( sk_B @ X37 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e15_31__wellord2])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X37: $i] :
      ( v1_funct_1 @ ( sk_B @ X37 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e15_31__wellord2])).

thf('62',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ( k1_xboole_0
        = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['51','54','62','63'])).

thf('65',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['48','64'])).

thf('66',plain,
    ( k1_xboole_0
    = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('68',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['39'])).

thf('69',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('70',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['39'])).

thf('71',plain,(
    k1_xboole_0
 != ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['67','68','69','70'])).

thf('72',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['66','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FROyNUpgsi
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:27:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 160 iterations in 0.088s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.55  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.55  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.55  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.55  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.55  thf(d3_tarski, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.55  thf('0', plain,
% 0.21/0.55      (![X1 : $i, X3 : $i]:
% 0.21/0.55         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.55  thf(t62_funct_2, conjecture,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.21/0.55         ( m1_subset_1 @
% 0.21/0.55           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.21/0.55       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.21/0.55         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.21/0.55           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.21/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.55        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.21/0.55            ( m1_subset_1 @
% 0.21/0.55              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.21/0.55          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.21/0.55            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.21/0.55              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 0.21/0.55  thf('1', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_C_1 @ 
% 0.21/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(t6_funct_2, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.55     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.55         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.55       ( ( r2_hidden @ C @ A ) =>
% 0.21/0.55         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.55           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.21/0.55  thf('2', plain,
% 0.21/0.55      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X39 @ X40)
% 0.21/0.55          | ((X41) = (k1_xboole_0))
% 0.21/0.55          | ~ (v1_funct_1 @ X42)
% 0.21/0.55          | ~ (v1_funct_2 @ X42 @ X40 @ X41)
% 0.21/0.55          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.21/0.55          | (r2_hidden @ (k1_funct_1 @ X42 @ X39) @ 
% 0.21/0.55             (k2_relset_1 @ X40 @ X41 @ X42)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t6_funct_2])).
% 0.21/0.55  thf('3', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ 
% 0.21/0.55           (k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C_1))
% 0.21/0.55          | ~ (v1_funct_2 @ sk_C_1 @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.21/0.55          | ~ (v1_funct_1 @ sk_C_1)
% 0.21/0.55          | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.55          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.55  thf('4', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_C_1 @ 
% 0.21/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.55       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.55  thf('5', plain,
% 0.21/0.55      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.21/0.55         (((k2_relset_1 @ X35 @ X36 @ X34) = (k2_relat_1 @ X34))
% 0.21/0.55          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.21/0.55      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.55  thf('6', plain,
% 0.21/0.55      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C_1)
% 0.21/0.55         = (k2_relat_1 @ sk_C_1))),
% 0.21/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.55  thf('7', plain, ((v1_funct_2 @ sk_C_1 @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('8', plain, ((v1_funct_1 @ sk_C_1)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('9', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ (k2_relat_1 @ sk_C_1))
% 0.21/0.55          | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.55          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.21/0.55      inference('demod', [status(thm)], ['3', '6', '7', '8'])).
% 0.21/0.55  thf('10', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('11', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ (k2_relat_1 @ sk_C_1))
% 0.21/0.55          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.21/0.55      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.21/0.55  thf('12', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((r1_tarski @ (k1_tarski @ sk_A) @ X0)
% 0.21/0.55          | (r2_hidden @ 
% 0.21/0.55             (k1_funct_1 @ sk_C_1 @ (sk_C @ X0 @ (k1_tarski @ sk_A))) @ 
% 0.21/0.55             (k2_relat_1 @ sk_C_1)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['0', '11'])).
% 0.21/0.55  thf(t7_ordinal1, axiom,
% 0.21/0.55    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.55  thf('13', plain,
% 0.21/0.55      (![X26 : $i, X27 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X26 @ X27) | ~ (r1_tarski @ X27 @ X26))),
% 0.21/0.55      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.21/0.55  thf('14', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((r1_tarski @ (k1_tarski @ sk_A) @ X0)
% 0.21/0.55          | ~ (r1_tarski @ (k2_relat_1 @ sk_C_1) @ 
% 0.21/0.55               (k1_funct_1 @ sk_C_1 @ (sk_C @ X0 @ (k1_tarski @ sk_A)))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.55  thf('15', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_C_1 @ 
% 0.21/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(cc2_relset_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.55       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.55  thf('16', plain,
% 0.21/0.55      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.21/0.55         ((v4_relat_1 @ X31 @ X32)
% 0.21/0.55          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.21/0.55      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.55  thf('17', plain, ((v4_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.55  thf(d18_relat_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ B ) =>
% 0.21/0.55       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.55  thf('18', plain,
% 0.21/0.55      (![X21 : $i, X22 : $i]:
% 0.21/0.55         (~ (v4_relat_1 @ X21 @ X22)
% 0.21/0.55          | (r1_tarski @ (k1_relat_1 @ X21) @ X22)
% 0.21/0.55          | ~ (v1_relat_1 @ X21))),
% 0.21/0.55      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.21/0.55  thf('19', plain,
% 0.21/0.55      ((~ (v1_relat_1 @ sk_C_1)
% 0.21/0.55        | (r1_tarski @ (k1_relat_1 @ sk_C_1) @ (k1_tarski @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.55  thf('20', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_C_1 @ 
% 0.21/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(cc1_relset_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.55       ( v1_relat_1 @ C ) ))).
% 0.21/0.55  thf('21', plain,
% 0.21/0.55      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.21/0.55         ((v1_relat_1 @ X28)
% 0.21/0.55          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.21/0.55      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.55  thf('22', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.55      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.55  thf('23', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ (k1_tarski @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['19', '22'])).
% 0.21/0.55  thf(l3_zfmisc_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.21/0.55       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.21/0.55  thf('24', plain,
% 0.21/0.55      (![X14 : $i, X15 : $i]:
% 0.21/0.55         (((X15) = (k1_tarski @ X14))
% 0.21/0.55          | ((X15) = (k1_xboole_0))
% 0.21/0.55          | ~ (r1_tarski @ X15 @ (k1_tarski @ X14)))),
% 0.21/0.55      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.21/0.55  thf('25', plain,
% 0.21/0.55      ((((k1_relat_1 @ sk_C_1) = (k1_xboole_0))
% 0.21/0.55        | ((k1_relat_1 @ sk_C_1) = (k1_tarski @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.55  thf(t14_funct_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.55       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.21/0.55         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.21/0.55  thf('26', plain,
% 0.21/0.55      (![X24 : $i, X25 : $i]:
% 0.21/0.55         (((k1_relat_1 @ X25) != (k1_tarski @ X24))
% 0.21/0.55          | ((k2_relat_1 @ X25) = (k1_tarski @ (k1_funct_1 @ X25 @ X24)))
% 0.21/0.55          | ~ (v1_funct_1 @ X25)
% 0.21/0.55          | ~ (v1_relat_1 @ X25))),
% 0.21/0.55      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.21/0.55  thf('27', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_C_1))
% 0.21/0.55          | ((k1_relat_1 @ sk_C_1) = (k1_xboole_0))
% 0.21/0.55          | ~ (v1_relat_1 @ X0)
% 0.21/0.55          | ~ (v1_funct_1 @ X0)
% 0.21/0.55          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.55  thf('28', plain,
% 0.21/0.55      ((((k2_relat_1 @ sk_C_1) = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))
% 0.21/0.55        | ~ (v1_funct_1 @ sk_C_1)
% 0.21/0.55        | ~ (v1_relat_1 @ sk_C_1)
% 0.21/0.55        | ((k1_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 0.21/0.55      inference('eq_res', [status(thm)], ['27'])).
% 0.21/0.55  thf('29', plain, ((v1_funct_1 @ sk_C_1)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('30', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.55      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.55  thf('31', plain,
% 0.21/0.55      ((((k2_relat_1 @ sk_C_1) = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))
% 0.21/0.55        | ((k1_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 0.21/0.55      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.21/0.55  thf('32', plain,
% 0.21/0.55      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C_1)
% 0.21/0.55         != (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('33', plain,
% 0.21/0.55      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C_1)
% 0.21/0.55         = (k2_relat_1 @ sk_C_1))),
% 0.21/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.55  thf('34', plain,
% 0.21/0.55      (((k2_relat_1 @ sk_C_1) != (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.21/0.55      inference('demod', [status(thm)], ['32', '33'])).
% 0.21/0.55  thf('35', plain, (((k1_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 0.21/0.55      inference('simplify_reflect-', [status(thm)], ['31', '34'])).
% 0.21/0.55  thf(t64_relat_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( v1_relat_1 @ A ) =>
% 0.21/0.55       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.55           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.55         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.55  thf('36', plain,
% 0.21/0.55      (![X23 : $i]:
% 0.21/0.55         (((k1_relat_1 @ X23) != (k1_xboole_0))
% 0.21/0.55          | ((X23) = (k1_xboole_0))
% 0.21/0.55          | ~ (v1_relat_1 @ X23))),
% 0.21/0.55      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.21/0.55  thf('37', plain,
% 0.21/0.55      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.55        | ~ (v1_relat_1 @ sk_C_1)
% 0.21/0.55        | ((sk_C_1) = (k1_xboole_0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.55  thf('38', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.55      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.55  thf('39', plain,
% 0.21/0.55      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C_1) = (k1_xboole_0)))),
% 0.21/0.55      inference('demod', [status(thm)], ['37', '38'])).
% 0.21/0.55  thf('40', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['39'])).
% 0.21/0.55  thf(t60_relat_1, axiom,
% 0.21/0.55    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.55     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.55  thf('41', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.55      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.55  thf('42', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['39'])).
% 0.21/0.55  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.55  thf('43', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.21/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.55  thf('44', plain, (![X0 : $i]: (r1_tarski @ (k1_tarski @ sk_A) @ X0)),
% 0.21/0.55      inference('demod', [status(thm)], ['14', '40', '41', '42', '43'])).
% 0.21/0.55  thf('45', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.21/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.55  thf(d10_xboole_0, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.55  thf('46', plain,
% 0.21/0.55      (![X4 : $i, X6 : $i]:
% 0.21/0.55         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.21/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.55  thf('47', plain,
% 0.21/0.55      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.55  thf('48', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['44', '47'])).
% 0.21/0.55  thf('49', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.55      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.55  thf('50', plain,
% 0.21/0.55      (![X24 : $i, X25 : $i]:
% 0.21/0.55         (((k1_relat_1 @ X25) != (k1_tarski @ X24))
% 0.21/0.55          | ((k2_relat_1 @ X25) = (k1_tarski @ (k1_funct_1 @ X25 @ X24)))
% 0.21/0.55          | ~ (v1_funct_1 @ X25)
% 0.21/0.55          | ~ (v1_relat_1 @ X25))),
% 0.21/0.55      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.21/0.55  thf('51', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.21/0.55          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.55          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.21/0.55          | ((k2_relat_1 @ k1_xboole_0)
% 0.21/0.55              = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.55  thf(t4_subset_1, axiom,
% 0.21/0.55    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.55  thf('52', plain,
% 0.21/0.55      (![X17 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X17))),
% 0.21/0.55      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.55  thf('53', plain,
% 0.21/0.55      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.21/0.55         ((v1_relat_1 @ X28)
% 0.21/0.55          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.21/0.55      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.55  thf('54', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.55      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.55  thf(s3_funct_1__e15_31__wellord2, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ?[B:$i]:
% 0.21/0.55       ( ( ![C:$i]:
% 0.21/0.55           ( ( r2_hidden @ C @ A ) =>
% 0.21/0.55             ( ( k1_funct_1 @ B @ C ) = ( k1_tarski @ C ) ) ) ) & 
% 0.21/0.55         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.21/0.55         ( v1_relat_1 @ B ) ) ))).
% 0.21/0.55  thf('55', plain, (![X37 : $i]: ((k1_relat_1 @ (sk_B @ X37)) = (X37))),
% 0.21/0.55      inference('cnf', [status(esa)], [s3_funct_1__e15_31__wellord2])).
% 0.21/0.55  thf('56', plain,
% 0.21/0.55      (![X23 : $i]:
% 0.21/0.55         (((k1_relat_1 @ X23) != (k1_xboole_0))
% 0.21/0.55          | ((X23) = (k1_xboole_0))
% 0.21/0.55          | ~ (v1_relat_1 @ X23))),
% 0.21/0.55      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.21/0.55  thf('57', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((X0) != (k1_xboole_0))
% 0.21/0.55          | ~ (v1_relat_1 @ (sk_B @ X0))
% 0.21/0.55          | ((sk_B @ X0) = (k1_xboole_0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['55', '56'])).
% 0.21/0.55  thf('58', plain, (![X37 : $i]: (v1_relat_1 @ (sk_B @ X37))),
% 0.21/0.55      inference('cnf', [status(esa)], [s3_funct_1__e15_31__wellord2])).
% 0.21/0.55  thf('59', plain,
% 0.21/0.55      (![X0 : $i]: (((X0) != (k1_xboole_0)) | ((sk_B @ X0) = (k1_xboole_0)))),
% 0.21/0.55      inference('demod', [status(thm)], ['57', '58'])).
% 0.21/0.55  thf('60', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['59'])).
% 0.21/0.55  thf('61', plain, (![X37 : $i]: (v1_funct_1 @ (sk_B @ X37))),
% 0.21/0.55      inference('cnf', [status(esa)], [s3_funct_1__e15_31__wellord2])).
% 0.21/0.55  thf('62', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.21/0.55      inference('sup+', [status(thm)], ['60', '61'])).
% 0.21/0.55  thf('63', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.55      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.55  thf('64', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.21/0.55          | ((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0))))),
% 0.21/0.55      inference('demod', [status(thm)], ['51', '54', '62', '63'])).
% 0.21/0.55  thf('65', plain,
% 0.21/0.55      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.55        | ((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['48', '64'])).
% 0.21/0.55  thf('66', plain,
% 0.21/0.55      (((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['65'])).
% 0.21/0.55  thf('67', plain,
% 0.21/0.55      (((k2_relat_1 @ sk_C_1) != (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.21/0.55      inference('demod', [status(thm)], ['32', '33'])).
% 0.21/0.55  thf('68', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['39'])).
% 0.21/0.55  thf('69', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.55      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.55  thf('70', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.21/0.55      inference('simplify', [status(thm)], ['39'])).
% 0.21/0.55  thf('71', plain,
% 0.21/0.55      (((k1_xboole_0) != (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A)))),
% 0.21/0.55      inference('demod', [status(thm)], ['67', '68', '69', '70'])).
% 0.21/0.55  thf('72', plain, ($false),
% 0.21/0.55      inference('simplify_reflect-', [status(thm)], ['66', '71'])).
% 0.21/0.55  
% 0.21/0.55  % SZS output end Refutation
% 0.21/0.55  
% 0.21/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
