%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RzNYJkao4I

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:38 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 131 expanded)
%              Number of leaves         :   37 (  55 expanded)
%              Depth                    :   16
%              Number of atoms          :  683 (1378 expanded)
%              Number of equality atoms :   67 ( 115 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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

thf('2',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( r2_hidden @ X32 @ X33 )
      | ( X34 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X35 @ X32 ) @ ( k2_relset_1 @ X33 @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t6_funct_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C ) )
      | ~ ( v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_C )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('5',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k2_relset_1 @ X30 @ X31 @ X29 )
        = ( k2_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('6',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ ( k2_relat_1 @ sk_C ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['3','6','7','8'])).

thf('10',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ ( k2_relat_1 @ sk_C ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C @ ( sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','11'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('13',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(fc3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc3_xboole_0])).

thf('15',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C @ ( sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k2_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('18',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('20',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v4_relat_1 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('21',plain,(
    v4_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('22',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v4_relat_1 @ X16 @ X17 )
      | ( r1_tarski @ ( k1_relat_1 @ X16 ) @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('23',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('25',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v1_relat_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('26',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l45_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('29',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( X14
        = ( k2_tarski @ X12 @ X13 ) )
      | ( X14
        = ( k1_tarski @ X13 ) )
      | ( X14
        = ( k1_tarski @ X12 ) )
      | ( X14 = k1_xboole_0 )
      | ~ ( r1_tarski @ X14 @ ( k2_tarski @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_tarski @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','31'])).

thf('33',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('34',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['34'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('36',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k1_relat_1 @ X20 )
       != ( k1_tarski @ X19 ) )
      | ( ( k2_relat_1 @ X20 )
        = ( k1_tarski @ ( k1_funct_1 @ X20 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_C ) )
      | ( ( k1_relat_1 @ sk_C )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['37'])).

thf('39',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['24','25'])).

thf('41',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('44',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['41','44'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('46',plain,(
    ! [X18: $i] :
      ( ( ( k1_relat_1 @ X18 )
       != k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('47',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['24','25'])).

thf('49',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['49'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('51',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('52',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('53',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('54',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X21 @ X22 )
      | ~ ( r1_tarski @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    $false ),
    inference(demod,[status(thm)],['18','50','51','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RzNYJkao4I
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:18:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.41/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.59  % Solved by: fo/fo7.sh
% 0.41/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.59  % done 256 iterations in 0.137s
% 0.41/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.59  % SZS output start Refutation
% 0.41/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.41/0.59  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.41/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.41/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.41/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.41/0.59  thf(sk_B_type, type, sk_B: $i > $i).
% 0.41/0.59  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.41/0.59  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.41/0.59  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.41/0.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.41/0.59  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.41/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.41/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.41/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.41/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.41/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.41/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.59  thf(d1_xboole_0, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.41/0.59  thf('0', plain,
% 0.41/0.59      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.41/0.59      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.41/0.59  thf(t62_funct_2, conjecture,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.41/0.59         ( m1_subset_1 @
% 0.41/0.59           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.41/0.59       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.41/0.59         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.41/0.59           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.41/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.59    (~( ![A:$i,B:$i,C:$i]:
% 0.41/0.59        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.41/0.59            ( m1_subset_1 @
% 0.41/0.59              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.41/0.59          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.41/0.59            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.41/0.59              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 0.41/0.59    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 0.41/0.59  thf('1', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_C @ 
% 0.41/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf(t6_funct_2, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.59     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.41/0.59         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.59       ( ( r2_hidden @ C @ A ) =>
% 0.41/0.59         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.41/0.59           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.41/0.59  thf('2', plain,
% 0.41/0.59      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.41/0.59         (~ (r2_hidden @ X32 @ X33)
% 0.41/0.59          | ((X34) = (k1_xboole_0))
% 0.41/0.59          | ~ (v1_funct_1 @ X35)
% 0.41/0.59          | ~ (v1_funct_2 @ X35 @ X33 @ X34)
% 0.41/0.59          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.41/0.59          | (r2_hidden @ (k1_funct_1 @ X35 @ X32) @ 
% 0.41/0.59             (k2_relset_1 @ X33 @ X34 @ X35)))),
% 0.41/0.59      inference('cnf', [status(esa)], [t6_funct_2])).
% 0.41/0.59  thf('3', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ 
% 0.41/0.59           (k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C))
% 0.41/0.59          | ~ (v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.41/0.59          | ~ (v1_funct_1 @ sk_C)
% 0.41/0.59          | ((sk_B_1) = (k1_xboole_0))
% 0.41/0.59          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['1', '2'])).
% 0.41/0.59  thf('4', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_C @ 
% 0.41/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf(redefinition_k2_relset_1, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.59       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.41/0.59  thf('5', plain,
% 0.41/0.59      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.41/0.59         (((k2_relset_1 @ X30 @ X31 @ X29) = (k2_relat_1 @ X29))
% 0.41/0.59          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.41/0.59      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.41/0.59  thf('6', plain,
% 0.41/0.59      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 0.41/0.59         = (k2_relat_1 @ sk_C))),
% 0.41/0.59      inference('sup-', [status(thm)], ['4', '5'])).
% 0.41/0.59  thf('7', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('9', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ (k2_relat_1 @ sk_C))
% 0.41/0.59          | ((sk_B_1) = (k1_xboole_0))
% 0.41/0.59          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.41/0.59      inference('demod', [status(thm)], ['3', '6', '7', '8'])).
% 0.41/0.59  thf('10', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('11', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ (k2_relat_1 @ sk_C))
% 0.41/0.59          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.41/0.59      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.41/0.59  thf('12', plain,
% 0.41/0.59      (((v1_xboole_0 @ (k1_tarski @ sk_A))
% 0.41/0.59        | (r2_hidden @ (k1_funct_1 @ sk_C @ (sk_B @ (k1_tarski @ sk_A))) @ 
% 0.41/0.59           (k2_relat_1 @ sk_C)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['0', '11'])).
% 0.41/0.59  thf(t69_enumset1, axiom,
% 0.41/0.59    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.41/0.59  thf('13', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.41/0.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.41/0.59  thf(fc3_xboole_0, axiom,
% 0.41/0.59    (![A:$i,B:$i]: ( ~( v1_xboole_0 @ ( k2_tarski @ A @ B ) ) ))).
% 0.41/0.59  thf('14', plain,
% 0.41/0.59      (![X10 : $i, X11 : $i]: ~ (v1_xboole_0 @ (k2_tarski @ X10 @ X11))),
% 0.41/0.59      inference('cnf', [status(esa)], [fc3_xboole_0])).
% 0.41/0.59  thf('15', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.41/0.59      inference('sup-', [status(thm)], ['13', '14'])).
% 0.41/0.59  thf('16', plain,
% 0.41/0.59      ((r2_hidden @ (k1_funct_1 @ sk_C @ (sk_B @ (k1_tarski @ sk_A))) @ 
% 0.41/0.59        (k2_relat_1 @ sk_C))),
% 0.41/0.59      inference('clc', [status(thm)], ['12', '15'])).
% 0.41/0.59  thf('17', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.41/0.59      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.41/0.59  thf('18', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.41/0.59      inference('sup-', [status(thm)], ['16', '17'])).
% 0.41/0.59  thf('19', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_C @ 
% 0.41/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf(cc2_relset_1, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.59       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.41/0.59  thf('20', plain,
% 0.41/0.59      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.41/0.59         ((v4_relat_1 @ X26 @ X27)
% 0.41/0.59          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.41/0.59      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.41/0.59  thf('21', plain, ((v4_relat_1 @ sk_C @ (k1_tarski @ sk_A))),
% 0.41/0.59      inference('sup-', [status(thm)], ['19', '20'])).
% 0.41/0.59  thf(d18_relat_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( v1_relat_1 @ B ) =>
% 0.41/0.59       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.41/0.59  thf('22', plain,
% 0.41/0.59      (![X16 : $i, X17 : $i]:
% 0.41/0.59         (~ (v4_relat_1 @ X16 @ X17)
% 0.41/0.59          | (r1_tarski @ (k1_relat_1 @ X16) @ X17)
% 0.41/0.59          | ~ (v1_relat_1 @ X16))),
% 0.41/0.59      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.41/0.59  thf('23', plain,
% 0.41/0.59      ((~ (v1_relat_1 @ sk_C)
% 0.41/0.59        | (r1_tarski @ (k1_relat_1 @ sk_C) @ (k1_tarski @ sk_A)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['21', '22'])).
% 0.41/0.59  thf('24', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_C @ 
% 0.41/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf(cc1_relset_1, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.59       ( v1_relat_1 @ C ) ))).
% 0.41/0.59  thf('25', plain,
% 0.41/0.59      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.41/0.59         ((v1_relat_1 @ X23)
% 0.41/0.59          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.41/0.59      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.41/0.59  thf('26', plain, ((v1_relat_1 @ sk_C)),
% 0.41/0.59      inference('sup-', [status(thm)], ['24', '25'])).
% 0.41/0.59  thf('27', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ (k1_tarski @ sk_A))),
% 0.41/0.59      inference('demod', [status(thm)], ['23', '26'])).
% 0.41/0.59  thf('28', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.41/0.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.41/0.59  thf(l45_zfmisc_1, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.41/0.59       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.41/0.59            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.41/0.59  thf('29', plain,
% 0.41/0.59      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.41/0.59         (((X14) = (k2_tarski @ X12 @ X13))
% 0.41/0.59          | ((X14) = (k1_tarski @ X13))
% 0.41/0.59          | ((X14) = (k1_tarski @ X12))
% 0.41/0.59          | ((X14) = (k1_xboole_0))
% 0.41/0.59          | ~ (r1_tarski @ X14 @ (k2_tarski @ X12 @ X13)))),
% 0.41/0.59      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.41/0.59  thf('30', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.41/0.59          | ((X1) = (k1_xboole_0))
% 0.41/0.59          | ((X1) = (k1_tarski @ X0))
% 0.41/0.59          | ((X1) = (k1_tarski @ X0))
% 0.41/0.59          | ((X1) = (k2_tarski @ X0 @ X0)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['28', '29'])).
% 0.41/0.59  thf('31', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         (((X1) = (k2_tarski @ X0 @ X0))
% 0.41/0.59          | ((X1) = (k1_tarski @ X0))
% 0.41/0.59          | ((X1) = (k1_xboole_0))
% 0.41/0.59          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 0.41/0.59      inference('simplify', [status(thm)], ['30'])).
% 0.41/0.59  thf('32', plain,
% 0.41/0.59      ((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 0.41/0.59        | ((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A))
% 0.41/0.59        | ((k1_relat_1 @ sk_C) = (k2_tarski @ sk_A @ sk_A)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['27', '31'])).
% 0.41/0.59  thf('33', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.41/0.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.41/0.59  thf('34', plain,
% 0.41/0.59      ((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 0.41/0.59        | ((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A))
% 0.41/0.59        | ((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A)))),
% 0.41/0.59      inference('demod', [status(thm)], ['32', '33'])).
% 0.41/0.59  thf('35', plain,
% 0.41/0.59      ((((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A))
% 0.41/0.59        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.41/0.59      inference('simplify', [status(thm)], ['34'])).
% 0.41/0.59  thf(t14_funct_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.41/0.59       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.41/0.59         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.41/0.59  thf('36', plain,
% 0.41/0.59      (![X19 : $i, X20 : $i]:
% 0.41/0.59         (((k1_relat_1 @ X20) != (k1_tarski @ X19))
% 0.41/0.59          | ((k2_relat_1 @ X20) = (k1_tarski @ (k1_funct_1 @ X20 @ X19)))
% 0.41/0.59          | ~ (v1_funct_1 @ X20)
% 0.41/0.59          | ~ (v1_relat_1 @ X20))),
% 0.41/0.59      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.41/0.59  thf('37', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_C))
% 0.41/0.59          | ((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 0.41/0.59          | ~ (v1_relat_1 @ X0)
% 0.41/0.59          | ~ (v1_funct_1 @ X0)
% 0.41/0.59          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.41/0.59      inference('sup-', [status(thm)], ['35', '36'])).
% 0.41/0.59  thf('38', plain,
% 0.41/0.59      ((((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 0.41/0.59        | ~ (v1_funct_1 @ sk_C)
% 0.41/0.59        | ~ (v1_relat_1 @ sk_C)
% 0.41/0.59        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.41/0.59      inference('eq_res', [status(thm)], ['37'])).
% 0.41/0.59  thf('39', plain, ((v1_funct_1 @ sk_C)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('40', plain, ((v1_relat_1 @ sk_C)),
% 0.41/0.59      inference('sup-', [status(thm)], ['24', '25'])).
% 0.41/0.59  thf('41', plain,
% 0.41/0.59      ((((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 0.41/0.59        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.41/0.59      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.41/0.59  thf('42', plain,
% 0.41/0.59      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 0.41/0.59         != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('43', plain,
% 0.41/0.59      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 0.41/0.59         = (k2_relat_1 @ sk_C))),
% 0.41/0.59      inference('sup-', [status(thm)], ['4', '5'])).
% 0.41/0.59  thf('44', plain,
% 0.41/0.59      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.41/0.59      inference('demod', [status(thm)], ['42', '43'])).
% 0.41/0.59  thf('45', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.41/0.59      inference('simplify_reflect-', [status(thm)], ['41', '44'])).
% 0.41/0.59  thf(t64_relat_1, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( v1_relat_1 @ A ) =>
% 0.41/0.59       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.41/0.59           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.41/0.59         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.41/0.59  thf('46', plain,
% 0.41/0.59      (![X18 : $i]:
% 0.41/0.59         (((k1_relat_1 @ X18) != (k1_xboole_0))
% 0.41/0.59          | ((X18) = (k1_xboole_0))
% 0.41/0.59          | ~ (v1_relat_1 @ X18))),
% 0.41/0.59      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.41/0.59  thf('47', plain,
% 0.41/0.59      ((((k1_xboole_0) != (k1_xboole_0))
% 0.41/0.59        | ~ (v1_relat_1 @ sk_C)
% 0.41/0.59        | ((sk_C) = (k1_xboole_0)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['45', '46'])).
% 0.41/0.59  thf('48', plain, ((v1_relat_1 @ sk_C)),
% 0.41/0.59      inference('sup-', [status(thm)], ['24', '25'])).
% 0.41/0.59  thf('49', plain,
% 0.41/0.59      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.41/0.59      inference('demod', [status(thm)], ['47', '48'])).
% 0.41/0.59  thf('50', plain, (((sk_C) = (k1_xboole_0))),
% 0.41/0.59      inference('simplify', [status(thm)], ['49'])).
% 0.41/0.59  thf(t60_relat_1, axiom,
% 0.41/0.59    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.41/0.59     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.41/0.59  thf('51', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.41/0.59      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.41/0.59  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.41/0.59  thf('52', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.41/0.59      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.41/0.59  thf('53', plain,
% 0.41/0.59      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.41/0.59      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.41/0.59  thf(t7_ordinal1, axiom,
% 0.41/0.59    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.41/0.59  thf('54', plain,
% 0.41/0.59      (![X21 : $i, X22 : $i]:
% 0.41/0.59         (~ (r2_hidden @ X21 @ X22) | ~ (r1_tarski @ X22 @ X21))),
% 0.41/0.59      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.41/0.59  thf('55', plain,
% 0.41/0.59      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['53', '54'])).
% 0.41/0.59  thf('56', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.41/0.59      inference('sup-', [status(thm)], ['52', '55'])).
% 0.41/0.59  thf('57', plain, ($false),
% 0.41/0.59      inference('demod', [status(thm)], ['18', '50', '51', '56'])).
% 0.41/0.59  
% 0.41/0.59  % SZS output end Refutation
% 0.41/0.59  
% 0.41/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
