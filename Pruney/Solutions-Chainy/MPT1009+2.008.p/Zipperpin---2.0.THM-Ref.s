%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CFG9DYQka2

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:49 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 281 expanded)
%              Number of leaves         :   34 ( 101 expanded)
%              Depth                    :   19
%              Number of atoms          :  674 (2859 expanded)
%              Number of equality atoms :   40 ( 121 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(t64_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_funct_2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( ( k7_relset_1 @ X34 @ X35 @ X33 @ X36 )
        = ( k9_relat_1 @ X33 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_zfmisc_1 @ X10 @ X11 )
        = k1_xboole_0 )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('6',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X11 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v5_relat_1 @ X30 @ X32 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('9',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('10',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v5_relat_1 @ X21 @ X22 )
      | ( r1_tarski @ ( k2_relat_1 @ X21 ) @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('13',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v1_relat_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('14',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['11','14'])).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('16',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X23 @ X24 ) @ ( k2_relat_1 @ X23 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('17',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v4_relat_1 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('19',plain,(
    v4_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('20',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v4_relat_1 @ X19 @ X20 )
      | ( r1_tarski @ ( k1_relat_1 @ X19 ) @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['12','13'])).

thf('23',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('24',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X7
        = ( k1_tarski @ X6 ) )
      | ( X7 = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('25',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
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
    ! [X25: $i,X26: $i] :
      ( ( ( k1_relat_1 @ X26 )
       != ( k1_tarski @ X25 ) )
      | ( ( k2_relat_1 @ X26 )
        = ( k1_tarski @ ( k1_funct_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D ) )
      | ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['27'])).

thf('29',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['12','13'])).

thf('31',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('33',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['12','13'])).

thf('36',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['34','35'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('37',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X37 ) @ X38 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X37 ) @ X39 )
      | ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ sk_D )
      | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('39',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('40',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['12','13'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X1 ) ) ),
    inference(demod,[status(thm)],['38','41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['15','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['6','44'])).

thf('46',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('47',plain,(
    r1_tarski @ sk_D @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('49',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    sk_D = k1_xboole_0 ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('53',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v5_relat_1 @ X30 @ X32 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v5_relat_1 @ X21 @ X22 )
      | ( r1_tarski @ ( k2_relat_1 @ X21 ) @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('58',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v1_relat_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('59',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('62',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X23 @ X24 ) @ ( k2_relat_1 @ X23 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['57','58'])).

thf('66',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    sk_D = k1_xboole_0 ),
    inference('sup-',[status(thm)],['47','50'])).

thf('70',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('71',plain,(
    $false ),
    inference(demod,[status(thm)],['4','51','68','69','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CFG9DYQka2
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:42:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.63  % Solved by: fo/fo7.sh
% 0.39/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.63  % done 254 iterations in 0.138s
% 0.39/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.63  % SZS output start Refutation
% 0.39/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.63  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.63  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.39/0.63  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.63  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.39/0.63  thf(sk_D_type, type, sk_D: $i).
% 0.39/0.63  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.39/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.63  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.39/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.63  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.39/0.63  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.39/0.63  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.63  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.39/0.63  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.39/0.63  thf(t64_funct_2, conjecture,
% 0.39/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.63     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.39/0.63         ( m1_subset_1 @
% 0.39/0.63           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.39/0.63       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.39/0.63         ( r1_tarski @
% 0.39/0.63           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.39/0.63           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.39/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.63    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.63        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.39/0.63            ( m1_subset_1 @
% 0.39/0.63              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.39/0.63          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.39/0.63            ( r1_tarski @
% 0.39/0.63              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.39/0.63              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.39/0.63    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.39/0.63  thf('0', plain,
% 0.39/0.63      (~ (r1_tarski @ 
% 0.39/0.63          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.39/0.63          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('1', plain,
% 0.39/0.63      ((m1_subset_1 @ sk_D @ 
% 0.39/0.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf(redefinition_k7_relset_1, axiom,
% 0.39/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.63       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.39/0.63  thf('2', plain,
% 0.39/0.63      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.39/0.63         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.39/0.63          | ((k7_relset_1 @ X34 @ X35 @ X33 @ X36) = (k9_relat_1 @ X33 @ X36)))),
% 0.39/0.63      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.39/0.63  thf('3', plain,
% 0.39/0.63      (![X0 : $i]:
% 0.39/0.63         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.39/0.63           = (k9_relat_1 @ sk_D @ X0))),
% 0.39/0.63      inference('sup-', [status(thm)], ['1', '2'])).
% 0.39/0.63  thf('4', plain,
% 0.39/0.63      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.39/0.63          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.39/0.63      inference('demod', [status(thm)], ['0', '3'])).
% 0.39/0.63  thf(t113_zfmisc_1, axiom,
% 0.39/0.63    (![A:$i,B:$i]:
% 0.39/0.63     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.39/0.63       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.39/0.63  thf('5', plain,
% 0.39/0.63      (![X10 : $i, X11 : $i]:
% 0.39/0.63         (((k2_zfmisc_1 @ X10 @ X11) = (k1_xboole_0))
% 0.39/0.63          | ((X10) != (k1_xboole_0)))),
% 0.39/0.63      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.39/0.63  thf('6', plain,
% 0.39/0.63      (![X11 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X11) = (k1_xboole_0))),
% 0.39/0.63      inference('simplify', [status(thm)], ['5'])).
% 0.39/0.63  thf('7', plain,
% 0.39/0.63      ((m1_subset_1 @ sk_D @ 
% 0.39/0.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf(cc2_relset_1, axiom,
% 0.39/0.63    (![A:$i,B:$i,C:$i]:
% 0.39/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.63       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.39/0.63  thf('8', plain,
% 0.39/0.63      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.39/0.63         ((v5_relat_1 @ X30 @ X32)
% 0.39/0.63          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.39/0.63      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.39/0.63  thf('9', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 0.39/0.63      inference('sup-', [status(thm)], ['7', '8'])).
% 0.39/0.63  thf(d19_relat_1, axiom,
% 0.39/0.63    (![A:$i,B:$i]:
% 0.39/0.63     ( ( v1_relat_1 @ B ) =>
% 0.39/0.63       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.39/0.63  thf('10', plain,
% 0.39/0.63      (![X21 : $i, X22 : $i]:
% 0.39/0.63         (~ (v5_relat_1 @ X21 @ X22)
% 0.39/0.63          | (r1_tarski @ (k2_relat_1 @ X21) @ X22)
% 0.39/0.63          | ~ (v1_relat_1 @ X21))),
% 0.39/0.63      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.39/0.63  thf('11', plain,
% 0.39/0.63      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 0.39/0.63      inference('sup-', [status(thm)], ['9', '10'])).
% 0.39/0.63  thf('12', plain,
% 0.39/0.63      ((m1_subset_1 @ sk_D @ 
% 0.39/0.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf(cc1_relset_1, axiom,
% 0.39/0.63    (![A:$i,B:$i,C:$i]:
% 0.39/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.63       ( v1_relat_1 @ C ) ))).
% 0.39/0.63  thf('13', plain,
% 0.39/0.63      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.39/0.63         ((v1_relat_1 @ X27)
% 0.39/0.63          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.39/0.63      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.39/0.63  thf('14', plain, ((v1_relat_1 @ sk_D)),
% 0.39/0.63      inference('sup-', [status(thm)], ['12', '13'])).
% 0.39/0.63  thf('15', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 0.39/0.63      inference('demod', [status(thm)], ['11', '14'])).
% 0.39/0.63  thf(t144_relat_1, axiom,
% 0.39/0.63    (![A:$i,B:$i]:
% 0.39/0.63     ( ( v1_relat_1 @ B ) =>
% 0.39/0.63       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.39/0.63  thf('16', plain,
% 0.39/0.63      (![X23 : $i, X24 : $i]:
% 0.39/0.63         ((r1_tarski @ (k9_relat_1 @ X23 @ X24) @ (k2_relat_1 @ X23))
% 0.39/0.63          | ~ (v1_relat_1 @ X23))),
% 0.39/0.63      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.39/0.63  thf('17', plain,
% 0.39/0.63      ((m1_subset_1 @ sk_D @ 
% 0.39/0.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('18', plain,
% 0.39/0.63      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.39/0.63         ((v4_relat_1 @ X30 @ X31)
% 0.39/0.63          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.39/0.63      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.39/0.63  thf('19', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 0.39/0.63      inference('sup-', [status(thm)], ['17', '18'])).
% 0.39/0.63  thf(d18_relat_1, axiom,
% 0.39/0.63    (![A:$i,B:$i]:
% 0.39/0.63     ( ( v1_relat_1 @ B ) =>
% 0.39/0.63       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.39/0.63  thf('20', plain,
% 0.39/0.63      (![X19 : $i, X20 : $i]:
% 0.39/0.63         (~ (v4_relat_1 @ X19 @ X20)
% 0.39/0.63          | (r1_tarski @ (k1_relat_1 @ X19) @ X20)
% 0.39/0.63          | ~ (v1_relat_1 @ X19))),
% 0.39/0.63      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.39/0.63  thf('21', plain,
% 0.39/0.63      ((~ (v1_relat_1 @ sk_D)
% 0.39/0.63        | (r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A)))),
% 0.39/0.63      inference('sup-', [status(thm)], ['19', '20'])).
% 0.39/0.63  thf('22', plain, ((v1_relat_1 @ sk_D)),
% 0.39/0.63      inference('sup-', [status(thm)], ['12', '13'])).
% 0.39/0.63  thf('23', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 0.39/0.63      inference('demod', [status(thm)], ['21', '22'])).
% 0.39/0.63  thf(l3_zfmisc_1, axiom,
% 0.39/0.63    (![A:$i,B:$i]:
% 0.39/0.63     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.39/0.63       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.39/0.63  thf('24', plain,
% 0.39/0.63      (![X6 : $i, X7 : $i]:
% 0.39/0.63         (((X7) = (k1_tarski @ X6))
% 0.39/0.63          | ((X7) = (k1_xboole_0))
% 0.39/0.63          | ~ (r1_tarski @ X7 @ (k1_tarski @ X6)))),
% 0.39/0.63      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.39/0.63  thf('25', plain,
% 0.39/0.63      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.39/0.63        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 0.39/0.63      inference('sup-', [status(thm)], ['23', '24'])).
% 0.39/0.63  thf(t14_funct_1, axiom,
% 0.39/0.63    (![A:$i,B:$i]:
% 0.39/0.63     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.39/0.63       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.39/0.63         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.39/0.63  thf('26', plain,
% 0.39/0.63      (![X25 : $i, X26 : $i]:
% 0.39/0.63         (((k1_relat_1 @ X26) != (k1_tarski @ X25))
% 0.39/0.63          | ((k2_relat_1 @ X26) = (k1_tarski @ (k1_funct_1 @ X26 @ X25)))
% 0.39/0.63          | ~ (v1_funct_1 @ X26)
% 0.39/0.63          | ~ (v1_relat_1 @ X26))),
% 0.39/0.63      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.39/0.63  thf('27', plain,
% 0.39/0.63      (![X0 : $i]:
% 0.39/0.63         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 0.39/0.63          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.39/0.63          | ~ (v1_relat_1 @ X0)
% 0.39/0.63          | ~ (v1_funct_1 @ X0)
% 0.39/0.63          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.39/0.63      inference('sup-', [status(thm)], ['25', '26'])).
% 0.39/0.63  thf('28', plain,
% 0.39/0.63      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.39/0.63        | ~ (v1_funct_1 @ sk_D)
% 0.39/0.63        | ~ (v1_relat_1 @ sk_D)
% 0.39/0.63        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.39/0.63      inference('eq_res', [status(thm)], ['27'])).
% 0.39/0.63  thf('29', plain, ((v1_funct_1 @ sk_D)),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('30', plain, ((v1_relat_1 @ sk_D)),
% 0.39/0.63      inference('sup-', [status(thm)], ['12', '13'])).
% 0.39/0.63  thf('31', plain,
% 0.39/0.63      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.39/0.63        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.39/0.63      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.39/0.63  thf('32', plain,
% 0.39/0.63      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.39/0.63          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.39/0.63      inference('demod', [status(thm)], ['0', '3'])).
% 0.39/0.63  thf('33', plain,
% 0.39/0.63      ((~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))
% 0.39/0.63        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.39/0.63      inference('sup-', [status(thm)], ['31', '32'])).
% 0.39/0.63  thf('34', plain,
% 0.39/0.63      ((~ (v1_relat_1 @ sk_D) | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.39/0.63      inference('sup-', [status(thm)], ['16', '33'])).
% 0.39/0.63  thf('35', plain, ((v1_relat_1 @ sk_D)),
% 0.39/0.63      inference('sup-', [status(thm)], ['12', '13'])).
% 0.39/0.63  thf('36', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.39/0.63      inference('demod', [status(thm)], ['34', '35'])).
% 0.39/0.63  thf(t11_relset_1, axiom,
% 0.39/0.63    (![A:$i,B:$i,C:$i]:
% 0.39/0.63     ( ( v1_relat_1 @ C ) =>
% 0.39/0.63       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.39/0.63           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.39/0.63         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.39/0.63  thf('37', plain,
% 0.39/0.63      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.39/0.63         (~ (r1_tarski @ (k1_relat_1 @ X37) @ X38)
% 0.39/0.63          | ~ (r1_tarski @ (k2_relat_1 @ X37) @ X39)
% 0.39/0.63          | (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.39/0.63          | ~ (v1_relat_1 @ X37))),
% 0.39/0.63      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.39/0.63  thf('38', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]:
% 0.39/0.63         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.39/0.63          | ~ (v1_relat_1 @ sk_D)
% 0.39/0.63          | (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 0.39/0.63          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X1))),
% 0.39/0.63      inference('sup-', [status(thm)], ['36', '37'])).
% 0.39/0.63  thf(t4_subset_1, axiom,
% 0.39/0.63    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.39/0.63  thf('39', plain,
% 0.39/0.63      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.39/0.63      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.39/0.63  thf(t3_subset, axiom,
% 0.39/0.63    (![A:$i,B:$i]:
% 0.39/0.63     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.39/0.63  thf('40', plain,
% 0.39/0.63      (![X13 : $i, X14 : $i]:
% 0.39/0.63         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.39/0.63      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.63  thf('41', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.39/0.63      inference('sup-', [status(thm)], ['39', '40'])).
% 0.39/0.63  thf('42', plain, ((v1_relat_1 @ sk_D)),
% 0.39/0.63      inference('sup-', [status(thm)], ['12', '13'])).
% 0.39/0.63  thf('43', plain,
% 0.39/0.63      (![X0 : $i, X1 : $i]:
% 0.39/0.63         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 0.39/0.63          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X1))),
% 0.39/0.63      inference('demod', [status(thm)], ['38', '41', '42'])).
% 0.39/0.63  thf('44', plain,
% 0.39/0.63      (![X0 : $i]:
% 0.39/0.63         (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))),
% 0.39/0.63      inference('sup-', [status(thm)], ['15', '43'])).
% 0.39/0.63  thf('45', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.39/0.63      inference('sup+', [status(thm)], ['6', '44'])).
% 0.39/0.63  thf('46', plain,
% 0.39/0.63      (![X13 : $i, X14 : $i]:
% 0.39/0.63         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.39/0.63      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.63  thf('47', plain, ((r1_tarski @ sk_D @ k1_xboole_0)),
% 0.39/0.63      inference('sup-', [status(thm)], ['45', '46'])).
% 0.39/0.63  thf('48', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.39/0.63      inference('sup-', [status(thm)], ['39', '40'])).
% 0.39/0.63  thf(d10_xboole_0, axiom,
% 0.39/0.63    (![A:$i,B:$i]:
% 0.39/0.63     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.39/0.63  thf('49', plain,
% 0.39/0.63      (![X0 : $i, X2 : $i]:
% 0.39/0.63         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.39/0.63      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.63  thf('50', plain,
% 0.39/0.63      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.39/0.63      inference('sup-', [status(thm)], ['48', '49'])).
% 0.39/0.63  thf('51', plain, (((sk_D) = (k1_xboole_0))),
% 0.39/0.63      inference('sup-', [status(thm)], ['47', '50'])).
% 0.39/0.63  thf('52', plain,
% 0.39/0.63      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.39/0.63      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.39/0.63  thf('53', plain,
% 0.39/0.63      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.39/0.63         ((v5_relat_1 @ X30 @ X32)
% 0.39/0.63          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.39/0.63      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.39/0.63  thf('54', plain, (![X0 : $i]: (v5_relat_1 @ k1_xboole_0 @ X0)),
% 0.39/0.63      inference('sup-', [status(thm)], ['52', '53'])).
% 0.39/0.63  thf('55', plain,
% 0.39/0.63      (![X21 : $i, X22 : $i]:
% 0.39/0.63         (~ (v5_relat_1 @ X21 @ X22)
% 0.39/0.63          | (r1_tarski @ (k2_relat_1 @ X21) @ X22)
% 0.39/0.63          | ~ (v1_relat_1 @ X21))),
% 0.39/0.63      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.39/0.63  thf('56', plain,
% 0.39/0.63      (![X0 : $i]:
% 0.39/0.63         (~ (v1_relat_1 @ k1_xboole_0)
% 0.39/0.63          | (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0))),
% 0.39/0.63      inference('sup-', [status(thm)], ['54', '55'])).
% 0.39/0.63  thf('57', plain,
% 0.39/0.63      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.39/0.63      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.39/0.63  thf('58', plain,
% 0.39/0.63      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.39/0.63         ((v1_relat_1 @ X27)
% 0.39/0.63          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.39/0.63      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.39/0.63  thf('59', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.39/0.63      inference('sup-', [status(thm)], ['57', '58'])).
% 0.39/0.63  thf('60', plain, (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0)),
% 0.39/0.63      inference('demod', [status(thm)], ['56', '59'])).
% 0.39/0.63  thf('61', plain,
% 0.39/0.63      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.39/0.63      inference('sup-', [status(thm)], ['48', '49'])).
% 0.39/0.63  thf('62', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.63      inference('sup-', [status(thm)], ['60', '61'])).
% 0.39/0.63  thf('63', plain,
% 0.39/0.63      (![X23 : $i, X24 : $i]:
% 0.39/0.63         ((r1_tarski @ (k9_relat_1 @ X23 @ X24) @ (k2_relat_1 @ X23))
% 0.39/0.63          | ~ (v1_relat_1 @ X23))),
% 0.39/0.63      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.39/0.63  thf('64', plain,
% 0.39/0.63      (![X0 : $i]:
% 0.39/0.63         ((r1_tarski @ (k9_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.39/0.63          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.39/0.63      inference('sup+', [status(thm)], ['62', '63'])).
% 0.39/0.63  thf('65', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.39/0.63      inference('sup-', [status(thm)], ['57', '58'])).
% 0.39/0.63  thf('66', plain,
% 0.39/0.63      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)),
% 0.39/0.63      inference('demod', [status(thm)], ['64', '65'])).
% 0.39/0.63  thf('67', plain,
% 0.39/0.63      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.39/0.63      inference('sup-', [status(thm)], ['48', '49'])).
% 0.39/0.63  thf('68', plain,
% 0.39/0.63      (![X0 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.39/0.63      inference('sup-', [status(thm)], ['66', '67'])).
% 0.39/0.63  thf('69', plain, (((sk_D) = (k1_xboole_0))),
% 0.39/0.63      inference('sup-', [status(thm)], ['47', '50'])).
% 0.39/0.63  thf('70', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.39/0.63      inference('sup-', [status(thm)], ['39', '40'])).
% 0.39/0.63  thf('71', plain, ($false),
% 0.39/0.63      inference('demod', [status(thm)], ['4', '51', '68', '69', '70'])).
% 0.39/0.63  
% 0.39/0.63  % SZS output end Refutation
% 0.39/0.63  
% 0.48/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
