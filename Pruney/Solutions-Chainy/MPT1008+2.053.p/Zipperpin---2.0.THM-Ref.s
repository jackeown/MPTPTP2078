%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pVkwU7hyLe

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:38 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 286 expanded)
%              Number of leaves         :   40 ( 103 expanded)
%              Depth                    :   23
%              Number of atoms          :  814 (3049 expanded)
%              Number of equality atoms :   79 ( 263 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    v1_funct_2 @ sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v4_relat_1 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('4',plain,(
    v4_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('5',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v4_relat_1 @ X18 @ X19 )
      | ( r1_tarski @ ( k1_relat_1 @ X18 ) @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('8',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v1_relat_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('9',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['6','9'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('11',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X12
        = ( k1_tarski @ X11 ) )
      | ( X12 = k1_xboole_0 )
      | ~ ( r1_tarski @ X12 @ ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('12',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('13',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k1_relat_1 @ X28 )
       != ( k1_tarski @ X27 ) )
      | ( ( k2_relat_1 @ X28 )
        = ( k1_tarski @ ( k1_funct_1 @ X28 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_C_1 ) )
      | ( ( k1_relat_1 @ sk_C_1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['14'])).

thf('16',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('18',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('21',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k2_relset_1 @ X38 @ X39 @ X37 )
        = ( k2_relat_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('22',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['18','23'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('25',plain,(
    ! [X22: $i] :
      ( ( ( k1_relat_1 @ X22 )
       != k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('26',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('28',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    v1_funct_2 @ k1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['1','29'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('31',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t6_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )).

thf('32',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( r2_hidden @ X40 @ X41 )
      | ( X42 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X43 @ X40 ) @ ( k2_relset_1 @ X41 @ X42 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t6_funct_2])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ k1_xboole_0 @ X2 ) @ ( k2_relset_1 @ X1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('35',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k2_relset_1 @ X38 @ X39 @ X37 )
        = ( k2_relat_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('37',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('39',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('40',plain,(
    ! [X26: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('41',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ k1_xboole_0 @ X2 ) @ k1_xboole_0 )
      | ~ ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['33','38','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( sk_B = k1_xboole_0 )
      | ( r2_hidden @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','42'])).

thf('44',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ k1_xboole_0 @ ( sk_C @ X0 @ ( k1_tarski @ sk_A ) ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','45'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('47',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X29 @ X30 )
      | ~ ( r1_tarski @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ ( k1_funct_1 @ k1_xboole_0 @ ( sk_C @ X0 @ ( k1_tarski @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('49',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('52',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ X23 @ ( k1_relat_1 @ X24 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X24 @ X23 ) )
        = X23 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ k1_xboole_0 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('55',plain,(
    ! [X25: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('56',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('58',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v4_relat_1 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('59',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('60',plain,(
    ! [X20: $i,X21: $i] :
      ( ( X20
        = ( k7_relat_1 @ X20 @ X21 ) )
      | ~ ( v4_relat_1 @ X20 @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k7_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['54','55'])).

thf('63',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k7_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference(demod,[status(thm)],['53','56','63','64'])).

thf('66',plain,
    ( k1_xboole_0
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['50','65'])).

thf('67',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('68',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k1_relat_1 @ X28 )
       != ( k1_tarski @ X27 ) )
      | ( ( k2_relat_1 @ X28 )
        = ( k1_tarski @ ( k1_funct_1 @ X28 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['54','55'])).

thf('71',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['39','40'])).

thf('72',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ( k1_xboole_0
        = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['69','70','71','72'])).

thf('74',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['66','73'])).

thf('75',plain,
    ( k1_xboole_0
    = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('77',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['28'])).

thf('78',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('79',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['28'])).

thf('80',plain,(
    k1_xboole_0
 != ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['76','77','78','79'])).

thf('81',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['75','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pVkwU7hyLe
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:53:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.36/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.56  % Solved by: fo/fo7.sh
% 0.36/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.56  % done 193 iterations in 0.090s
% 0.36/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.56  % SZS output start Refutation
% 0.36/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.56  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.36/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.36/0.56  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.36/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.56  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.36/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.56  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.36/0.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.36/0.56  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.36/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.36/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.36/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.56  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.36/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.56  thf(d3_tarski, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( r1_tarski @ A @ B ) <=>
% 0.36/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.36/0.56  thf('0', plain,
% 0.36/0.56      (![X1 : $i, X3 : $i]:
% 0.36/0.56         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.36/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.36/0.56  thf(t62_funct_2, conjecture,
% 0.36/0.56    (![A:$i,B:$i,C:$i]:
% 0.36/0.56     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.36/0.56         ( m1_subset_1 @
% 0.36/0.56           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.36/0.56       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.36/0.56         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.36/0.56           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.36/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.56    (~( ![A:$i,B:$i,C:$i]:
% 0.36/0.56        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.36/0.56            ( m1_subset_1 @
% 0.36/0.56              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.36/0.56          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.36/0.56            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.36/0.56              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 0.36/0.56    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 0.36/0.56  thf('1', plain, ((v1_funct_2 @ sk_C_1 @ (k1_tarski @ sk_A) @ sk_B)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('2', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_C_1 @ 
% 0.36/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(cc2_relset_1, axiom,
% 0.36/0.56    (![A:$i,B:$i,C:$i]:
% 0.36/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.56       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.36/0.56  thf('3', plain,
% 0.36/0.56      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.36/0.56         ((v4_relat_1 @ X34 @ X35)
% 0.36/0.56          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.36/0.56      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.36/0.56  thf('4', plain, ((v4_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A))),
% 0.36/0.56      inference('sup-', [status(thm)], ['2', '3'])).
% 0.36/0.56  thf(d18_relat_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( v1_relat_1 @ B ) =>
% 0.36/0.56       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.36/0.56  thf('5', plain,
% 0.36/0.56      (![X18 : $i, X19 : $i]:
% 0.36/0.56         (~ (v4_relat_1 @ X18 @ X19)
% 0.36/0.56          | (r1_tarski @ (k1_relat_1 @ X18) @ X19)
% 0.36/0.56          | ~ (v1_relat_1 @ X18))),
% 0.36/0.56      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.36/0.56  thf('6', plain,
% 0.36/0.56      ((~ (v1_relat_1 @ sk_C_1)
% 0.36/0.56        | (r1_tarski @ (k1_relat_1 @ sk_C_1) @ (k1_tarski @ sk_A)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['4', '5'])).
% 0.36/0.56  thf('7', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_C_1 @ 
% 0.36/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(cc1_relset_1, axiom,
% 0.36/0.56    (![A:$i,B:$i,C:$i]:
% 0.36/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.56       ( v1_relat_1 @ C ) ))).
% 0.36/0.56  thf('8', plain,
% 0.36/0.56      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.36/0.56         ((v1_relat_1 @ X31)
% 0.36/0.56          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.36/0.56      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.36/0.56  thf('9', plain, ((v1_relat_1 @ sk_C_1)),
% 0.36/0.56      inference('sup-', [status(thm)], ['7', '8'])).
% 0.36/0.56  thf('10', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ (k1_tarski @ sk_A))),
% 0.36/0.56      inference('demod', [status(thm)], ['6', '9'])).
% 0.36/0.56  thf(l3_zfmisc_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.36/0.56       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.36/0.56  thf('11', plain,
% 0.36/0.56      (![X11 : $i, X12 : $i]:
% 0.36/0.56         (((X12) = (k1_tarski @ X11))
% 0.36/0.56          | ((X12) = (k1_xboole_0))
% 0.36/0.56          | ~ (r1_tarski @ X12 @ (k1_tarski @ X11)))),
% 0.36/0.56      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.36/0.56  thf('12', plain,
% 0.36/0.56      ((((k1_relat_1 @ sk_C_1) = (k1_xboole_0))
% 0.36/0.56        | ((k1_relat_1 @ sk_C_1) = (k1_tarski @ sk_A)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['10', '11'])).
% 0.36/0.56  thf(t14_funct_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.36/0.56       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.36/0.56         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.36/0.56  thf('13', plain,
% 0.36/0.56      (![X27 : $i, X28 : $i]:
% 0.36/0.56         (((k1_relat_1 @ X28) != (k1_tarski @ X27))
% 0.36/0.56          | ((k2_relat_1 @ X28) = (k1_tarski @ (k1_funct_1 @ X28 @ X27)))
% 0.36/0.56          | ~ (v1_funct_1 @ X28)
% 0.36/0.56          | ~ (v1_relat_1 @ X28))),
% 0.36/0.56      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.36/0.56  thf('14', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_C_1))
% 0.36/0.56          | ((k1_relat_1 @ sk_C_1) = (k1_xboole_0))
% 0.36/0.56          | ~ (v1_relat_1 @ X0)
% 0.36/0.56          | ~ (v1_funct_1 @ X0)
% 0.36/0.56          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.36/0.56      inference('sup-', [status(thm)], ['12', '13'])).
% 0.36/0.56  thf('15', plain,
% 0.36/0.56      ((((k2_relat_1 @ sk_C_1) = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))
% 0.36/0.56        | ~ (v1_funct_1 @ sk_C_1)
% 0.36/0.56        | ~ (v1_relat_1 @ sk_C_1)
% 0.36/0.56        | ((k1_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 0.36/0.56      inference('eq_res', [status(thm)], ['14'])).
% 0.36/0.56  thf('16', plain, ((v1_funct_1 @ sk_C_1)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('17', plain, ((v1_relat_1 @ sk_C_1)),
% 0.36/0.56      inference('sup-', [status(thm)], ['7', '8'])).
% 0.36/0.56  thf('18', plain,
% 0.36/0.56      ((((k2_relat_1 @ sk_C_1) = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))
% 0.36/0.56        | ((k1_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 0.36/0.56      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.36/0.56  thf('19', plain,
% 0.36/0.56      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1)
% 0.36/0.56         != (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('20', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_C_1 @ 
% 0.36/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(redefinition_k2_relset_1, axiom,
% 0.36/0.56    (![A:$i,B:$i,C:$i]:
% 0.36/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.56       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.36/0.56  thf('21', plain,
% 0.36/0.56      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.36/0.56         (((k2_relset_1 @ X38 @ X39 @ X37) = (k2_relat_1 @ X37))
% 0.36/0.56          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 0.36/0.56      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.36/0.56  thf('22', plain,
% 0.36/0.56      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1)
% 0.36/0.56         = (k2_relat_1 @ sk_C_1))),
% 0.36/0.56      inference('sup-', [status(thm)], ['20', '21'])).
% 0.36/0.56  thf('23', plain,
% 0.36/0.56      (((k2_relat_1 @ sk_C_1) != (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.36/0.56      inference('demod', [status(thm)], ['19', '22'])).
% 0.36/0.56  thf('24', plain, (((k1_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 0.36/0.56      inference('simplify_reflect-', [status(thm)], ['18', '23'])).
% 0.36/0.56  thf(t64_relat_1, axiom,
% 0.36/0.56    (![A:$i]:
% 0.36/0.56     ( ( v1_relat_1 @ A ) =>
% 0.36/0.56       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.36/0.56           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.36/0.56         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.36/0.56  thf('25', plain,
% 0.36/0.56      (![X22 : $i]:
% 0.36/0.56         (((k1_relat_1 @ X22) != (k1_xboole_0))
% 0.36/0.56          | ((X22) = (k1_xboole_0))
% 0.36/0.56          | ~ (v1_relat_1 @ X22))),
% 0.36/0.56      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.36/0.56  thf('26', plain,
% 0.36/0.56      ((((k1_xboole_0) != (k1_xboole_0))
% 0.36/0.56        | ~ (v1_relat_1 @ sk_C_1)
% 0.36/0.56        | ((sk_C_1) = (k1_xboole_0)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['24', '25'])).
% 0.36/0.56  thf('27', plain, ((v1_relat_1 @ sk_C_1)),
% 0.36/0.56      inference('sup-', [status(thm)], ['7', '8'])).
% 0.36/0.56  thf('28', plain,
% 0.36/0.56      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C_1) = (k1_xboole_0)))),
% 0.36/0.56      inference('demod', [status(thm)], ['26', '27'])).
% 0.36/0.56  thf('29', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.36/0.56      inference('simplify', [status(thm)], ['28'])).
% 0.36/0.56  thf('30', plain, ((v1_funct_2 @ k1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)),
% 0.36/0.56      inference('demod', [status(thm)], ['1', '29'])).
% 0.36/0.56  thf(t4_subset_1, axiom,
% 0.36/0.56    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.36/0.56  thf('31', plain,
% 0.36/0.56      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 0.36/0.56      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.36/0.56  thf(t6_funct_2, axiom,
% 0.36/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.56     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.36/0.56         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.56       ( ( r2_hidden @ C @ A ) =>
% 0.36/0.56         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.36/0.56           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.36/0.56  thf('32', plain,
% 0.36/0.56      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.36/0.56         (~ (r2_hidden @ X40 @ X41)
% 0.36/0.56          | ((X42) = (k1_xboole_0))
% 0.36/0.56          | ~ (v1_funct_1 @ X43)
% 0.36/0.56          | ~ (v1_funct_2 @ X43 @ X41 @ X42)
% 0.36/0.56          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.36/0.56          | (r2_hidden @ (k1_funct_1 @ X43 @ X40) @ 
% 0.36/0.56             (k2_relset_1 @ X41 @ X42 @ X43)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t6_funct_2])).
% 0.36/0.56  thf('33', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.56         ((r2_hidden @ (k1_funct_1 @ k1_xboole_0 @ X2) @ 
% 0.36/0.56           (k2_relset_1 @ X1 @ X0 @ k1_xboole_0))
% 0.36/0.56          | ~ (v1_funct_2 @ k1_xboole_0 @ X1 @ X0)
% 0.36/0.56          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.36/0.56          | ((X0) = (k1_xboole_0))
% 0.36/0.56          | ~ (r2_hidden @ X2 @ X1))),
% 0.36/0.56      inference('sup-', [status(thm)], ['31', '32'])).
% 0.36/0.56  thf('34', plain,
% 0.36/0.56      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 0.36/0.56      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.36/0.56  thf('35', plain,
% 0.36/0.56      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.36/0.56         (((k2_relset_1 @ X38 @ X39 @ X37) = (k2_relat_1 @ X37))
% 0.36/0.56          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 0.36/0.56      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.36/0.56  thf('36', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]:
% 0.36/0.56         ((k2_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 0.36/0.56      inference('sup-', [status(thm)], ['34', '35'])).
% 0.36/0.56  thf(t60_relat_1, axiom,
% 0.36/0.56    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.36/0.56     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.36/0.56  thf('37', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.56      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.36/0.56  thf('38', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]:
% 0.36/0.56         ((k2_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.56      inference('demod', [status(thm)], ['36', '37'])).
% 0.36/0.56  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.36/0.56  thf('39', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.56      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.36/0.56  thf(fc3_funct_1, axiom,
% 0.36/0.56    (![A:$i]:
% 0.36/0.56     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.36/0.56       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.36/0.56  thf('40', plain, (![X26 : $i]: (v1_funct_1 @ (k6_relat_1 @ X26))),
% 0.36/0.56      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.36/0.56  thf('41', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.36/0.56      inference('sup+', [status(thm)], ['39', '40'])).
% 0.36/0.56  thf('42', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.56         ((r2_hidden @ (k1_funct_1 @ k1_xboole_0 @ X2) @ k1_xboole_0)
% 0.36/0.56          | ~ (v1_funct_2 @ k1_xboole_0 @ X1 @ X0)
% 0.36/0.56          | ((X0) = (k1_xboole_0))
% 0.36/0.56          | ~ (r2_hidden @ X2 @ X1))),
% 0.36/0.56      inference('demod', [status(thm)], ['33', '38', '41'])).
% 0.36/0.56  thf('43', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.36/0.56          | ((sk_B) = (k1_xboole_0))
% 0.36/0.56          | (r2_hidden @ (k1_funct_1 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.36/0.56      inference('sup-', [status(thm)], ['30', '42'])).
% 0.36/0.56  thf('44', plain, (((sk_B) != (k1_xboole_0))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('45', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.36/0.56          | (r2_hidden @ (k1_funct_1 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.36/0.56      inference('simplify_reflect-', [status(thm)], ['43', '44'])).
% 0.36/0.56  thf('46', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((r1_tarski @ (k1_tarski @ sk_A) @ X0)
% 0.36/0.56          | (r2_hidden @ 
% 0.36/0.56             (k1_funct_1 @ k1_xboole_0 @ (sk_C @ X0 @ (k1_tarski @ sk_A))) @ 
% 0.36/0.56             k1_xboole_0))),
% 0.36/0.56      inference('sup-', [status(thm)], ['0', '45'])).
% 0.36/0.56  thf(t7_ordinal1, axiom,
% 0.36/0.56    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.36/0.56  thf('47', plain,
% 0.36/0.56      (![X29 : $i, X30 : $i]:
% 0.36/0.56         (~ (r2_hidden @ X29 @ X30) | ~ (r1_tarski @ X30 @ X29))),
% 0.36/0.56      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.36/0.56  thf('48', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         ((r1_tarski @ (k1_tarski @ sk_A) @ X0)
% 0.36/0.56          | ~ (r1_tarski @ k1_xboole_0 @ 
% 0.36/0.56               (k1_funct_1 @ k1_xboole_0 @ (sk_C @ X0 @ (k1_tarski @ sk_A)))))),
% 0.36/0.56      inference('sup-', [status(thm)], ['46', '47'])).
% 0.36/0.56  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.36/0.56  thf('49', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.36/0.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.36/0.56  thf('50', plain, (![X0 : $i]: (r1_tarski @ (k1_tarski @ sk_A) @ X0)),
% 0.36/0.56      inference('demod', [status(thm)], ['48', '49'])).
% 0.36/0.56  thf('51', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.56      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.36/0.56  thf(t91_relat_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( v1_relat_1 @ B ) =>
% 0.36/0.56       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.36/0.56         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.36/0.56  thf('52', plain,
% 0.36/0.56      (![X23 : $i, X24 : $i]:
% 0.36/0.56         (~ (r1_tarski @ X23 @ (k1_relat_1 @ X24))
% 0.36/0.56          | ((k1_relat_1 @ (k7_relat_1 @ X24 @ X23)) = (X23))
% 0.36/0.56          | ~ (v1_relat_1 @ X24))),
% 0.36/0.56      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.36/0.56  thf('53', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (~ (r1_tarski @ X0 @ k1_xboole_0)
% 0.36/0.56          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.36/0.56          | ((k1_relat_1 @ (k7_relat_1 @ k1_xboole_0 @ X0)) = (X0)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['51', '52'])).
% 0.36/0.56  thf('54', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.56      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.36/0.56  thf('55', plain, (![X25 : $i]: (v1_relat_1 @ (k6_relat_1 @ X25))),
% 0.36/0.56      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.36/0.56  thf('56', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.36/0.56      inference('sup+', [status(thm)], ['54', '55'])).
% 0.36/0.56  thf('57', plain,
% 0.36/0.56      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 0.36/0.56      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.36/0.56  thf('58', plain,
% 0.36/0.56      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.36/0.56         ((v4_relat_1 @ X34 @ X35)
% 0.36/0.56          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.36/0.56      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.36/0.56  thf('59', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 0.36/0.56      inference('sup-', [status(thm)], ['57', '58'])).
% 0.36/0.56  thf(t209_relat_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.36/0.56       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.36/0.56  thf('60', plain,
% 0.36/0.56      (![X20 : $i, X21 : $i]:
% 0.36/0.56         (((X20) = (k7_relat_1 @ X20 @ X21))
% 0.36/0.56          | ~ (v4_relat_1 @ X20 @ X21)
% 0.36/0.56          | ~ (v1_relat_1 @ X20))),
% 0.36/0.56      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.36/0.56  thf('61', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (~ (v1_relat_1 @ k1_xboole_0)
% 0.36/0.56          | ((k1_xboole_0) = (k7_relat_1 @ k1_xboole_0 @ X0)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['59', '60'])).
% 0.36/0.56  thf('62', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.36/0.56      inference('sup+', [status(thm)], ['54', '55'])).
% 0.36/0.56  thf('63', plain,
% 0.36/0.56      (![X0 : $i]: ((k1_xboole_0) = (k7_relat_1 @ k1_xboole_0 @ X0))),
% 0.36/0.56      inference('demod', [status(thm)], ['61', '62'])).
% 0.36/0.56  thf('64', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.56      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.36/0.56  thf('65', plain,
% 0.36/0.56      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((k1_xboole_0) = (X0)))),
% 0.36/0.56      inference('demod', [status(thm)], ['53', '56', '63', '64'])).
% 0.36/0.56  thf('66', plain, (((k1_xboole_0) = (k1_tarski @ sk_A))),
% 0.36/0.56      inference('sup-', [status(thm)], ['50', '65'])).
% 0.36/0.56  thf('67', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.56      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.36/0.56  thf('68', plain,
% 0.36/0.56      (![X27 : $i, X28 : $i]:
% 0.36/0.56         (((k1_relat_1 @ X28) != (k1_tarski @ X27))
% 0.36/0.56          | ((k2_relat_1 @ X28) = (k1_tarski @ (k1_funct_1 @ X28 @ X27)))
% 0.36/0.56          | ~ (v1_funct_1 @ X28)
% 0.36/0.56          | ~ (v1_relat_1 @ X28))),
% 0.36/0.56      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.36/0.56  thf('69', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.36/0.56          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.36/0.56          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.36/0.56          | ((k2_relat_1 @ k1_xboole_0)
% 0.36/0.56              = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0))))),
% 0.36/0.56      inference('sup-', [status(thm)], ['67', '68'])).
% 0.36/0.56  thf('70', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.36/0.56      inference('sup+', [status(thm)], ['54', '55'])).
% 0.36/0.56  thf('71', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.36/0.56      inference('sup+', [status(thm)], ['39', '40'])).
% 0.36/0.56  thf('72', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.56      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.36/0.56  thf('73', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.36/0.56          | ((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0))))),
% 0.36/0.56      inference('demod', [status(thm)], ['69', '70', '71', '72'])).
% 0.36/0.56  thf('74', plain,
% 0.36/0.56      ((((k1_xboole_0) != (k1_xboole_0))
% 0.36/0.56        | ((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A))))),
% 0.36/0.56      inference('sup-', [status(thm)], ['66', '73'])).
% 0.36/0.56  thf('75', plain,
% 0.36/0.56      (((k1_xboole_0) = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A)))),
% 0.36/0.56      inference('simplify', [status(thm)], ['74'])).
% 0.36/0.56  thf('76', plain,
% 0.36/0.56      (((k2_relat_1 @ sk_C_1) != (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.36/0.56      inference('demod', [status(thm)], ['19', '22'])).
% 0.36/0.56  thf('77', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.36/0.56      inference('simplify', [status(thm)], ['28'])).
% 0.36/0.56  thf('78', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.56      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.36/0.56  thf('79', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.36/0.56      inference('simplify', [status(thm)], ['28'])).
% 0.36/0.56  thf('80', plain,
% 0.36/0.56      (((k1_xboole_0) != (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A)))),
% 0.36/0.56      inference('demod', [status(thm)], ['76', '77', '78', '79'])).
% 0.36/0.56  thf('81', plain, ($false),
% 0.36/0.56      inference('simplify_reflect-', [status(thm)], ['75', '80'])).
% 0.36/0.56  
% 0.36/0.56  % SZS output end Refutation
% 0.36/0.56  
% 0.36/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
