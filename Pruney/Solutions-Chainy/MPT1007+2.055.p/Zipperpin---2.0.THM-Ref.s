%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OLSxITOyr3

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:23 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 206 expanded)
%              Number of leaves         :   44 (  81 expanded)
%              Depth                    :   22
%              Number of atoms          :  734 (2155 expanded)
%              Number of equality atoms :   57 ( 126 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(t6_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i,G: $i] :
                  ( ( ( r2_hidden @ C @ D )
                    & ( r2_hidden @ D @ E )
                    & ( r2_hidden @ E @ F )
                    & ( r2_hidden @ F @ G )
                    & ( r2_hidden @ G @ B ) )
                 => ( r1_xboole_0 @ C @ A ) ) ) ) )).

thf('0',plain,(
    ! [X42: $i] :
      ( ( X42 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X42 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

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
    v1_funct_2 @ sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t56_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ! [B: $i,C: $i] :
            ~ ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
       => ( A = k1_xboole_0 ) ) ) )).

thf('2',plain,(
    ! [X22: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ X22 ) @ ( sk_C @ X22 ) ) @ X22 )
      | ( X22 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t56_relat_1])).

thf('3',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('4',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ( r2_hidden @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_C_1 ) @ ( sk_C @ sk_C_1 ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
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

thf('10',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_C_1 ) @ ( sk_C @ sk_C_1 ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['6','9'])).

thf(t128_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) )
    <=> ( ( A = C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('11',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X9 = X8 )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X8 ) @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t128_zfmisc_1])).

thf('12',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( sk_B @ sk_C_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X22: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ X22 ) @ ( sk_C @ X22 ) ) @ X22 )
      | ( X22 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t56_relat_1])).

thf('14',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_C @ sk_C_1 ) ) @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('16',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_C @ sk_C_1 ) ) @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_C @ sk_C_1 ) ) @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('18',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X26 @ X28 ) @ X27 )
      | ( X28
        = ( k1_funct_1 @ X27 @ X26 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('19',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( sk_C @ sk_C_1 )
      = ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('21',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( sk_C @ sk_C_1 )
      = ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ~ ( r2_hidden @ ( sk_C @ sk_C_1 ) @ sk_B_2 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_C_1 ) @ ( sk_C @ sk_C_1 ) ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('26',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X8 ) @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t128_zfmisc_1])).

thf('27',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C @ sk_C_1 ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['24','27'])).

thf('29',plain,(
    v1_funct_2 @ k1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_2 ),
    inference(demod,[status(thm)],['1','28'])).

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
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('30',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( v1_funct_2 @ X52 @ X50 @ X51 )
      | ( X50
        = ( k1_relset_1 @ X50 @ X51 @ X52 ) )
      | ~ ( zip_tseitin_1 @ X52 @ X51 @ X50 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('31',plain,
    ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ sk_B_2 @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('32',plain,(
    ! [X48: $i,X49: $i] :
      ( ( zip_tseitin_0 @ X48 @ X49 )
      | ( X48 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('33',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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

thf('34',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ~ ( zip_tseitin_0 @ X53 @ X54 )
      | ( zip_tseitin_1 @ X55 @ X53 @ X54 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X53 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('35',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_2 @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B_2 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( sk_B_2 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B_2 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    zip_tseitin_1 @ sk_C_1 @ sk_B_2 @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['36','37'])).

thf('39',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['24','27'])).

thf('40',plain,(
    zip_tseitin_1 @ k1_xboole_0 @ sk_B_2 @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_2 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','40'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('42',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t22_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ! [E: $i] :
                  ~ ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) )
      <=> ( ( k1_relset_1 @ B @ A @ C )
          = B ) ) ) )).

thf('43',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( ( k1_relset_1 @ X37 @ X38 @ X39 )
       != X37 )
      | ~ ( r2_hidden @ X40 @ X37 )
      | ( r2_hidden @ ( k4_tarski @ X40 @ ( sk_E @ X40 @ X39 ) ) @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[t22_relset_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_E @ X2 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
       != X1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( sk_E @ ( sk_B_1 @ ( k1_tarski @ sk_A ) ) @ k1_xboole_0 ) ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','46'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('49',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X13 ) @ X14 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( sk_E @ ( sk_B_1 @ ( k1_tarski @ sk_A ) ) @ k1_xboole_0 ) ) @ k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['47','50'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('52',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X29 @ X30 )
      | ~ ( r1_tarski @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('53',plain,(
    ~ ( r1_tarski @ k1_xboole_0 @ ( k4_tarski @ ( sk_B_1 @ ( k1_tarski @ sk_A ) ) @ ( sk_E @ ( sk_B_1 @ ( k1_tarski @ sk_A ) ) @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('54',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['53','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OLSxITOyr3
% 0.13/0.36  % Computer   : n003.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 17:07:57 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.75/0.98  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.75/0.98  % Solved by: fo/fo7.sh
% 0.75/0.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.98  % done 570 iterations in 0.511s
% 0.75/0.98  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.75/0.98  % SZS output start Refutation
% 0.75/0.98  thf(sk_C_type, type, sk_C: $i > $i).
% 0.75/0.98  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.98  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.75/0.98  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.75/0.98  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.75/0.98  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.75/0.98  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.75/0.98  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.75/0.98  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.75/0.98  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.75/0.98  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.75/0.98  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.75/0.98  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.75/0.98  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.75/0.98  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.75/0.98  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.75/0.98  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.75/0.98  thf(sk_B_type, type, sk_B: $i > $i).
% 0.75/0.98  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.75/0.98  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.75/0.98  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.75/0.98  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.75/0.98  thf(sk_E_type, type, sk_E: $i > $i > $i).
% 0.75/0.98  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.75/0.98  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.75/0.98  thf(t6_mcart_1, axiom,
% 0.75/0.98    (![A:$i]:
% 0.75/0.98     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.75/0.98          ( ![B:$i]:
% 0.75/0.98            ( ~( ( r2_hidden @ B @ A ) & 
% 0.75/0.98                 ( ![C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.75/0.98                   ( ( ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ E ) & 
% 0.75/0.98                       ( r2_hidden @ E @ F ) & ( r2_hidden @ F @ G ) & 
% 0.75/0.98                       ( r2_hidden @ G @ B ) ) =>
% 0.75/0.98                     ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 0.75/0.98  thf('0', plain,
% 0.75/0.98      (![X42 : $i]:
% 0.75/0.98         (((X42) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X42) @ X42))),
% 0.75/0.98      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.75/0.98  thf(t61_funct_2, conjecture,
% 0.75/0.98    (![A:$i,B:$i,C:$i]:
% 0.75/0.98     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.75/0.98         ( m1_subset_1 @
% 0.75/0.98           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.75/0.98       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.75/0.98         ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ))).
% 0.75/0.98  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.98    (~( ![A:$i,B:$i,C:$i]:
% 0.75/0.98        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.75/0.98            ( m1_subset_1 @
% 0.75/0.98              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.75/0.98          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.75/0.98            ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )),
% 0.75/0.98    inference('cnf.neg', [status(esa)], [t61_funct_2])).
% 0.75/0.98  thf('1', plain, ((v1_funct_2 @ sk_C_1 @ (k1_tarski @ sk_A) @ sk_B_2)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf(t56_relat_1, axiom,
% 0.75/0.98    (![A:$i]:
% 0.75/0.98     ( ( v1_relat_1 @ A ) =>
% 0.75/0.98       ( ( ![B:$i,C:$i]: ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) =>
% 0.75/0.98         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.75/0.98  thf('2', plain,
% 0.75/0.98      (![X22 : $i]:
% 0.75/0.98         ((r2_hidden @ (k4_tarski @ (sk_B @ X22) @ (sk_C @ X22)) @ X22)
% 0.75/0.98          | ((X22) = (k1_xboole_0))
% 0.75/0.98          | ~ (v1_relat_1 @ X22))),
% 0.75/0.98      inference('cnf', [status(esa)], [t56_relat_1])).
% 0.75/0.98  thf('3', plain,
% 0.75/0.98      ((m1_subset_1 @ sk_C_1 @ 
% 0.75/0.98        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf(l3_subset_1, axiom,
% 0.75/0.98    (![A:$i,B:$i]:
% 0.75/0.98     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.75/0.98       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.75/0.98  thf('4', plain,
% 0.75/0.98      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.75/0.98         (~ (r2_hidden @ X15 @ X16)
% 0.75/0.98          | (r2_hidden @ X15 @ X17)
% 0.75/0.98          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.75/0.98      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.75/0.98  thf('5', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2))
% 0.75/0.98          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.75/0.98      inference('sup-', [status(thm)], ['3', '4'])).
% 0.75/0.98  thf('6', plain,
% 0.75/0.98      ((~ (v1_relat_1 @ sk_C_1)
% 0.75/0.98        | ((sk_C_1) = (k1_xboole_0))
% 0.75/0.98        | (r2_hidden @ (k4_tarski @ (sk_B @ sk_C_1) @ (sk_C @ sk_C_1)) @ 
% 0.75/0.98           (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['2', '5'])).
% 0.75/0.98  thf('7', plain,
% 0.75/0.98      ((m1_subset_1 @ sk_C_1 @ 
% 0.75/0.98        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf(cc1_relset_1, axiom,
% 0.75/0.98    (![A:$i,B:$i,C:$i]:
% 0.75/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.98       ( v1_relat_1 @ C ) ))).
% 0.75/0.98  thf('8', plain,
% 0.75/0.98      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.75/0.98         ((v1_relat_1 @ X31)
% 0.75/0.98          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.75/0.98      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.75/0.98  thf('9', plain, ((v1_relat_1 @ sk_C_1)),
% 0.75/0.98      inference('sup-', [status(thm)], ['7', '8'])).
% 0.75/0.98  thf('10', plain,
% 0.75/0.98      ((((sk_C_1) = (k1_xboole_0))
% 0.75/0.98        | (r2_hidden @ (k4_tarski @ (sk_B @ sk_C_1) @ (sk_C @ sk_C_1)) @ 
% 0.75/0.98           (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.75/0.98      inference('demod', [status(thm)], ['6', '9'])).
% 0.75/0.98  thf(t128_zfmisc_1, axiom,
% 0.75/0.98    (![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.98     ( ( r2_hidden @
% 0.75/0.98         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 0.75/0.98       ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ))).
% 0.75/0.98  thf('11', plain,
% 0.75/0.98      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.75/0.98         (((X9) = (X8))
% 0.75/0.98          | ~ (r2_hidden @ (k4_tarski @ X9 @ X10) @ 
% 0.75/0.98               (k2_zfmisc_1 @ (k1_tarski @ X8) @ X11)))),
% 0.75/0.98      inference('cnf', [status(esa)], [t128_zfmisc_1])).
% 0.75/0.98  thf('12', plain, ((((sk_C_1) = (k1_xboole_0)) | ((sk_B @ sk_C_1) = (sk_A)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['10', '11'])).
% 0.75/0.98  thf('13', plain,
% 0.75/0.98      (![X22 : $i]:
% 0.75/0.98         ((r2_hidden @ (k4_tarski @ (sk_B @ X22) @ (sk_C @ X22)) @ X22)
% 0.75/0.98          | ((X22) = (k1_xboole_0))
% 0.75/0.98          | ~ (v1_relat_1 @ X22))),
% 0.75/0.98      inference('cnf', [status(esa)], [t56_relat_1])).
% 0.75/0.98  thf('14', plain,
% 0.75/0.98      (((r2_hidden @ (k4_tarski @ sk_A @ (sk_C @ sk_C_1)) @ sk_C_1)
% 0.75/0.98        | ((sk_C_1) = (k1_xboole_0))
% 0.75/0.98        | ~ (v1_relat_1 @ sk_C_1)
% 0.75/0.98        | ((sk_C_1) = (k1_xboole_0)))),
% 0.75/0.98      inference('sup+', [status(thm)], ['12', '13'])).
% 0.75/0.98  thf('15', plain, ((v1_relat_1 @ sk_C_1)),
% 0.75/0.98      inference('sup-', [status(thm)], ['7', '8'])).
% 0.75/0.98  thf('16', plain,
% 0.75/0.98      (((r2_hidden @ (k4_tarski @ sk_A @ (sk_C @ sk_C_1)) @ sk_C_1)
% 0.75/0.98        | ((sk_C_1) = (k1_xboole_0))
% 0.75/0.98        | ((sk_C_1) = (k1_xboole_0)))),
% 0.75/0.98      inference('demod', [status(thm)], ['14', '15'])).
% 0.75/0.98  thf('17', plain,
% 0.75/0.98      ((((sk_C_1) = (k1_xboole_0))
% 0.75/0.98        | (r2_hidden @ (k4_tarski @ sk_A @ (sk_C @ sk_C_1)) @ sk_C_1))),
% 0.75/0.98      inference('simplify', [status(thm)], ['16'])).
% 0.75/0.98  thf(t8_funct_1, axiom,
% 0.75/0.98    (![A:$i,B:$i,C:$i]:
% 0.75/0.98     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.75/0.98       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.75/0.98         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.75/0.98           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.75/0.98  thf('18', plain,
% 0.75/0.98      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.75/0.98         (~ (r2_hidden @ (k4_tarski @ X26 @ X28) @ X27)
% 0.75/0.98          | ((X28) = (k1_funct_1 @ X27 @ X26))
% 0.75/0.98          | ~ (v1_funct_1 @ X27)
% 0.75/0.98          | ~ (v1_relat_1 @ X27))),
% 0.75/0.98      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.75/0.98  thf('19', plain,
% 0.75/0.98      ((((sk_C_1) = (k1_xboole_0))
% 0.75/0.98        | ~ (v1_relat_1 @ sk_C_1)
% 0.75/0.98        | ~ (v1_funct_1 @ sk_C_1)
% 0.75/0.98        | ((sk_C @ sk_C_1) = (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['17', '18'])).
% 0.75/0.98  thf('20', plain, ((v1_relat_1 @ sk_C_1)),
% 0.75/0.98      inference('sup-', [status(thm)], ['7', '8'])).
% 0.75/0.98  thf('21', plain, ((v1_funct_1 @ sk_C_1)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('22', plain,
% 0.75/0.98      ((((sk_C_1) = (k1_xboole_0))
% 0.75/0.98        | ((sk_C @ sk_C_1) = (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.75/0.98      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.75/0.98  thf('23', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B_2)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('24', plain,
% 0.75/0.98      ((~ (r2_hidden @ (sk_C @ sk_C_1) @ sk_B_2) | ((sk_C_1) = (k1_xboole_0)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['22', '23'])).
% 0.75/0.98  thf('25', plain,
% 0.75/0.98      ((((sk_C_1) = (k1_xboole_0))
% 0.75/0.98        | (r2_hidden @ (k4_tarski @ (sk_B @ sk_C_1) @ (sk_C @ sk_C_1)) @ 
% 0.75/0.98           (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.75/0.98      inference('demod', [status(thm)], ['6', '9'])).
% 0.75/0.98  thf('26', plain,
% 0.75/0.98      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.75/0.98         ((r2_hidden @ X10 @ X11)
% 0.75/0.98          | ~ (r2_hidden @ (k4_tarski @ X9 @ X10) @ 
% 0.75/0.98               (k2_zfmisc_1 @ (k1_tarski @ X8) @ X11)))),
% 0.75/0.98      inference('cnf', [status(esa)], [t128_zfmisc_1])).
% 0.75/0.98  thf('27', plain,
% 0.75/0.98      ((((sk_C_1) = (k1_xboole_0)) | (r2_hidden @ (sk_C @ sk_C_1) @ sk_B_2))),
% 0.75/0.98      inference('sup-', [status(thm)], ['25', '26'])).
% 0.75/0.98  thf('28', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.75/0.98      inference('clc', [status(thm)], ['24', '27'])).
% 0.75/0.98  thf('29', plain, ((v1_funct_2 @ k1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_2)),
% 0.75/0.98      inference('demod', [status(thm)], ['1', '28'])).
% 0.75/0.98  thf(d1_funct_2, axiom,
% 0.75/0.98    (![A:$i,B:$i,C:$i]:
% 0.75/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.98       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.75/0.98           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.75/0.98             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.75/0.98         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.75/0.98           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.75/0.98             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.75/0.98  thf(zf_stmt_1, axiom,
% 0.75/0.98    (![C:$i,B:$i,A:$i]:
% 0.75/0.98     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.75/0.98       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.75/0.98  thf('30', plain,
% 0.75/0.98      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.75/0.98         (~ (v1_funct_2 @ X52 @ X50 @ X51)
% 0.75/0.98          | ((X50) = (k1_relset_1 @ X50 @ X51 @ X52))
% 0.75/0.98          | ~ (zip_tseitin_1 @ X52 @ X51 @ X50))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.75/0.98  thf('31', plain,
% 0.75/0.98      ((~ (zip_tseitin_1 @ k1_xboole_0 @ sk_B_2 @ (k1_tarski @ sk_A))
% 0.75/0.98        | ((k1_tarski @ sk_A)
% 0.75/0.98            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_2 @ k1_xboole_0)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['29', '30'])).
% 0.75/0.98  thf(zf_stmt_2, axiom,
% 0.75/0.98    (![B:$i,A:$i]:
% 0.75/0.98     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.75/0.98       ( zip_tseitin_0 @ B @ A ) ))).
% 0.75/0.98  thf('32', plain,
% 0.75/0.98      (![X48 : $i, X49 : $i]:
% 0.75/0.98         ((zip_tseitin_0 @ X48 @ X49) | ((X48) = (k1_xboole_0)))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.75/0.98  thf('33', plain,
% 0.75/0.98      ((m1_subset_1 @ sk_C_1 @ 
% 0.75/0.98        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_2)))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.75/0.98  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.75/0.98  thf(zf_stmt_5, axiom,
% 0.75/0.98    (![A:$i,B:$i,C:$i]:
% 0.75/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.98       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.75/0.98         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.75/0.98           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.75/0.98             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.75/0.98  thf('34', plain,
% 0.75/0.98      (![X53 : $i, X54 : $i, X55 : $i]:
% 0.75/0.98         (~ (zip_tseitin_0 @ X53 @ X54)
% 0.75/0.98          | (zip_tseitin_1 @ X55 @ X53 @ X54)
% 0.75/0.98          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X53))))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.75/0.98  thf('35', plain,
% 0.75/0.98      (((zip_tseitin_1 @ sk_C_1 @ sk_B_2 @ (k1_tarski @ sk_A))
% 0.75/0.98        | ~ (zip_tseitin_0 @ sk_B_2 @ (k1_tarski @ sk_A)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['33', '34'])).
% 0.75/0.98  thf('36', plain,
% 0.75/0.98      ((((sk_B_2) = (k1_xboole_0))
% 0.75/0.98        | (zip_tseitin_1 @ sk_C_1 @ sk_B_2 @ (k1_tarski @ sk_A)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['32', '35'])).
% 0.75/0.98  thf('37', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('38', plain, ((zip_tseitin_1 @ sk_C_1 @ sk_B_2 @ (k1_tarski @ sk_A))),
% 0.75/0.98      inference('simplify_reflect-', [status(thm)], ['36', '37'])).
% 0.75/0.98  thf('39', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.75/0.98      inference('clc', [status(thm)], ['24', '27'])).
% 0.75/0.98  thf('40', plain,
% 0.75/0.98      ((zip_tseitin_1 @ k1_xboole_0 @ sk_B_2 @ (k1_tarski @ sk_A))),
% 0.75/0.98      inference('demod', [status(thm)], ['38', '39'])).
% 0.75/0.98  thf('41', plain,
% 0.75/0.98      (((k1_tarski @ sk_A)
% 0.75/0.98         = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_2 @ k1_xboole_0))),
% 0.75/0.99      inference('demod', [status(thm)], ['31', '40'])).
% 0.75/0.99  thf(t4_subset_1, axiom,
% 0.75/0.99    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.75/0.99  thf('42', plain,
% 0.75/0.99      (![X18 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X18))),
% 0.75/0.99      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.75/0.99  thf(t22_relset_1, axiom,
% 0.75/0.99    (![A:$i,B:$i,C:$i]:
% 0.75/0.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.75/0.99       ( ( ![D:$i]:
% 0.75/0.99           ( ~( ( r2_hidden @ D @ B ) & 
% 0.75/0.99                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) ) ) ) ) ) <=>
% 0.75/0.99         ( ( k1_relset_1 @ B @ A @ C ) = ( B ) ) ) ))).
% 0.75/0.99  thf('43', plain,
% 0.75/0.99      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.75/0.99         (((k1_relset_1 @ X37 @ X38 @ X39) != (X37))
% 0.75/0.99          | ~ (r2_hidden @ X40 @ X37)
% 0.75/0.99          | (r2_hidden @ (k4_tarski @ X40 @ (sk_E @ X40 @ X39)) @ X39)
% 0.75/0.99          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 0.75/0.99      inference('cnf', [status(esa)], [t22_relset_1])).
% 0.75/0.99  thf('44', plain,
% 0.75/0.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.99         ((r2_hidden @ (k4_tarski @ X2 @ (sk_E @ X2 @ k1_xboole_0)) @ 
% 0.75/0.99           k1_xboole_0)
% 0.75/0.99          | ~ (r2_hidden @ X2 @ X1)
% 0.75/0.99          | ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) != (X1)))),
% 0.75/0.99      inference('sup-', [status(thm)], ['42', '43'])).
% 0.75/0.99  thf('45', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.75/0.99          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.75/0.99          | (r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ k1_xboole_0)) @ 
% 0.75/0.99             k1_xboole_0))),
% 0.75/0.99      inference('sup-', [status(thm)], ['41', '44'])).
% 0.75/0.99  thf('46', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         ((r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ k1_xboole_0)) @ 
% 0.75/0.99           k1_xboole_0)
% 0.75/0.99          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.75/0.99      inference('simplify', [status(thm)], ['45'])).
% 0.75/0.99  thf('47', plain,
% 0.75/0.99      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.75/0.99        | (r2_hidden @ 
% 0.75/0.99           (k4_tarski @ (sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.75/0.99            (sk_E @ (sk_B_1 @ (k1_tarski @ sk_A)) @ k1_xboole_0)) @ 
% 0.75/0.99           k1_xboole_0))),
% 0.75/0.99      inference('sup-', [status(thm)], ['0', '46'])).
% 0.75/0.99  thf(t1_boole, axiom,
% 0.75/0.99    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.75/0.99  thf('48', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.75/0.99      inference('cnf', [status(esa)], [t1_boole])).
% 0.75/0.99  thf(t49_zfmisc_1, axiom,
% 0.75/0.99    (![A:$i,B:$i]:
% 0.75/0.99     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.75/0.99  thf('49', plain,
% 0.75/0.99      (![X13 : $i, X14 : $i]:
% 0.75/0.99         ((k2_xboole_0 @ (k1_tarski @ X13) @ X14) != (k1_xboole_0))),
% 0.75/0.99      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.75/0.99  thf('50', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.75/0.99      inference('sup-', [status(thm)], ['48', '49'])).
% 0.75/0.99  thf('51', plain,
% 0.75/0.99      ((r2_hidden @ 
% 0.75/0.99        (k4_tarski @ (sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.75/0.99         (sk_E @ (sk_B_1 @ (k1_tarski @ sk_A)) @ k1_xboole_0)) @ 
% 0.75/0.99        k1_xboole_0)),
% 0.75/0.99      inference('simplify_reflect-', [status(thm)], ['47', '50'])).
% 0.75/0.99  thf(t7_ordinal1, axiom,
% 0.75/0.99    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.75/0.99  thf('52', plain,
% 0.75/0.99      (![X29 : $i, X30 : $i]:
% 0.75/0.99         (~ (r2_hidden @ X29 @ X30) | ~ (r1_tarski @ X30 @ X29))),
% 0.75/0.99      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.75/0.99  thf('53', plain,
% 0.75/0.99      (~ (r1_tarski @ k1_xboole_0 @ 
% 0.75/0.99          (k4_tarski @ (sk_B_1 @ (k1_tarski @ sk_A)) @ 
% 0.75/0.99           (sk_E @ (sk_B_1 @ (k1_tarski @ sk_A)) @ k1_xboole_0)))),
% 0.75/0.99      inference('sup-', [status(thm)], ['51', '52'])).
% 0.75/0.99  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.75/0.99  thf('54', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.75/0.99      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.75/0.99  thf('55', plain, ($false), inference('demod', [status(thm)], ['53', '54'])).
% 0.75/0.99  
% 0.75/0.99  % SZS output end Refutation
% 0.75/0.99  
% 0.83/0.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
