%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Nh8Fk0zgPq

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:19 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 360 expanded)
%              Number of leaves         :   49 ( 130 expanded)
%              Depth                    :   13
%              Number of atoms          :  826 (3774 expanded)
%              Number of equality atoms :   63 ( 202 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('0',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ ( sk_B @ X8 ) @ X8 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

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

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t22_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ! [E: $i] :
                  ~ ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) )
      <=> ( ( k1_relset_1 @ B @ A @ C )
          = B ) ) ) )).

thf('4',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( ( k1_relset_1 @ X35 @ X36 @ X37 )
       != X35 )
      | ~ ( r2_hidden @ X38 @ X35 )
      | ( r2_hidden @ ( k4_tarski @ X38 @ ( sk_E @ X38 @ X37 ) ) @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[t22_relset_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ sk_C ) ) @ sk_C )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('7',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_2 @ X44 @ X42 @ X43 )
      | ( X42
        = ( k1_relset_1 @ X42 @ X43 @ X44 ) )
      | ~ ( zip_tseitin_1 @ X44 @ X43 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('8',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X40: $i,X41: $i] :
      ( ( zip_tseitin_0 @ X40 @ X41 )
      | ( X40 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
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

thf('11',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( zip_tseitin_0 @ X45 @ X46 )
      | ( zip_tseitin_1 @ X47 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('12',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    zip_tseitin_1 @ sk_C @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C ) ),
    inference(demod,[status(thm)],['8','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ sk_C ) ) @ sk_C )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['5','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ sk_C ) ) @ sk_C ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ ( sk_E @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ sk_C ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['2','18'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('20',plain,(
    ! [X7: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('21',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ ( sk_E @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ sk_C ) ) @ sk_C ),
    inference(clc,[status(thm)],['19','20'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('22',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X27 @ X28 )
      | ~ ( r1_tarski @ X28 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('23',plain,(
    ~ ( r1_tarski @ sk_C @ ( k4_tarski @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ ( sk_E @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('25',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v4_relat_1 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('26',plain,(
    v4_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X21: $i,X22: $i] :
      ( ( X21
        = ( k7_relat_1 @ X21 @ X22 ) )
      | ~ ( v4_relat_1 @ X21 @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('28',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('30',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v1_relat_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('31',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','31'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('33',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) )
        = ( k9_relat_1 @ X17 @ X18 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('34',plain,(
    ! [X23: $i] :
      ( ( ( k2_relat_1 @ X23 )
       != k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k9_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['29','30'])).

thf('38',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('39',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['29','30'])).

thf('40',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('41',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) )
        = ( k9_relat_1 @ X17 @ X18 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('42',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['29','30'])).

thf('44',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_C )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37','38','39','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v5_relat_1 @ X32 @ X34 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('48',plain,(
    v5_relat_1 @ sk_C @ sk_B_1 ),
    inference('sup-',[status(thm)],['46','47'])).

thf(t205_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf('49',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k11_relat_1 @ X19 @ X20 )
        = k1_xboole_0 )
      | ( r2_hidden @ X20 @ ( k1_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf(t172_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) )).

thf('50',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X24 @ ( k1_relat_1 @ X25 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X25 @ X24 ) @ X26 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v5_relat_1 @ X25 @ X26 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t172_funct_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v5_relat_1 @ X0 @ X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v5_relat_1 @ X0 @ X2 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( ( k11_relat_1 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['48','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['29','30'])).

thf('55',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ sk_C @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( k11_relat_1 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['56','57'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('59',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k11_relat_1 @ X15 @ X16 )
        = ( k9_relat_1 @ X15 @ ( k1_tarski @ X16 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('60',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('61',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k11_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['29','30'])).

thf('63',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k11_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['58','63'])).

thf('65',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( k1_xboole_0 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','64'])).

thf('66',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['65'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('68',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('69',plain,(
    $false ),
    inference(demod,[status(thm)],['23','66','67','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Nh8Fk0zgPq
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:22:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.69/0.91  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.69/0.91  % Solved by: fo/fo7.sh
% 0.69/0.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.69/0.91  % done 535 iterations in 0.446s
% 0.69/0.91  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.69/0.91  % SZS output start Refutation
% 0.69/0.91  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.69/0.91  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.69/0.91  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.69/0.91  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.69/0.91  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.69/0.91  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.69/0.91  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.69/0.91  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.69/0.91  thf(sk_B_type, type, sk_B: $i > $i).
% 0.69/0.91  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.69/0.91  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.69/0.91  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.69/0.91  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.69/0.91  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.69/0.91  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.69/0.91  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.69/0.91  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.69/0.91  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.69/0.91  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.69/0.91  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.69/0.91  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.69/0.91  thf(sk_E_type, type, sk_E: $i > $i > $i).
% 0.69/0.91  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.69/0.91  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.69/0.91  thf(sk_A_type, type, sk_A: $i).
% 0.69/0.91  thf(sk_C_type, type, sk_C: $i).
% 0.69/0.91  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.69/0.91  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.69/0.91  thf(existence_m1_subset_1, axiom,
% 0.69/0.91    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.69/0.91  thf('0', plain, (![X8 : $i]: (m1_subset_1 @ (sk_B @ X8) @ X8)),
% 0.69/0.91      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.69/0.91  thf(t2_subset, axiom,
% 0.69/0.91    (![A:$i,B:$i]:
% 0.69/0.91     ( ( m1_subset_1 @ A @ B ) =>
% 0.69/0.91       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.69/0.91  thf('1', plain,
% 0.69/0.91      (![X10 : $i, X11 : $i]:
% 0.69/0.91         ((r2_hidden @ X10 @ X11)
% 0.69/0.91          | (v1_xboole_0 @ X11)
% 0.69/0.91          | ~ (m1_subset_1 @ X10 @ X11))),
% 0.69/0.91      inference('cnf', [status(esa)], [t2_subset])).
% 0.69/0.91  thf('2', plain,
% 0.69/0.91      (![X0 : $i]: ((v1_xboole_0 @ X0) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.69/0.91      inference('sup-', [status(thm)], ['0', '1'])).
% 0.69/0.91  thf(t61_funct_2, conjecture,
% 0.69/0.91    (![A:$i,B:$i,C:$i]:
% 0.69/0.91     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.69/0.91         ( m1_subset_1 @
% 0.69/0.91           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.69/0.91       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.69/0.91         ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ))).
% 0.69/0.91  thf(zf_stmt_0, negated_conjecture,
% 0.69/0.91    (~( ![A:$i,B:$i,C:$i]:
% 0.69/0.91        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.69/0.91            ( m1_subset_1 @
% 0.69/0.91              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.69/0.91          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.69/0.91            ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )),
% 0.69/0.91    inference('cnf.neg', [status(esa)], [t61_funct_2])).
% 0.69/0.91  thf('3', plain,
% 0.69/0.91      ((m1_subset_1 @ sk_C @ 
% 0.69/0.91        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf(t22_relset_1, axiom,
% 0.69/0.91    (![A:$i,B:$i,C:$i]:
% 0.69/0.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.69/0.91       ( ( ![D:$i]:
% 0.69/0.91           ( ~( ( r2_hidden @ D @ B ) & 
% 0.69/0.91                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) ) ) ) ) ) <=>
% 0.69/0.91         ( ( k1_relset_1 @ B @ A @ C ) = ( B ) ) ) ))).
% 0.69/0.91  thf('4', plain,
% 0.69/0.91      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.69/0.91         (((k1_relset_1 @ X35 @ X36 @ X37) != (X35))
% 0.69/0.91          | ~ (r2_hidden @ X38 @ X35)
% 0.69/0.91          | (r2_hidden @ (k4_tarski @ X38 @ (sk_E @ X38 @ X37)) @ X37)
% 0.69/0.91          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.69/0.91      inference('cnf', [status(esa)], [t22_relset_1])).
% 0.69/0.91  thf('5', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         ((r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ sk_C)) @ sk_C)
% 0.69/0.91          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.69/0.91          | ((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 0.69/0.91              != (k1_tarski @ sk_A)))),
% 0.69/0.91      inference('sup-', [status(thm)], ['3', '4'])).
% 0.69/0.91  thf('6', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf(d1_funct_2, axiom,
% 0.69/0.91    (![A:$i,B:$i,C:$i]:
% 0.69/0.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.69/0.91       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.69/0.91           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.69/0.91             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.69/0.91         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.69/0.91           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.69/0.91             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.69/0.91  thf(zf_stmt_1, axiom,
% 0.69/0.91    (![C:$i,B:$i,A:$i]:
% 0.69/0.91     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.69/0.91       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.69/0.91  thf('7', plain,
% 0.69/0.91      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.69/0.91         (~ (v1_funct_2 @ X44 @ X42 @ X43)
% 0.69/0.91          | ((X42) = (k1_relset_1 @ X42 @ X43 @ X44))
% 0.69/0.91          | ~ (zip_tseitin_1 @ X44 @ X43 @ X42))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.69/0.91  thf('8', plain,
% 0.69/0.91      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.69/0.91        | ((k1_tarski @ sk_A)
% 0.69/0.91            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)))),
% 0.69/0.91      inference('sup-', [status(thm)], ['6', '7'])).
% 0.69/0.91  thf(zf_stmt_2, axiom,
% 0.69/0.91    (![B:$i,A:$i]:
% 0.69/0.91     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.69/0.91       ( zip_tseitin_0 @ B @ A ) ))).
% 0.69/0.91  thf('9', plain,
% 0.69/0.91      (![X40 : $i, X41 : $i]:
% 0.69/0.91         ((zip_tseitin_0 @ X40 @ X41) | ((X40) = (k1_xboole_0)))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.69/0.91  thf('10', plain,
% 0.69/0.91      ((m1_subset_1 @ sk_C @ 
% 0.69/0.91        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.69/0.91  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.69/0.91  thf(zf_stmt_5, axiom,
% 0.69/0.91    (![A:$i,B:$i,C:$i]:
% 0.69/0.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.69/0.91       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.69/0.91         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.69/0.91           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.69/0.91             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.69/0.91  thf('11', plain,
% 0.69/0.91      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.69/0.91         (~ (zip_tseitin_0 @ X45 @ X46)
% 0.69/0.91          | (zip_tseitin_1 @ X47 @ X45 @ X46)
% 0.69/0.91          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45))))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.69/0.91  thf('12', plain,
% 0.69/0.91      (((zip_tseitin_1 @ sk_C @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.69/0.91        | ~ (zip_tseitin_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.69/0.91      inference('sup-', [status(thm)], ['10', '11'])).
% 0.69/0.91  thf('13', plain,
% 0.69/0.91      ((((sk_B_1) = (k1_xboole_0))
% 0.69/0.91        | (zip_tseitin_1 @ sk_C @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.69/0.91      inference('sup-', [status(thm)], ['9', '12'])).
% 0.69/0.91  thf('14', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('15', plain, ((zip_tseitin_1 @ sk_C @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.69/0.91      inference('simplify_reflect-', [status(thm)], ['13', '14'])).
% 0.69/0.91  thf('16', plain,
% 0.69/0.91      (((k1_tarski @ sk_A) = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C))),
% 0.69/0.91      inference('demod', [status(thm)], ['8', '15'])).
% 0.69/0.91  thf('17', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         ((r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ sk_C)) @ sk_C)
% 0.69/0.91          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.69/0.91          | ((k1_tarski @ sk_A) != (k1_tarski @ sk_A)))),
% 0.69/0.91      inference('demod', [status(thm)], ['5', '16'])).
% 0.69/0.91  thf('18', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.69/0.91          | (r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ sk_C)) @ sk_C))),
% 0.69/0.91      inference('simplify', [status(thm)], ['17'])).
% 0.69/0.91  thf('19', plain,
% 0.69/0.91      (((v1_xboole_0 @ (k1_tarski @ sk_A))
% 0.69/0.91        | (r2_hidden @ 
% 0.69/0.91           (k4_tarski @ (sk_B @ (k1_tarski @ sk_A)) @ 
% 0.69/0.91            (sk_E @ (sk_B @ (k1_tarski @ sk_A)) @ sk_C)) @ 
% 0.69/0.91           sk_C))),
% 0.69/0.91      inference('sup-', [status(thm)], ['2', '18'])).
% 0.69/0.91  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.69/0.91  thf('20', plain, (![X7 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X7))),
% 0.69/0.91      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.69/0.91  thf('21', plain,
% 0.69/0.91      ((r2_hidden @ 
% 0.69/0.91        (k4_tarski @ (sk_B @ (k1_tarski @ sk_A)) @ 
% 0.69/0.91         (sk_E @ (sk_B @ (k1_tarski @ sk_A)) @ sk_C)) @ 
% 0.69/0.91        sk_C)),
% 0.69/0.91      inference('clc', [status(thm)], ['19', '20'])).
% 0.69/0.91  thf(t7_ordinal1, axiom,
% 0.69/0.91    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.69/0.91  thf('22', plain,
% 0.69/0.91      (![X27 : $i, X28 : $i]:
% 0.69/0.91         (~ (r2_hidden @ X27 @ X28) | ~ (r1_tarski @ X28 @ X27))),
% 0.69/0.91      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.69/0.91  thf('23', plain,
% 0.69/0.91      (~ (r1_tarski @ sk_C @ 
% 0.69/0.91          (k4_tarski @ (sk_B @ (k1_tarski @ sk_A)) @ 
% 0.69/0.91           (sk_E @ (sk_B @ (k1_tarski @ sk_A)) @ sk_C)))),
% 0.69/0.91      inference('sup-', [status(thm)], ['21', '22'])).
% 0.69/0.91  thf('24', plain,
% 0.69/0.91      ((m1_subset_1 @ sk_C @ 
% 0.69/0.91        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf(cc2_relset_1, axiom,
% 0.69/0.91    (![A:$i,B:$i,C:$i]:
% 0.69/0.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.69/0.91       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.69/0.91  thf('25', plain,
% 0.69/0.91      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.69/0.91         ((v4_relat_1 @ X32 @ X33)
% 0.69/0.91          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.69/0.91      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.69/0.91  thf('26', plain, ((v4_relat_1 @ sk_C @ (k1_tarski @ sk_A))),
% 0.69/0.91      inference('sup-', [status(thm)], ['24', '25'])).
% 0.69/0.91  thf(t209_relat_1, axiom,
% 0.69/0.91    (![A:$i,B:$i]:
% 0.69/0.91     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.69/0.91       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.69/0.91  thf('27', plain,
% 0.69/0.91      (![X21 : $i, X22 : $i]:
% 0.69/0.91         (((X21) = (k7_relat_1 @ X21 @ X22))
% 0.69/0.91          | ~ (v4_relat_1 @ X21 @ X22)
% 0.69/0.91          | ~ (v1_relat_1 @ X21))),
% 0.69/0.91      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.69/0.91  thf('28', plain,
% 0.69/0.91      ((~ (v1_relat_1 @ sk_C)
% 0.69/0.91        | ((sk_C) = (k7_relat_1 @ sk_C @ (k1_tarski @ sk_A))))),
% 0.69/0.91      inference('sup-', [status(thm)], ['26', '27'])).
% 0.69/0.91  thf('29', plain,
% 0.69/0.91      ((m1_subset_1 @ sk_C @ 
% 0.69/0.91        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf(cc1_relset_1, axiom,
% 0.69/0.91    (![A:$i,B:$i,C:$i]:
% 0.69/0.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.69/0.91       ( v1_relat_1 @ C ) ))).
% 0.69/0.91  thf('30', plain,
% 0.69/0.91      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.69/0.91         ((v1_relat_1 @ X29)
% 0.69/0.91          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.69/0.91      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.69/0.91  thf('31', plain, ((v1_relat_1 @ sk_C)),
% 0.69/0.91      inference('sup-', [status(thm)], ['29', '30'])).
% 0.69/0.91  thf('32', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_tarski @ sk_A)))),
% 0.69/0.91      inference('demod', [status(thm)], ['28', '31'])).
% 0.69/0.91  thf(t148_relat_1, axiom,
% 0.69/0.91    (![A:$i,B:$i]:
% 0.69/0.91     ( ( v1_relat_1 @ B ) =>
% 0.69/0.91       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.69/0.91  thf('33', plain,
% 0.69/0.91      (![X17 : $i, X18 : $i]:
% 0.69/0.91         (((k2_relat_1 @ (k7_relat_1 @ X17 @ X18)) = (k9_relat_1 @ X17 @ X18))
% 0.69/0.91          | ~ (v1_relat_1 @ X17))),
% 0.69/0.91      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.69/0.91  thf(t64_relat_1, axiom,
% 0.69/0.91    (![A:$i]:
% 0.69/0.91     ( ( v1_relat_1 @ A ) =>
% 0.69/0.91       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.69/0.91           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.69/0.91         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.69/0.91  thf('34', plain,
% 0.69/0.91      (![X23 : $i]:
% 0.69/0.91         (((k2_relat_1 @ X23) != (k1_xboole_0))
% 0.69/0.91          | ((X23) = (k1_xboole_0))
% 0.69/0.91          | ~ (v1_relat_1 @ X23))),
% 0.69/0.91      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.69/0.91  thf('35', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i]:
% 0.69/0.91         (((k9_relat_1 @ X1 @ X0) != (k1_xboole_0))
% 0.69/0.91          | ~ (v1_relat_1 @ X1)
% 0.69/0.91          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.69/0.91          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.69/0.91      inference('sup-', [status(thm)], ['33', '34'])).
% 0.69/0.91  thf('36', plain,
% 0.69/0.91      ((~ (v1_relat_1 @ sk_C)
% 0.69/0.91        | ((k7_relat_1 @ sk_C @ (k1_tarski @ sk_A)) = (k1_xboole_0))
% 0.69/0.91        | ~ (v1_relat_1 @ sk_C)
% 0.69/0.91        | ((k9_relat_1 @ sk_C @ (k1_tarski @ sk_A)) != (k1_xboole_0)))),
% 0.69/0.91      inference('sup-', [status(thm)], ['32', '35'])).
% 0.69/0.91  thf('37', plain, ((v1_relat_1 @ sk_C)),
% 0.69/0.91      inference('sup-', [status(thm)], ['29', '30'])).
% 0.69/0.91  thf('38', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_tarski @ sk_A)))),
% 0.69/0.91      inference('demod', [status(thm)], ['28', '31'])).
% 0.69/0.91  thf('39', plain, ((v1_relat_1 @ sk_C)),
% 0.69/0.91      inference('sup-', [status(thm)], ['29', '30'])).
% 0.69/0.91  thf('40', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_tarski @ sk_A)))),
% 0.69/0.91      inference('demod', [status(thm)], ['28', '31'])).
% 0.69/0.91  thf('41', plain,
% 0.69/0.91      (![X17 : $i, X18 : $i]:
% 0.69/0.91         (((k2_relat_1 @ (k7_relat_1 @ X17 @ X18)) = (k9_relat_1 @ X17 @ X18))
% 0.69/0.91          | ~ (v1_relat_1 @ X17))),
% 0.69/0.91      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.69/0.91  thf('42', plain,
% 0.69/0.91      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_tarski @ sk_A)))
% 0.69/0.91        | ~ (v1_relat_1 @ sk_C))),
% 0.69/0.91      inference('sup+', [status(thm)], ['40', '41'])).
% 0.69/0.91  thf('43', plain, ((v1_relat_1 @ sk_C)),
% 0.69/0.91      inference('sup-', [status(thm)], ['29', '30'])).
% 0.69/0.91  thf('44', plain,
% 0.69/0.91      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_tarski @ sk_A)))),
% 0.69/0.91      inference('demod', [status(thm)], ['42', '43'])).
% 0.69/0.91  thf('45', plain,
% 0.69/0.91      ((((sk_C) = (k1_xboole_0)) | ((k2_relat_1 @ sk_C) != (k1_xboole_0)))),
% 0.69/0.91      inference('demod', [status(thm)], ['36', '37', '38', '39', '44'])).
% 0.69/0.91  thf('46', plain,
% 0.69/0.91      ((m1_subset_1 @ sk_C @ 
% 0.69/0.91        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('47', plain,
% 0.69/0.91      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.69/0.91         ((v5_relat_1 @ X32 @ X34)
% 0.69/0.91          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.69/0.91      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.69/0.91  thf('48', plain, ((v5_relat_1 @ sk_C @ sk_B_1)),
% 0.69/0.91      inference('sup-', [status(thm)], ['46', '47'])).
% 0.69/0.91  thf(t205_relat_1, axiom,
% 0.69/0.91    (![A:$i,B:$i]:
% 0.69/0.91     ( ( v1_relat_1 @ B ) =>
% 0.69/0.91       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.69/0.91         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.69/0.91  thf('49', plain,
% 0.69/0.91      (![X19 : $i, X20 : $i]:
% 0.69/0.91         (((k11_relat_1 @ X19 @ X20) = (k1_xboole_0))
% 0.69/0.91          | (r2_hidden @ X20 @ (k1_relat_1 @ X19))
% 0.69/0.91          | ~ (v1_relat_1 @ X19))),
% 0.69/0.91      inference('cnf', [status(esa)], [t205_relat_1])).
% 0.69/0.91  thf(t172_funct_1, axiom,
% 0.69/0.91    (![A:$i,B:$i]:
% 0.69/0.91     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 0.69/0.91       ( ![C:$i]:
% 0.69/0.91         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.69/0.91           ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) ))).
% 0.69/0.91  thf('50', plain,
% 0.69/0.91      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.69/0.91         (~ (r2_hidden @ X24 @ (k1_relat_1 @ X25))
% 0.69/0.91          | (r2_hidden @ (k1_funct_1 @ X25 @ X24) @ X26)
% 0.69/0.91          | ~ (v1_funct_1 @ X25)
% 0.69/0.91          | ~ (v5_relat_1 @ X25 @ X26)
% 0.69/0.91          | ~ (v1_relat_1 @ X25))),
% 0.69/0.91      inference('cnf', [status(esa)], [t172_funct_1])).
% 0.69/0.91  thf('51', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.91         (~ (v1_relat_1 @ X0)
% 0.69/0.91          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.69/0.91          | ~ (v1_relat_1 @ X0)
% 0.69/0.91          | ~ (v5_relat_1 @ X0 @ X2)
% 0.69/0.91          | ~ (v1_funct_1 @ X0)
% 0.69/0.91          | (r2_hidden @ (k1_funct_1 @ X0 @ X1) @ X2))),
% 0.69/0.91      inference('sup-', [status(thm)], ['49', '50'])).
% 0.69/0.91  thf('52', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.91         ((r2_hidden @ (k1_funct_1 @ X0 @ X1) @ X2)
% 0.69/0.91          | ~ (v1_funct_1 @ X0)
% 0.69/0.91          | ~ (v5_relat_1 @ X0 @ X2)
% 0.69/0.91          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.69/0.91          | ~ (v1_relat_1 @ X0))),
% 0.69/0.91      inference('simplify', [status(thm)], ['51'])).
% 0.69/0.91  thf('53', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         (~ (v1_relat_1 @ sk_C)
% 0.69/0.91          | ((k11_relat_1 @ sk_C @ X0) = (k1_xboole_0))
% 0.69/0.91          | ~ (v1_funct_1 @ sk_C)
% 0.69/0.91          | (r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_1))),
% 0.69/0.91      inference('sup-', [status(thm)], ['48', '52'])).
% 0.69/0.91  thf('54', plain, ((v1_relat_1 @ sk_C)),
% 0.69/0.91      inference('sup-', [status(thm)], ['29', '30'])).
% 0.69/0.91  thf('55', plain, ((v1_funct_1 @ sk_C)),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('56', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         (((k11_relat_1 @ sk_C @ X0) = (k1_xboole_0))
% 0.69/0.91          | (r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_1))),
% 0.69/0.91      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.69/0.91  thf('57', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B_1)),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('58', plain, (((k11_relat_1 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.69/0.91      inference('sup-', [status(thm)], ['56', '57'])).
% 0.69/0.91  thf(d16_relat_1, axiom,
% 0.69/0.91    (![A:$i]:
% 0.69/0.91     ( ( v1_relat_1 @ A ) =>
% 0.69/0.91       ( ![B:$i]:
% 0.69/0.91         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.69/0.91  thf('59', plain,
% 0.69/0.91      (![X15 : $i, X16 : $i]:
% 0.69/0.91         (((k11_relat_1 @ X15 @ X16) = (k9_relat_1 @ X15 @ (k1_tarski @ X16)))
% 0.69/0.91          | ~ (v1_relat_1 @ X15))),
% 0.69/0.91      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.69/0.91  thf('60', plain,
% 0.69/0.91      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_tarski @ sk_A)))),
% 0.69/0.91      inference('demod', [status(thm)], ['42', '43'])).
% 0.69/0.91  thf('61', plain,
% 0.69/0.91      ((((k2_relat_1 @ sk_C) = (k11_relat_1 @ sk_C @ sk_A))
% 0.69/0.91        | ~ (v1_relat_1 @ sk_C))),
% 0.69/0.91      inference('sup+', [status(thm)], ['59', '60'])).
% 0.69/0.91  thf('62', plain, ((v1_relat_1 @ sk_C)),
% 0.69/0.91      inference('sup-', [status(thm)], ['29', '30'])).
% 0.69/0.91  thf('63', plain, (((k2_relat_1 @ sk_C) = (k11_relat_1 @ sk_C @ sk_A))),
% 0.69/0.91      inference('demod', [status(thm)], ['61', '62'])).
% 0.69/0.91  thf('64', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.69/0.91      inference('sup+', [status(thm)], ['58', '63'])).
% 0.69/0.91  thf('65', plain,
% 0.69/0.91      ((((sk_C) = (k1_xboole_0)) | ((k1_xboole_0) != (k1_xboole_0)))),
% 0.69/0.91      inference('demod', [status(thm)], ['45', '64'])).
% 0.69/0.91  thf('66', plain, (((sk_C) = (k1_xboole_0))),
% 0.69/0.91      inference('simplify', [status(thm)], ['65'])).
% 0.69/0.91  thf('67', plain, (((sk_C) = (k1_xboole_0))),
% 0.69/0.91      inference('simplify', [status(thm)], ['65'])).
% 0.69/0.91  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.69/0.91  thf('68', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.69/0.91      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.69/0.91  thf('69', plain, ($false),
% 0.69/0.91      inference('demod', [status(thm)], ['23', '66', '67', '68'])).
% 0.69/0.91  
% 0.69/0.91  % SZS output end Refutation
% 0.69/0.91  
% 0.69/0.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
