%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ILNMHHYS0J

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:34 EST 2020

% Result     : Theorem 54.49s
% Output     : Refutation 54.49s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 479 expanded)
%              Number of leaves         :   47 ( 160 expanded)
%              Depth                    :   25
%              Number of atoms          :  876 (5850 expanded)
%              Number of equality atoms :   86 ( 474 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf('2',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( v1_funct_2 @ X48 @ X46 @ X47 )
      | ( X46
        = ( k1_relset_1 @ X46 @ X47 @ X48 ) )
      | ~ ( zip_tseitin_1 @ X48 @ X47 @ X46 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X44: $i,X45: $i] :
      ( ( zip_tseitin_0 @ X44 @ X45 )
      | ( X44 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('5',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
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

thf('6',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( zip_tseitin_0 @ X49 @ X50 )
      | ( zip_tseitin_1 @ X51 @ X49 @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X49 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('7',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    zip_tseitin_1 @ sk_C_1 @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['3','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v4_relat_1 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('14',plain,(
    v4_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X21: $i,X22: $i] :
      ( ( X21
        = ( k7_relat_1 @ X21 @ X22 ) )
      | ~ ( v4_relat_1 @ X21 @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1
      = ( k7_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('18',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v1_relat_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('19',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( sk_C_1
    = ( k7_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','19'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('21',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X24 @ X25 ) ) @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('22',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_tarski @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('24',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('25',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X15
        = ( k1_tarski @ X14 ) )
      | ( X15 = k1_xboole_0 )
      | ~ ( r1_tarski @ X15 @ ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('26',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('27',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k1_relat_1 @ X27 )
       != ( k1_tarski @ X26 ) )
      | ( ( k2_relat_1 @ X27 )
        = ( k1_tarski @ ( k1_funct_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_C_1 ) )
      | ( ( k1_relat_1 @ sk_C_1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['28'])).

thf('30',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('32',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('35',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k2_relset_1 @ X37 @ X38 @ X36 )
        = ( k2_relat_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('36',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','36'])).

thf('38',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['32','37'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('39',plain,(
    ! [X23: $i] :
      ( ( ( k1_relat_1 @ X23 )
       != k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('40',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('42',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','43'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('45',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X17 ) ) ),
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

thf('46',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( ( k1_relset_1 @ X39 @ X40 @ X41 )
       != X39 )
      | ~ ( r2_hidden @ X42 @ X39 )
      | ( r2_hidden @ ( k4_tarski @ X42 @ ( sk_E @ X42 @ X41 ) ) @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[t22_relset_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_E @ X2 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
       != X1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ ( k1_tarski @ sk_A ) ) @ ( sk_E @ ( sk_C @ X0 @ ( k1_tarski @ sk_A ) ) @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','49'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('51',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X28 @ X29 )
      | ~ ( r1_tarski @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ ( k4_tarski @ ( sk_C @ X0 @ ( k1_tarski @ sk_A ) ) @ ( sk_E @ ( sk_C @ X0 @ ( k1_tarski @ sk_A ) ) @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('53',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('56',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['32','37'])).

thf('60',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k1_relat_1 @ X27 )
       != ( k1_tarski @ X26 ) )
      | ( ( k2_relat_1 @ X27 )
        = ( k1_tarski @ ( k1_funct_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( ( k2_relat_1 @ sk_C_1 )
        = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('63',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_C_1 )
        = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['42'])).

thf('66',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['42'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['58','67'])).

thf('69',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','36'])).

thf('71',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['42'])).

thf('72',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['42'])).

thf('73',plain,(
    ( k2_relat_1 @ k1_xboole_0 )
 != ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['69','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ILNMHHYS0J
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:37:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 54.49/54.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 54.49/54.71  % Solved by: fo/fo7.sh
% 54.49/54.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 54.49/54.71  % done 23359 iterations in 54.253s
% 54.49/54.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 54.49/54.71  % SZS output start Refutation
% 54.49/54.71  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 54.49/54.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 54.49/54.71  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 54.49/54.71  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 54.49/54.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 54.49/54.71  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 54.49/54.71  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 54.49/54.71  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 54.49/54.71  thf(sk_E_type, type, sk_E: $i > $i > $i).
% 54.49/54.71  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 54.49/54.71  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 54.49/54.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 54.49/54.71  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 54.49/54.71  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 54.49/54.71  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 54.49/54.71  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 54.49/54.71  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 54.49/54.71  thf(sk_A_type, type, sk_A: $i).
% 54.49/54.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 54.49/54.71  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 54.49/54.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 54.49/54.71  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 54.49/54.71  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 54.49/54.71  thf(sk_C_1_type, type, sk_C_1: $i).
% 54.49/54.71  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 54.49/54.71  thf(sk_B_type, type, sk_B: $i).
% 54.49/54.71  thf(d3_tarski, axiom,
% 54.49/54.71    (![A:$i,B:$i]:
% 54.49/54.71     ( ( r1_tarski @ A @ B ) <=>
% 54.49/54.71       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 54.49/54.71  thf('0', plain,
% 54.49/54.71      (![X1 : $i, X3 : $i]:
% 54.49/54.71         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 54.49/54.71      inference('cnf', [status(esa)], [d3_tarski])).
% 54.49/54.71  thf(t62_funct_2, conjecture,
% 54.49/54.71    (![A:$i,B:$i,C:$i]:
% 54.49/54.71     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 54.49/54.71         ( m1_subset_1 @
% 54.49/54.71           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 54.49/54.71       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 54.49/54.71         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 54.49/54.71           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 54.49/54.71  thf(zf_stmt_0, negated_conjecture,
% 54.49/54.71    (~( ![A:$i,B:$i,C:$i]:
% 54.49/54.71        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 54.49/54.71            ( m1_subset_1 @
% 54.49/54.71              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 54.49/54.71          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 54.49/54.71            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 54.49/54.71              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 54.49/54.71    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 54.49/54.71  thf('1', plain, ((v1_funct_2 @ sk_C_1 @ (k1_tarski @ sk_A) @ sk_B)),
% 54.49/54.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.49/54.71  thf(d1_funct_2, axiom,
% 54.49/54.71    (![A:$i,B:$i,C:$i]:
% 54.49/54.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 54.49/54.71       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 54.49/54.71           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 54.49/54.71             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 54.49/54.71         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 54.49/54.71           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 54.49/54.71             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 54.49/54.71  thf(zf_stmt_1, axiom,
% 54.49/54.71    (![C:$i,B:$i,A:$i]:
% 54.49/54.71     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 54.49/54.71       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 54.49/54.71  thf('2', plain,
% 54.49/54.71      (![X46 : $i, X47 : $i, X48 : $i]:
% 54.49/54.71         (~ (v1_funct_2 @ X48 @ X46 @ X47)
% 54.49/54.71          | ((X46) = (k1_relset_1 @ X46 @ X47 @ X48))
% 54.49/54.71          | ~ (zip_tseitin_1 @ X48 @ X47 @ X46))),
% 54.49/54.71      inference('cnf', [status(esa)], [zf_stmt_1])).
% 54.49/54.71  thf('3', plain,
% 54.49/54.71      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ (k1_tarski @ sk_A))
% 54.49/54.71        | ((k1_tarski @ sk_A)
% 54.49/54.71            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1)))),
% 54.49/54.71      inference('sup-', [status(thm)], ['1', '2'])).
% 54.49/54.71  thf(zf_stmt_2, axiom,
% 54.49/54.71    (![B:$i,A:$i]:
% 54.49/54.71     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 54.49/54.71       ( zip_tseitin_0 @ B @ A ) ))).
% 54.49/54.71  thf('4', plain,
% 54.49/54.71      (![X44 : $i, X45 : $i]:
% 54.49/54.71         ((zip_tseitin_0 @ X44 @ X45) | ((X44) = (k1_xboole_0)))),
% 54.49/54.71      inference('cnf', [status(esa)], [zf_stmt_2])).
% 54.49/54.71  thf('5', plain,
% 54.49/54.71      ((m1_subset_1 @ sk_C_1 @ 
% 54.49/54.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 54.49/54.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.49/54.71  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 54.49/54.71  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 54.49/54.71  thf(zf_stmt_5, axiom,
% 54.49/54.71    (![A:$i,B:$i,C:$i]:
% 54.49/54.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 54.49/54.71       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 54.49/54.71         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 54.49/54.71           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 54.49/54.71             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 54.49/54.71  thf('6', plain,
% 54.49/54.71      (![X49 : $i, X50 : $i, X51 : $i]:
% 54.49/54.71         (~ (zip_tseitin_0 @ X49 @ X50)
% 54.49/54.71          | (zip_tseitin_1 @ X51 @ X49 @ X50)
% 54.49/54.71          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X49))))),
% 54.49/54.71      inference('cnf', [status(esa)], [zf_stmt_5])).
% 54.49/54.71  thf('7', plain,
% 54.49/54.71      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ (k1_tarski @ sk_A))
% 54.49/54.71        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 54.49/54.71      inference('sup-', [status(thm)], ['5', '6'])).
% 54.49/54.71  thf('8', plain,
% 54.49/54.71      ((((sk_B) = (k1_xboole_0))
% 54.49/54.71        | (zip_tseitin_1 @ sk_C_1 @ sk_B @ (k1_tarski @ sk_A)))),
% 54.49/54.71      inference('sup-', [status(thm)], ['4', '7'])).
% 54.49/54.71  thf('9', plain, (((sk_B) != (k1_xboole_0))),
% 54.49/54.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.49/54.71  thf('10', plain, ((zip_tseitin_1 @ sk_C_1 @ sk_B @ (k1_tarski @ sk_A))),
% 54.49/54.71      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 54.49/54.71  thf('11', plain,
% 54.49/54.71      (((k1_tarski @ sk_A) = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1))),
% 54.49/54.71      inference('demod', [status(thm)], ['3', '10'])).
% 54.49/54.71  thf('12', plain,
% 54.49/54.71      ((m1_subset_1 @ sk_C_1 @ 
% 54.49/54.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 54.49/54.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.49/54.71  thf(cc2_relset_1, axiom,
% 54.49/54.71    (![A:$i,B:$i,C:$i]:
% 54.49/54.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 54.49/54.71       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 54.49/54.71  thf('13', plain,
% 54.49/54.71      (![X33 : $i, X34 : $i, X35 : $i]:
% 54.49/54.71         ((v4_relat_1 @ X33 @ X34)
% 54.49/54.71          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 54.49/54.71      inference('cnf', [status(esa)], [cc2_relset_1])).
% 54.49/54.71  thf('14', plain, ((v4_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A))),
% 54.49/54.71      inference('sup-', [status(thm)], ['12', '13'])).
% 54.49/54.71  thf(t209_relat_1, axiom,
% 54.49/54.71    (![A:$i,B:$i]:
% 54.49/54.71     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 54.49/54.71       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 54.49/54.71  thf('15', plain,
% 54.49/54.71      (![X21 : $i, X22 : $i]:
% 54.49/54.71         (((X21) = (k7_relat_1 @ X21 @ X22))
% 54.49/54.71          | ~ (v4_relat_1 @ X21 @ X22)
% 54.49/54.71          | ~ (v1_relat_1 @ X21))),
% 54.49/54.71      inference('cnf', [status(esa)], [t209_relat_1])).
% 54.49/54.71  thf('16', plain,
% 54.49/54.71      ((~ (v1_relat_1 @ sk_C_1)
% 54.49/54.71        | ((sk_C_1) = (k7_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A))))),
% 54.49/54.71      inference('sup-', [status(thm)], ['14', '15'])).
% 54.49/54.71  thf('17', plain,
% 54.49/54.71      ((m1_subset_1 @ sk_C_1 @ 
% 54.49/54.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 54.49/54.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.49/54.71  thf(cc1_relset_1, axiom,
% 54.49/54.71    (![A:$i,B:$i,C:$i]:
% 54.49/54.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 54.49/54.71       ( v1_relat_1 @ C ) ))).
% 54.49/54.71  thf('18', plain,
% 54.49/54.71      (![X30 : $i, X31 : $i, X32 : $i]:
% 54.49/54.71         ((v1_relat_1 @ X30)
% 54.49/54.71          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 54.49/54.71      inference('cnf', [status(esa)], [cc1_relset_1])).
% 54.49/54.71  thf('19', plain, ((v1_relat_1 @ sk_C_1)),
% 54.49/54.71      inference('sup-', [status(thm)], ['17', '18'])).
% 54.49/54.71  thf('20', plain, (((sk_C_1) = (k7_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A)))),
% 54.49/54.71      inference('demod', [status(thm)], ['16', '19'])).
% 54.49/54.71  thf(t87_relat_1, axiom,
% 54.49/54.71    (![A:$i,B:$i]:
% 54.49/54.71     ( ( v1_relat_1 @ B ) =>
% 54.49/54.71       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 54.49/54.71  thf('21', plain,
% 54.49/54.71      (![X24 : $i, X25 : $i]:
% 54.49/54.71         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X24 @ X25)) @ X25)
% 54.49/54.71          | ~ (v1_relat_1 @ X24))),
% 54.49/54.71      inference('cnf', [status(esa)], [t87_relat_1])).
% 54.49/54.71  thf('22', plain,
% 54.49/54.71      (((r1_tarski @ (k1_relat_1 @ sk_C_1) @ (k1_tarski @ sk_A))
% 54.49/54.71        | ~ (v1_relat_1 @ sk_C_1))),
% 54.49/54.71      inference('sup+', [status(thm)], ['20', '21'])).
% 54.49/54.71  thf('23', plain, ((v1_relat_1 @ sk_C_1)),
% 54.49/54.71      inference('sup-', [status(thm)], ['17', '18'])).
% 54.49/54.71  thf('24', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ (k1_tarski @ sk_A))),
% 54.49/54.71      inference('demod', [status(thm)], ['22', '23'])).
% 54.49/54.71  thf(l3_zfmisc_1, axiom,
% 54.49/54.71    (![A:$i,B:$i]:
% 54.49/54.71     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 54.49/54.71       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 54.49/54.71  thf('25', plain,
% 54.49/54.71      (![X14 : $i, X15 : $i]:
% 54.49/54.71         (((X15) = (k1_tarski @ X14))
% 54.49/54.71          | ((X15) = (k1_xboole_0))
% 54.49/54.71          | ~ (r1_tarski @ X15 @ (k1_tarski @ X14)))),
% 54.49/54.71      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 54.49/54.71  thf('26', plain,
% 54.49/54.71      ((((k1_relat_1 @ sk_C_1) = (k1_xboole_0))
% 54.49/54.71        | ((k1_relat_1 @ sk_C_1) = (k1_tarski @ sk_A)))),
% 54.49/54.71      inference('sup-', [status(thm)], ['24', '25'])).
% 54.49/54.71  thf(t14_funct_1, axiom,
% 54.49/54.71    (![A:$i,B:$i]:
% 54.49/54.71     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 54.49/54.71       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 54.49/54.71         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 54.49/54.71  thf('27', plain,
% 54.49/54.71      (![X26 : $i, X27 : $i]:
% 54.49/54.71         (((k1_relat_1 @ X27) != (k1_tarski @ X26))
% 54.49/54.71          | ((k2_relat_1 @ X27) = (k1_tarski @ (k1_funct_1 @ X27 @ X26)))
% 54.49/54.71          | ~ (v1_funct_1 @ X27)
% 54.49/54.71          | ~ (v1_relat_1 @ X27))),
% 54.49/54.71      inference('cnf', [status(esa)], [t14_funct_1])).
% 54.49/54.71  thf('28', plain,
% 54.49/54.71      (![X0 : $i]:
% 54.49/54.71         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_C_1))
% 54.49/54.71          | ((k1_relat_1 @ sk_C_1) = (k1_xboole_0))
% 54.49/54.71          | ~ (v1_relat_1 @ X0)
% 54.49/54.71          | ~ (v1_funct_1 @ X0)
% 54.49/54.71          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 54.49/54.71      inference('sup-', [status(thm)], ['26', '27'])).
% 54.49/54.71  thf('29', plain,
% 54.49/54.71      ((((k2_relat_1 @ sk_C_1) = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))
% 54.49/54.71        | ~ (v1_funct_1 @ sk_C_1)
% 54.49/54.71        | ~ (v1_relat_1 @ sk_C_1)
% 54.49/54.71        | ((k1_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 54.49/54.71      inference('eq_res', [status(thm)], ['28'])).
% 54.49/54.71  thf('30', plain, ((v1_funct_1 @ sk_C_1)),
% 54.49/54.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.49/54.71  thf('31', plain, ((v1_relat_1 @ sk_C_1)),
% 54.49/54.71      inference('sup-', [status(thm)], ['17', '18'])).
% 54.49/54.71  thf('32', plain,
% 54.49/54.71      ((((k2_relat_1 @ sk_C_1) = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))
% 54.49/54.71        | ((k1_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 54.49/54.71      inference('demod', [status(thm)], ['29', '30', '31'])).
% 54.49/54.71  thf('33', plain,
% 54.49/54.71      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1)
% 54.49/54.71         != (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 54.49/54.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.49/54.71  thf('34', plain,
% 54.49/54.71      ((m1_subset_1 @ sk_C_1 @ 
% 54.49/54.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 54.49/54.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.49/54.71  thf(redefinition_k2_relset_1, axiom,
% 54.49/54.71    (![A:$i,B:$i,C:$i]:
% 54.49/54.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 54.49/54.71       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 54.49/54.71  thf('35', plain,
% 54.49/54.71      (![X36 : $i, X37 : $i, X38 : $i]:
% 54.49/54.71         (((k2_relset_1 @ X37 @ X38 @ X36) = (k2_relat_1 @ X36))
% 54.49/54.71          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 54.49/54.71      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 54.49/54.71  thf('36', plain,
% 54.49/54.71      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1)
% 54.49/54.71         = (k2_relat_1 @ sk_C_1))),
% 54.49/54.71      inference('sup-', [status(thm)], ['34', '35'])).
% 54.49/54.71  thf('37', plain,
% 54.49/54.71      (((k2_relat_1 @ sk_C_1) != (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 54.49/54.71      inference('demod', [status(thm)], ['33', '36'])).
% 54.49/54.71  thf('38', plain, (((k1_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 54.49/54.71      inference('simplify_reflect-', [status(thm)], ['32', '37'])).
% 54.49/54.71  thf(t64_relat_1, axiom,
% 54.49/54.71    (![A:$i]:
% 54.49/54.71     ( ( v1_relat_1 @ A ) =>
% 54.49/54.71       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 54.49/54.71           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 54.49/54.71         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 54.49/54.71  thf('39', plain,
% 54.49/54.71      (![X23 : $i]:
% 54.49/54.71         (((k1_relat_1 @ X23) != (k1_xboole_0))
% 54.49/54.71          | ((X23) = (k1_xboole_0))
% 54.49/54.71          | ~ (v1_relat_1 @ X23))),
% 54.49/54.71      inference('cnf', [status(esa)], [t64_relat_1])).
% 54.49/54.71  thf('40', plain,
% 54.49/54.71      ((((k1_xboole_0) != (k1_xboole_0))
% 54.49/54.71        | ~ (v1_relat_1 @ sk_C_1)
% 54.49/54.71        | ((sk_C_1) = (k1_xboole_0)))),
% 54.49/54.71      inference('sup-', [status(thm)], ['38', '39'])).
% 54.49/54.71  thf('41', plain, ((v1_relat_1 @ sk_C_1)),
% 54.49/54.71      inference('sup-', [status(thm)], ['17', '18'])).
% 54.49/54.71  thf('42', plain,
% 54.49/54.71      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C_1) = (k1_xboole_0)))),
% 54.49/54.71      inference('demod', [status(thm)], ['40', '41'])).
% 54.49/54.71  thf('43', plain, (((sk_C_1) = (k1_xboole_0))),
% 54.49/54.71      inference('simplify', [status(thm)], ['42'])).
% 54.49/54.71  thf('44', plain,
% 54.49/54.71      (((k1_tarski @ sk_A)
% 54.49/54.71         = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ k1_xboole_0))),
% 54.49/54.71      inference('demod', [status(thm)], ['11', '43'])).
% 54.49/54.71  thf(t4_subset_1, axiom,
% 54.49/54.71    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 54.49/54.71  thf('45', plain,
% 54.49/54.71      (![X17 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X17))),
% 54.49/54.71      inference('cnf', [status(esa)], [t4_subset_1])).
% 54.49/54.71  thf(t22_relset_1, axiom,
% 54.49/54.71    (![A:$i,B:$i,C:$i]:
% 54.49/54.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 54.49/54.71       ( ( ![D:$i]:
% 54.49/54.71           ( ~( ( r2_hidden @ D @ B ) & 
% 54.49/54.71                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) ) ) ) ) ) <=>
% 54.49/54.71         ( ( k1_relset_1 @ B @ A @ C ) = ( B ) ) ) ))).
% 54.49/54.71  thf('46', plain,
% 54.49/54.71      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 54.49/54.71         (((k1_relset_1 @ X39 @ X40 @ X41) != (X39))
% 54.49/54.71          | ~ (r2_hidden @ X42 @ X39)
% 54.49/54.71          | (r2_hidden @ (k4_tarski @ X42 @ (sk_E @ X42 @ X41)) @ X41)
% 54.49/54.71          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40))))),
% 54.49/54.71      inference('cnf', [status(esa)], [t22_relset_1])).
% 54.49/54.71  thf('47', plain,
% 54.49/54.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 54.49/54.71         ((r2_hidden @ (k4_tarski @ X2 @ (sk_E @ X2 @ k1_xboole_0)) @ 
% 54.49/54.71           k1_xboole_0)
% 54.49/54.71          | ~ (r2_hidden @ X2 @ X1)
% 54.49/54.71          | ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) != (X1)))),
% 54.49/54.71      inference('sup-', [status(thm)], ['45', '46'])).
% 54.49/54.71  thf('48', plain,
% 54.49/54.71      (![X0 : $i]:
% 54.49/54.71         (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 54.49/54.71          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 54.49/54.71          | (r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ k1_xboole_0)) @ 
% 54.49/54.71             k1_xboole_0))),
% 54.49/54.71      inference('sup-', [status(thm)], ['44', '47'])).
% 54.49/54.71  thf('49', plain,
% 54.49/54.71      (![X0 : $i]:
% 54.49/54.71         ((r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ k1_xboole_0)) @ 
% 54.49/54.71           k1_xboole_0)
% 54.49/54.71          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 54.49/54.71      inference('simplify', [status(thm)], ['48'])).
% 54.49/54.71  thf('50', plain,
% 54.49/54.71      (![X0 : $i]:
% 54.49/54.71         ((r1_tarski @ (k1_tarski @ sk_A) @ X0)
% 54.49/54.71          | (r2_hidden @ 
% 54.49/54.71             (k4_tarski @ (sk_C @ X0 @ (k1_tarski @ sk_A)) @ 
% 54.49/54.71              (sk_E @ (sk_C @ X0 @ (k1_tarski @ sk_A)) @ k1_xboole_0)) @ 
% 54.49/54.71             k1_xboole_0))),
% 54.49/54.71      inference('sup-', [status(thm)], ['0', '49'])).
% 54.49/54.71  thf(t7_ordinal1, axiom,
% 54.49/54.71    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 54.49/54.71  thf('51', plain,
% 54.49/54.71      (![X28 : $i, X29 : $i]:
% 54.49/54.71         (~ (r2_hidden @ X28 @ X29) | ~ (r1_tarski @ X29 @ X28))),
% 54.49/54.71      inference('cnf', [status(esa)], [t7_ordinal1])).
% 54.49/54.71  thf('52', plain,
% 54.49/54.71      (![X0 : $i]:
% 54.49/54.71         ((r1_tarski @ (k1_tarski @ sk_A) @ X0)
% 54.49/54.71          | ~ (r1_tarski @ k1_xboole_0 @ 
% 54.49/54.71               (k4_tarski @ (sk_C @ X0 @ (k1_tarski @ sk_A)) @ 
% 54.49/54.71                (sk_E @ (sk_C @ X0 @ (k1_tarski @ sk_A)) @ k1_xboole_0))))),
% 54.49/54.71      inference('sup-', [status(thm)], ['50', '51'])).
% 54.49/54.71  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 54.49/54.71  thf('53', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 54.49/54.71      inference('cnf', [status(esa)], [t2_xboole_1])).
% 54.49/54.71  thf('54', plain, (![X0 : $i]: (r1_tarski @ (k1_tarski @ sk_A) @ X0)),
% 54.49/54.71      inference('demod', [status(thm)], ['52', '53'])).
% 54.49/54.71  thf('55', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 54.49/54.71      inference('cnf', [status(esa)], [t2_xboole_1])).
% 54.49/54.71  thf(d10_xboole_0, axiom,
% 54.49/54.71    (![A:$i,B:$i]:
% 54.49/54.71     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 54.49/54.71  thf('56', plain,
% 54.49/54.71      (![X4 : $i, X6 : $i]:
% 54.49/54.71         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 54.49/54.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 54.49/54.71  thf('57', plain,
% 54.49/54.71      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 54.49/54.71      inference('sup-', [status(thm)], ['55', '56'])).
% 54.49/54.71  thf('58', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 54.49/54.71      inference('sup-', [status(thm)], ['54', '57'])).
% 54.49/54.71  thf('59', plain, (((k1_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 54.49/54.71      inference('simplify_reflect-', [status(thm)], ['32', '37'])).
% 54.49/54.71  thf('60', plain,
% 54.49/54.71      (![X26 : $i, X27 : $i]:
% 54.49/54.71         (((k1_relat_1 @ X27) != (k1_tarski @ X26))
% 54.49/54.71          | ((k2_relat_1 @ X27) = (k1_tarski @ (k1_funct_1 @ X27 @ X26)))
% 54.49/54.71          | ~ (v1_funct_1 @ X27)
% 54.49/54.71          | ~ (v1_relat_1 @ X27))),
% 54.49/54.71      inference('cnf', [status(esa)], [t14_funct_1])).
% 54.49/54.71  thf('61', plain,
% 54.49/54.71      (![X0 : $i]:
% 54.49/54.71         (((k1_xboole_0) != (k1_tarski @ X0))
% 54.49/54.71          | ~ (v1_relat_1 @ sk_C_1)
% 54.49/54.71          | ~ (v1_funct_1 @ sk_C_1)
% 54.49/54.71          | ((k2_relat_1 @ sk_C_1) = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ X0))))),
% 54.49/54.71      inference('sup-', [status(thm)], ['59', '60'])).
% 54.49/54.71  thf('62', plain, ((v1_relat_1 @ sk_C_1)),
% 54.49/54.71      inference('sup-', [status(thm)], ['17', '18'])).
% 54.49/54.71  thf('63', plain, ((v1_funct_1 @ sk_C_1)),
% 54.49/54.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.49/54.71  thf('64', plain,
% 54.49/54.71      (![X0 : $i]:
% 54.49/54.71         (((k1_xboole_0) != (k1_tarski @ X0))
% 54.49/54.71          | ((k2_relat_1 @ sk_C_1) = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ X0))))),
% 54.49/54.71      inference('demod', [status(thm)], ['61', '62', '63'])).
% 54.49/54.71  thf('65', plain, (((sk_C_1) = (k1_xboole_0))),
% 54.49/54.71      inference('simplify', [status(thm)], ['42'])).
% 54.49/54.71  thf('66', plain, (((sk_C_1) = (k1_xboole_0))),
% 54.49/54.71      inference('simplify', [status(thm)], ['42'])).
% 54.49/54.71  thf('67', plain,
% 54.49/54.71      (![X0 : $i]:
% 54.49/54.71         (((k1_xboole_0) != (k1_tarski @ X0))
% 54.49/54.71          | ((k2_relat_1 @ k1_xboole_0)
% 54.49/54.71              = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0))))),
% 54.49/54.71      inference('demod', [status(thm)], ['64', '65', '66'])).
% 54.49/54.71  thf('68', plain,
% 54.49/54.71      ((((k1_xboole_0) != (k1_xboole_0))
% 54.49/54.71        | ((k2_relat_1 @ k1_xboole_0)
% 54.49/54.71            = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A))))),
% 54.49/54.71      inference('sup-', [status(thm)], ['58', '67'])).
% 54.49/54.71  thf('69', plain,
% 54.49/54.71      (((k2_relat_1 @ k1_xboole_0)
% 54.49/54.71         = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A)))),
% 54.49/54.71      inference('simplify', [status(thm)], ['68'])).
% 54.49/54.71  thf('70', plain,
% 54.49/54.71      (((k2_relat_1 @ sk_C_1) != (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 54.49/54.71      inference('demod', [status(thm)], ['33', '36'])).
% 54.49/54.71  thf('71', plain, (((sk_C_1) = (k1_xboole_0))),
% 54.49/54.71      inference('simplify', [status(thm)], ['42'])).
% 54.49/54.71  thf('72', plain, (((sk_C_1) = (k1_xboole_0))),
% 54.49/54.71      inference('simplify', [status(thm)], ['42'])).
% 54.49/54.71  thf('73', plain,
% 54.49/54.71      (((k2_relat_1 @ k1_xboole_0)
% 54.49/54.71         != (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A)))),
% 54.49/54.71      inference('demod', [status(thm)], ['70', '71', '72'])).
% 54.49/54.71  thf('74', plain, ($false),
% 54.49/54.71      inference('simplify_reflect-', [status(thm)], ['69', '73'])).
% 54.49/54.71  
% 54.49/54.71  % SZS output end Refutation
% 54.49/54.71  
% 54.49/54.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
