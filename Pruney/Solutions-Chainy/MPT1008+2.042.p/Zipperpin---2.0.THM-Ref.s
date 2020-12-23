%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xg2lqjZm0A

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:37 EST 2020

% Result     : Theorem 1.00s
% Output     : Refutation 1.00s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 413 expanded)
%              Number of leaves         :   45 ( 140 expanded)
%              Depth                    :   22
%              Number of atoms          :  815 (5154 expanded)
%              Number of equality atoms :   84 ( 428 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(t29_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) )).

thf('0',plain,(
    ! [X35: $i] :
      ( ( X35 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X35 ) @ X35 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

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

thf('2',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_funct_2 @ X43 @ X41 @ X42 )
      | ( X41
        = ( k1_relset_1 @ X41 @ X42 @ X43 ) )
      | ~ ( zip_tseitin_1 @ X43 @ X42 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X39: $i,X40: $i] :
      ( ( zip_tseitin_0 @ X39 @ X40 )
      | ( X39 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('5',plain,(
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

thf('6',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( zip_tseitin_0 @ X44 @ X45 )
      | ( zip_tseitin_1 @ X46 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('7',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    zip_tseitin_1 @ sk_C @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C ) ),
    inference(demod,[status(thm)],['3','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v4_relat_1 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('14',plain,(
    v4_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('15',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v4_relat_1 @ X14 @ X15 )
      | ( r1_tarski @ ( k1_relat_1 @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('18',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('19',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['16','19'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('21',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X8
        = ( k1_tarski @ X7 ) )
      | ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('22',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('23',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k1_relat_1 @ X18 )
       != ( k1_tarski @ X17 ) )
      | ( ( k2_relat_1 @ X18 )
        = ( k1_tarski @ ( k1_funct_1 @ X18 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_C ) )
      | ( ( k1_relat_1 @ sk_C )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['24'])).

thf('26',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('28',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('31',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k2_relset_1 @ X28 @ X29 @ X27 )
        = ( k2_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('32',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','32'])).

thf('34',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['28','33'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('35',plain,(
    ! [X16: $i] :
      ( ( ( k1_relat_1 @ X16 )
       != k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('36',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('38',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','39'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('41',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
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

thf('42',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( ( k1_relset_1 @ X30 @ X31 @ X32 )
       != X30 )
      | ~ ( r2_hidden @ X33 @ X30 )
      | ( r2_hidden @ ( k4_tarski @ X33 @ ( sk_E @ X33 @ X32 ) ) @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[t22_relset_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_E @ X2 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
       != X1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ ( sk_E @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ k1_xboole_0 ) ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','45'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('47',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( r1_tarski @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('48',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ~ ( r1_tarski @ k1_xboole_0 @ ( k4_tarski @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ ( sk_E @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('49',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('50',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['28','33'])).

thf('52',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k1_relat_1 @ X18 )
       != ( k1_tarski @ X17 ) )
      | ( ( k2_relat_1 @ X18 )
        = ( k1_tarski @ ( k1_funct_1 @ X18 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k2_relat_1 @ sk_C )
        = ( k1_tarski @ ( k1_funct_1 @ sk_C @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('55',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_C )
        = ( k1_tarski @ ( k1_funct_1 @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['38'])).

thf('58',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['38'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['50','59'])).

thf('61',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','32'])).

thf('63',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['38'])).

thf('64',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['38'])).

thf('65',plain,(
    ( k2_relat_1 @ k1_xboole_0 )
 != ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['61','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xg2lqjZm0A
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:13:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.00/1.18  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.00/1.18  % Solved by: fo/fo7.sh
% 1.00/1.18  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.00/1.18  % done 705 iterations in 0.717s
% 1.00/1.18  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.00/1.18  % SZS output start Refutation
% 1.00/1.18  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.00/1.18  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.00/1.18  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.00/1.18  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.00/1.18  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.00/1.18  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.00/1.18  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.00/1.18  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 1.00/1.18  thf(sk_E_type, type, sk_E: $i > $i > $i).
% 1.00/1.18  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.00/1.18  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.00/1.18  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.00/1.18  thf(sk_B_type, type, sk_B: $i > $i).
% 1.00/1.18  thf(sk_C_type, type, sk_C: $i).
% 1.00/1.18  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.00/1.18  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.00/1.18  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.00/1.18  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.00/1.18  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.00/1.18  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.00/1.18  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.00/1.18  thf(sk_A_type, type, sk_A: $i).
% 1.00/1.18  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.00/1.18  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.00/1.18  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.00/1.18  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.00/1.18  thf(t29_mcart_1, axiom,
% 1.00/1.18    (![A:$i]:
% 1.00/1.18     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.00/1.18          ( ![B:$i]:
% 1.00/1.18            ( ~( ( r2_hidden @ B @ A ) & 
% 1.00/1.18                 ( ![C:$i,D:$i,E:$i]:
% 1.00/1.18                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 1.00/1.18                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 1.00/1.18  thf('0', plain,
% 1.00/1.18      (![X35 : $i]:
% 1.00/1.18         (((X35) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X35) @ X35))),
% 1.00/1.18      inference('cnf', [status(esa)], [t29_mcart_1])).
% 1.00/1.18  thf(t62_funct_2, conjecture,
% 1.00/1.18    (![A:$i,B:$i,C:$i]:
% 1.00/1.18     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 1.00/1.18         ( m1_subset_1 @
% 1.00/1.18           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 1.00/1.18       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 1.00/1.18         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 1.00/1.18           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 1.00/1.18  thf(zf_stmt_0, negated_conjecture,
% 1.00/1.18    (~( ![A:$i,B:$i,C:$i]:
% 1.00/1.18        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 1.00/1.18            ( m1_subset_1 @
% 1.00/1.18              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 1.00/1.18          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 1.00/1.18            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 1.00/1.18              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 1.00/1.18    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 1.00/1.18  thf('1', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_1)),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf(d1_funct_2, axiom,
% 1.00/1.18    (![A:$i,B:$i,C:$i]:
% 1.00/1.18     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.00/1.18       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.00/1.18           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.00/1.18             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.00/1.18         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.00/1.18           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.00/1.18             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.00/1.18  thf(zf_stmt_1, axiom,
% 1.00/1.18    (![C:$i,B:$i,A:$i]:
% 1.00/1.18     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.00/1.18       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.00/1.18  thf('2', plain,
% 1.00/1.18      (![X41 : $i, X42 : $i, X43 : $i]:
% 1.00/1.18         (~ (v1_funct_2 @ X43 @ X41 @ X42)
% 1.00/1.18          | ((X41) = (k1_relset_1 @ X41 @ X42 @ X43))
% 1.00/1.18          | ~ (zip_tseitin_1 @ X43 @ X42 @ X41))),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.00/1.18  thf('3', plain,
% 1.00/1.18      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ (k1_tarski @ sk_A))
% 1.00/1.18        | ((k1_tarski @ sk_A)
% 1.00/1.18            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)))),
% 1.00/1.18      inference('sup-', [status(thm)], ['1', '2'])).
% 1.00/1.18  thf(zf_stmt_2, axiom,
% 1.00/1.18    (![B:$i,A:$i]:
% 1.00/1.18     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.00/1.18       ( zip_tseitin_0 @ B @ A ) ))).
% 1.00/1.18  thf('4', plain,
% 1.00/1.18      (![X39 : $i, X40 : $i]:
% 1.00/1.18         ((zip_tseitin_0 @ X39 @ X40) | ((X39) = (k1_xboole_0)))),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.00/1.18  thf('5', plain,
% 1.00/1.18      ((m1_subset_1 @ sk_C @ 
% 1.00/1.18        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.00/1.18  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.00/1.18  thf(zf_stmt_5, axiom,
% 1.00/1.18    (![A:$i,B:$i,C:$i]:
% 1.00/1.18     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.00/1.18       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.00/1.18         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.00/1.18           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.00/1.18             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.00/1.18  thf('6', plain,
% 1.00/1.18      (![X44 : $i, X45 : $i, X46 : $i]:
% 1.00/1.18         (~ (zip_tseitin_0 @ X44 @ X45)
% 1.00/1.18          | (zip_tseitin_1 @ X46 @ X44 @ X45)
% 1.00/1.18          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44))))),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.00/1.18  thf('7', plain,
% 1.00/1.18      (((zip_tseitin_1 @ sk_C @ sk_B_1 @ (k1_tarski @ sk_A))
% 1.00/1.18        | ~ (zip_tseitin_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 1.00/1.18      inference('sup-', [status(thm)], ['5', '6'])).
% 1.00/1.18  thf('8', plain,
% 1.00/1.18      ((((sk_B_1) = (k1_xboole_0))
% 1.00/1.18        | (zip_tseitin_1 @ sk_C @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 1.00/1.18      inference('sup-', [status(thm)], ['4', '7'])).
% 1.00/1.18  thf('9', plain, (((sk_B_1) != (k1_xboole_0))),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf('10', plain, ((zip_tseitin_1 @ sk_C @ sk_B_1 @ (k1_tarski @ sk_A))),
% 1.00/1.18      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 1.00/1.18  thf('11', plain,
% 1.00/1.18      (((k1_tarski @ sk_A) = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C))),
% 1.00/1.18      inference('demod', [status(thm)], ['3', '10'])).
% 1.00/1.18  thf('12', plain,
% 1.00/1.18      ((m1_subset_1 @ sk_C @ 
% 1.00/1.18        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf(cc2_relset_1, axiom,
% 1.00/1.18    (![A:$i,B:$i,C:$i]:
% 1.00/1.18     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.00/1.18       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.00/1.18  thf('13', plain,
% 1.00/1.18      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.00/1.18         ((v4_relat_1 @ X24 @ X25)
% 1.00/1.18          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 1.00/1.18      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.00/1.18  thf('14', plain, ((v4_relat_1 @ sk_C @ (k1_tarski @ sk_A))),
% 1.00/1.18      inference('sup-', [status(thm)], ['12', '13'])).
% 1.00/1.18  thf(d18_relat_1, axiom,
% 1.00/1.18    (![A:$i,B:$i]:
% 1.00/1.18     ( ( v1_relat_1 @ B ) =>
% 1.00/1.18       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.00/1.18  thf('15', plain,
% 1.00/1.18      (![X14 : $i, X15 : $i]:
% 1.00/1.18         (~ (v4_relat_1 @ X14 @ X15)
% 1.00/1.18          | (r1_tarski @ (k1_relat_1 @ X14) @ X15)
% 1.00/1.18          | ~ (v1_relat_1 @ X14))),
% 1.00/1.18      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.00/1.18  thf('16', plain,
% 1.00/1.18      ((~ (v1_relat_1 @ sk_C)
% 1.00/1.18        | (r1_tarski @ (k1_relat_1 @ sk_C) @ (k1_tarski @ sk_A)))),
% 1.00/1.18      inference('sup-', [status(thm)], ['14', '15'])).
% 1.00/1.18  thf('17', plain,
% 1.00/1.18      ((m1_subset_1 @ sk_C @ 
% 1.00/1.18        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf(cc1_relset_1, axiom,
% 1.00/1.18    (![A:$i,B:$i,C:$i]:
% 1.00/1.18     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.00/1.18       ( v1_relat_1 @ C ) ))).
% 1.00/1.18  thf('18', plain,
% 1.00/1.18      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.00/1.18         ((v1_relat_1 @ X21)
% 1.00/1.18          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 1.00/1.18      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.00/1.18  thf('19', plain, ((v1_relat_1 @ sk_C)),
% 1.00/1.18      inference('sup-', [status(thm)], ['17', '18'])).
% 1.00/1.18  thf('20', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ (k1_tarski @ sk_A))),
% 1.00/1.18      inference('demod', [status(thm)], ['16', '19'])).
% 1.00/1.18  thf(l3_zfmisc_1, axiom,
% 1.00/1.18    (![A:$i,B:$i]:
% 1.00/1.18     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 1.00/1.18       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 1.00/1.18  thf('21', plain,
% 1.00/1.18      (![X7 : $i, X8 : $i]:
% 1.00/1.18         (((X8) = (k1_tarski @ X7))
% 1.00/1.18          | ((X8) = (k1_xboole_0))
% 1.00/1.18          | ~ (r1_tarski @ X8 @ (k1_tarski @ X7)))),
% 1.00/1.18      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 1.00/1.18  thf('22', plain,
% 1.00/1.18      ((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 1.00/1.18        | ((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A)))),
% 1.00/1.18      inference('sup-', [status(thm)], ['20', '21'])).
% 1.00/1.18  thf(t14_funct_1, axiom,
% 1.00/1.18    (![A:$i,B:$i]:
% 1.00/1.18     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.00/1.18       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 1.00/1.18         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 1.00/1.18  thf('23', plain,
% 1.00/1.18      (![X17 : $i, X18 : $i]:
% 1.00/1.18         (((k1_relat_1 @ X18) != (k1_tarski @ X17))
% 1.00/1.18          | ((k2_relat_1 @ X18) = (k1_tarski @ (k1_funct_1 @ X18 @ X17)))
% 1.00/1.18          | ~ (v1_funct_1 @ X18)
% 1.00/1.18          | ~ (v1_relat_1 @ X18))),
% 1.00/1.18      inference('cnf', [status(esa)], [t14_funct_1])).
% 1.00/1.18  thf('24', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_C))
% 1.00/1.18          | ((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 1.00/1.18          | ~ (v1_relat_1 @ X0)
% 1.00/1.18          | ~ (v1_funct_1 @ X0)
% 1.00/1.18          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 1.00/1.18      inference('sup-', [status(thm)], ['22', '23'])).
% 1.00/1.18  thf('25', plain,
% 1.00/1.18      ((((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 1.00/1.18        | ~ (v1_funct_1 @ sk_C)
% 1.00/1.18        | ~ (v1_relat_1 @ sk_C)
% 1.00/1.18        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 1.00/1.18      inference('eq_res', [status(thm)], ['24'])).
% 1.00/1.18  thf('26', plain, ((v1_funct_1 @ sk_C)),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf('27', plain, ((v1_relat_1 @ sk_C)),
% 1.00/1.18      inference('sup-', [status(thm)], ['17', '18'])).
% 1.00/1.18  thf('28', plain,
% 1.00/1.18      ((((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 1.00/1.18        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 1.00/1.18      inference('demod', [status(thm)], ['25', '26', '27'])).
% 1.00/1.18  thf('29', plain,
% 1.00/1.18      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 1.00/1.18         != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf('30', plain,
% 1.00/1.18      ((m1_subset_1 @ sk_C @ 
% 1.00/1.18        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf(redefinition_k2_relset_1, axiom,
% 1.00/1.18    (![A:$i,B:$i,C:$i]:
% 1.00/1.18     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.00/1.18       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.00/1.18  thf('31', plain,
% 1.00/1.18      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.00/1.18         (((k2_relset_1 @ X28 @ X29 @ X27) = (k2_relat_1 @ X27))
% 1.00/1.18          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 1.00/1.18      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.00/1.18  thf('32', plain,
% 1.00/1.18      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 1.00/1.18         = (k2_relat_1 @ sk_C))),
% 1.00/1.18      inference('sup-', [status(thm)], ['30', '31'])).
% 1.00/1.18  thf('33', plain,
% 1.00/1.18      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 1.00/1.18      inference('demod', [status(thm)], ['29', '32'])).
% 1.00/1.18  thf('34', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 1.00/1.18      inference('simplify_reflect-', [status(thm)], ['28', '33'])).
% 1.00/1.18  thf(t64_relat_1, axiom,
% 1.00/1.18    (![A:$i]:
% 1.00/1.18     ( ( v1_relat_1 @ A ) =>
% 1.00/1.18       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 1.00/1.18           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 1.00/1.18         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 1.00/1.18  thf('35', plain,
% 1.00/1.18      (![X16 : $i]:
% 1.00/1.18         (((k1_relat_1 @ X16) != (k1_xboole_0))
% 1.00/1.18          | ((X16) = (k1_xboole_0))
% 1.00/1.18          | ~ (v1_relat_1 @ X16))),
% 1.00/1.18      inference('cnf', [status(esa)], [t64_relat_1])).
% 1.00/1.18  thf('36', plain,
% 1.00/1.18      ((((k1_xboole_0) != (k1_xboole_0))
% 1.00/1.18        | ~ (v1_relat_1 @ sk_C)
% 1.00/1.18        | ((sk_C) = (k1_xboole_0)))),
% 1.00/1.18      inference('sup-', [status(thm)], ['34', '35'])).
% 1.00/1.18  thf('37', plain, ((v1_relat_1 @ sk_C)),
% 1.00/1.18      inference('sup-', [status(thm)], ['17', '18'])).
% 1.00/1.18  thf('38', plain,
% 1.00/1.18      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 1.00/1.18      inference('demod', [status(thm)], ['36', '37'])).
% 1.00/1.18  thf('39', plain, (((sk_C) = (k1_xboole_0))),
% 1.00/1.18      inference('simplify', [status(thm)], ['38'])).
% 1.00/1.18  thf('40', plain,
% 1.00/1.18      (((k1_tarski @ sk_A)
% 1.00/1.18         = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ k1_xboole_0))),
% 1.00/1.18      inference('demod', [status(thm)], ['11', '39'])).
% 1.00/1.18  thf(t4_subset_1, axiom,
% 1.00/1.18    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.00/1.18  thf('41', plain,
% 1.00/1.18      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 1.00/1.18      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.00/1.18  thf(t22_relset_1, axiom,
% 1.00/1.18    (![A:$i,B:$i,C:$i]:
% 1.00/1.18     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 1.00/1.18       ( ( ![D:$i]:
% 1.00/1.18           ( ~( ( r2_hidden @ D @ B ) & 
% 1.00/1.18                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) ) ) ) ) ) <=>
% 1.00/1.18         ( ( k1_relset_1 @ B @ A @ C ) = ( B ) ) ) ))).
% 1.00/1.18  thf('42', plain,
% 1.00/1.18      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 1.00/1.18         (((k1_relset_1 @ X30 @ X31 @ X32) != (X30))
% 1.00/1.18          | ~ (r2_hidden @ X33 @ X30)
% 1.00/1.18          | (r2_hidden @ (k4_tarski @ X33 @ (sk_E @ X33 @ X32)) @ X32)
% 1.00/1.18          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 1.00/1.18      inference('cnf', [status(esa)], [t22_relset_1])).
% 1.00/1.18  thf('43', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.00/1.18         ((r2_hidden @ (k4_tarski @ X2 @ (sk_E @ X2 @ k1_xboole_0)) @ 
% 1.00/1.18           k1_xboole_0)
% 1.00/1.18          | ~ (r2_hidden @ X2 @ X1)
% 1.00/1.18          | ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) != (X1)))),
% 1.00/1.18      inference('sup-', [status(thm)], ['41', '42'])).
% 1.00/1.18  thf('44', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         (((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 1.00/1.18          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 1.00/1.18          | (r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ k1_xboole_0)) @ 
% 1.00/1.18             k1_xboole_0))),
% 1.00/1.18      inference('sup-', [status(thm)], ['40', '43'])).
% 1.00/1.18  thf('45', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         ((r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ k1_xboole_0)) @ 
% 1.00/1.18           k1_xboole_0)
% 1.00/1.18          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 1.00/1.18      inference('simplify', [status(thm)], ['44'])).
% 1.00/1.18  thf('46', plain,
% 1.00/1.18      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 1.00/1.18        | (r2_hidden @ 
% 1.00/1.18           (k4_tarski @ (sk_B @ (k1_tarski @ sk_A)) @ 
% 1.00/1.18            (sk_E @ (sk_B @ (k1_tarski @ sk_A)) @ k1_xboole_0)) @ 
% 1.00/1.18           k1_xboole_0))),
% 1.00/1.18      inference('sup-', [status(thm)], ['0', '45'])).
% 1.00/1.18  thf(t7_ordinal1, axiom,
% 1.00/1.18    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.00/1.18  thf('47', plain,
% 1.00/1.18      (![X19 : $i, X20 : $i]:
% 1.00/1.18         (~ (r2_hidden @ X19 @ X20) | ~ (r1_tarski @ X20 @ X19))),
% 1.00/1.18      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.00/1.18  thf('48', plain,
% 1.00/1.18      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 1.00/1.18        | ~ (r1_tarski @ k1_xboole_0 @ 
% 1.00/1.18             (k4_tarski @ (sk_B @ (k1_tarski @ sk_A)) @ 
% 1.00/1.18              (sk_E @ (sk_B @ (k1_tarski @ sk_A)) @ k1_xboole_0))))),
% 1.00/1.18      inference('sup-', [status(thm)], ['46', '47'])).
% 1.00/1.18  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.00/1.18  thf('49', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.00/1.18      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.00/1.18  thf('50', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 1.00/1.18      inference('demod', [status(thm)], ['48', '49'])).
% 1.00/1.18  thf('51', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 1.00/1.18      inference('simplify_reflect-', [status(thm)], ['28', '33'])).
% 1.00/1.18  thf('52', plain,
% 1.00/1.18      (![X17 : $i, X18 : $i]:
% 1.00/1.18         (((k1_relat_1 @ X18) != (k1_tarski @ X17))
% 1.00/1.18          | ((k2_relat_1 @ X18) = (k1_tarski @ (k1_funct_1 @ X18 @ X17)))
% 1.00/1.18          | ~ (v1_funct_1 @ X18)
% 1.00/1.18          | ~ (v1_relat_1 @ X18))),
% 1.00/1.18      inference('cnf', [status(esa)], [t14_funct_1])).
% 1.00/1.18  thf('53', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         (((k1_xboole_0) != (k1_tarski @ X0))
% 1.00/1.18          | ~ (v1_relat_1 @ sk_C)
% 1.00/1.18          | ~ (v1_funct_1 @ sk_C)
% 1.00/1.18          | ((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ X0))))),
% 1.00/1.18      inference('sup-', [status(thm)], ['51', '52'])).
% 1.00/1.18  thf('54', plain, ((v1_relat_1 @ sk_C)),
% 1.00/1.18      inference('sup-', [status(thm)], ['17', '18'])).
% 1.00/1.18  thf('55', plain, ((v1_funct_1 @ sk_C)),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf('56', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         (((k1_xboole_0) != (k1_tarski @ X0))
% 1.00/1.18          | ((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ X0))))),
% 1.00/1.18      inference('demod', [status(thm)], ['53', '54', '55'])).
% 1.00/1.18  thf('57', plain, (((sk_C) = (k1_xboole_0))),
% 1.00/1.18      inference('simplify', [status(thm)], ['38'])).
% 1.00/1.18  thf('58', plain, (((sk_C) = (k1_xboole_0))),
% 1.00/1.18      inference('simplify', [status(thm)], ['38'])).
% 1.00/1.18  thf('59', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         (((k1_xboole_0) != (k1_tarski @ X0))
% 1.00/1.18          | ((k2_relat_1 @ k1_xboole_0)
% 1.00/1.18              = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0))))),
% 1.00/1.18      inference('demod', [status(thm)], ['56', '57', '58'])).
% 1.00/1.18  thf('60', plain,
% 1.00/1.18      ((((k1_xboole_0) != (k1_xboole_0))
% 1.00/1.18        | ((k2_relat_1 @ k1_xboole_0)
% 1.00/1.18            = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A))))),
% 1.00/1.18      inference('sup-', [status(thm)], ['50', '59'])).
% 1.00/1.18  thf('61', plain,
% 1.00/1.18      (((k2_relat_1 @ k1_xboole_0)
% 1.00/1.18         = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A)))),
% 1.00/1.18      inference('simplify', [status(thm)], ['60'])).
% 1.00/1.18  thf('62', plain,
% 1.00/1.18      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 1.00/1.18      inference('demod', [status(thm)], ['29', '32'])).
% 1.00/1.18  thf('63', plain, (((sk_C) = (k1_xboole_0))),
% 1.00/1.18      inference('simplify', [status(thm)], ['38'])).
% 1.00/1.18  thf('64', plain, (((sk_C) = (k1_xboole_0))),
% 1.00/1.18      inference('simplify', [status(thm)], ['38'])).
% 1.00/1.18  thf('65', plain,
% 1.00/1.18      (((k2_relat_1 @ k1_xboole_0)
% 1.00/1.18         != (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A)))),
% 1.00/1.18      inference('demod', [status(thm)], ['62', '63', '64'])).
% 1.00/1.18  thf('66', plain, ($false),
% 1.00/1.18      inference('simplify_reflect-', [status(thm)], ['61', '65'])).
% 1.00/1.18  
% 1.00/1.18  % SZS output end Refutation
% 1.00/1.18  
% 1.00/1.19  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
