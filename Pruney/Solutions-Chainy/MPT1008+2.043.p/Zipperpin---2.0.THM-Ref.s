%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6QHJYMzh6A

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:37 EST 2020

% Result     : Theorem 0.72s
% Output     : Refutation 0.72s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 525 expanded)
%              Number of leaves         :   46 ( 171 expanded)
%              Depth                    :   19
%              Number of atoms          :  915 (6692 expanded)
%              Number of equality atoms :  104 ( 639 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ! [X36: $i] :
      ( ( X36 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X36 ) @ X36 ) ) ),
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

thf('2',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( ( k1_relset_1 @ X31 @ X32 @ X33 )
       != X31 )
      | ~ ( r2_hidden @ X34 @ X31 )
      | ( r2_hidden @ ( k4_tarski @ X34 @ ( sk_E @ X34 @ X33 ) ) @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[t22_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ sk_C ) ) @ sk_C )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_2 @ X44 @ X42 @ X43 )
      | ( X42
        = ( k1_relset_1 @ X42 @ X43 @ X44 ) )
      | ~ ( zip_tseitin_1 @ X44 @ X43 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X40: $i,X41: $i] :
      ( ( zip_tseitin_0 @ X40 @ X41 )
      | ( X40 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,(
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

thf('9',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( zip_tseitin_0 @ X45 @ X46 )
      | ( zip_tseitin_1 @ X47 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('10',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    zip_tseitin_1 @ sk_C @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ sk_C ) ) @ sk_C )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['3','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_E @ X0 @ sk_C ) ) @ sk_C ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ ( sk_E @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ sk_C ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['0','16'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('18',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ~ ( r1_tarski @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('19',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ~ ( r1_tarski @ sk_C @ ( k4_tarski @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ ( sk_E @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('21',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v4_relat_1 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('22',plain,(
    v4_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('23',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v4_relat_1 @ X15 @ X16 )
      | ( r1_tarski @ ( k1_relat_1 @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('26',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('27',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['24','27'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('29',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
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

thf('30',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( X9
        = ( k2_tarski @ X7 @ X8 ) )
      | ( X9
        = ( k1_tarski @ X8 ) )
      | ( X9
        = ( k1_tarski @ X7 ) )
      | ( X9 = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ ( k2_tarski @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_tarski @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','32'])).

thf('34',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('35',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['35'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('37',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k1_relat_1 @ X19 )
       != ( k1_tarski @ X18 ) )
      | ( ( k2_relat_1 @ X19 )
        = ( k1_tarski @ ( k1_funct_1 @ X19 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_C ) )
      | ( ( k1_relat_1 @ sk_C )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['38'])).

thf('40',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['25','26'])).

thf('42',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('45',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X30 @ X28 )
        = ( k2_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('46',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','46'])).

thf('48',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['42','47'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('49',plain,(
    ! [X17: $i] :
      ( ( ( k1_relat_1 @ X17 )
       != k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('50',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['25','26'])).

thf('52',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['52'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('55',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('56',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['19','53','54','55'])).

thf('57',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['42','47'])).

thf('58',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k1_relat_1 @ X19 )
       != ( k1_tarski @ X18 ) )
      | ( ( k2_relat_1 @ X19 )
        = ( k1_tarski @ ( k1_funct_1 @ X19 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k2_relat_1 @ sk_C )
        = ( k1_tarski @ ( k1_funct_1 @ sk_C @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['25','26'])).

thf('61',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_C )
        = ( k1_tarski @ ( k1_funct_1 @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['52'])).

thf('64',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['52'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['56','65'])).

thf('67',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','46'])).

thf('69',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['52'])).

thf('70',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['52'])).

thf('71',plain,(
    ( k2_relat_1 @ k1_xboole_0 )
 != ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['67','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6QHJYMzh6A
% 0.14/0.33  % Computer   : n004.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 16:24:39 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.33  % Running portfolio for 600 s
% 0.14/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.33  % Number of cores: 8
% 0.14/0.33  % Python version: Python 3.6.8
% 0.20/0.34  % Running in FO mode
% 0.72/0.90  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.72/0.90  % Solved by: fo/fo7.sh
% 0.72/0.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.72/0.90  % done 639 iterations in 0.460s
% 0.72/0.90  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.72/0.90  % SZS output start Refutation
% 0.72/0.90  thf(sk_B_type, type, sk_B: $i > $i).
% 0.72/0.90  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.72/0.90  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.72/0.90  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.72/0.90  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.72/0.90  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.72/0.90  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.72/0.90  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.72/0.90  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.72/0.90  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.72/0.90  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.72/0.90  thf(sk_C_type, type, sk_C: $i).
% 0.72/0.90  thf(sk_A_type, type, sk_A: $i).
% 0.72/0.90  thf(sk_E_type, type, sk_E: $i > $i > $i).
% 0.72/0.90  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.72/0.90  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.72/0.90  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.72/0.90  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.72/0.90  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.72/0.90  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.72/0.90  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.72/0.90  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.72/0.90  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.72/0.90  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.72/0.90  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.72/0.90  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.72/0.90  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.72/0.90  thf(t29_mcart_1, axiom,
% 0.72/0.90    (![A:$i]:
% 0.72/0.90     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.72/0.90          ( ![B:$i]:
% 0.72/0.90            ( ~( ( r2_hidden @ B @ A ) & 
% 0.72/0.90                 ( ![C:$i,D:$i,E:$i]:
% 0.72/0.90                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.72/0.90                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 0.72/0.90  thf('0', plain,
% 0.72/0.90      (![X36 : $i]:
% 0.72/0.90         (((X36) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X36) @ X36))),
% 0.72/0.90      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.72/0.90  thf(t62_funct_2, conjecture,
% 0.72/0.90    (![A:$i,B:$i,C:$i]:
% 0.72/0.90     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.72/0.90         ( m1_subset_1 @
% 0.72/0.90           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.72/0.90       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.72/0.90         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.72/0.90           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.72/0.90  thf(zf_stmt_0, negated_conjecture,
% 0.72/0.90    (~( ![A:$i,B:$i,C:$i]:
% 0.72/0.90        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.72/0.90            ( m1_subset_1 @
% 0.72/0.90              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.72/0.90          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.72/0.90            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.72/0.90              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 0.72/0.90    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 0.72/0.90  thf('1', plain,
% 0.72/0.90      ((m1_subset_1 @ sk_C @ 
% 0.72/0.90        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf(t22_relset_1, axiom,
% 0.72/0.90    (![A:$i,B:$i,C:$i]:
% 0.72/0.90     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.72/0.90       ( ( ![D:$i]:
% 0.72/0.90           ( ~( ( r2_hidden @ D @ B ) & 
% 0.72/0.90                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) ) ) ) ) ) <=>
% 0.72/0.90         ( ( k1_relset_1 @ B @ A @ C ) = ( B ) ) ) ))).
% 0.72/0.90  thf('2', plain,
% 0.72/0.90      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.72/0.90         (((k1_relset_1 @ X31 @ X32 @ X33) != (X31))
% 0.72/0.90          | ~ (r2_hidden @ X34 @ X31)
% 0.72/0.90          | (r2_hidden @ (k4_tarski @ X34 @ (sk_E @ X34 @ X33)) @ X33)
% 0.72/0.90          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.72/0.90      inference('cnf', [status(esa)], [t22_relset_1])).
% 0.72/0.90  thf('3', plain,
% 0.72/0.90      (![X0 : $i]:
% 0.72/0.90         ((r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ sk_C)) @ sk_C)
% 0.72/0.90          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.72/0.90          | ((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 0.72/0.90              != (k1_tarski @ sk_A)))),
% 0.72/0.90      inference('sup-', [status(thm)], ['1', '2'])).
% 0.72/0.90  thf('4', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf(d1_funct_2, axiom,
% 0.72/0.90    (![A:$i,B:$i,C:$i]:
% 0.72/0.90     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.72/0.90       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.72/0.90           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.72/0.90             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.72/0.90         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.72/0.90           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.72/0.90             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.72/0.90  thf(zf_stmt_1, axiom,
% 0.72/0.90    (![C:$i,B:$i,A:$i]:
% 0.72/0.90     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.72/0.90       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.72/0.90  thf('5', plain,
% 0.72/0.90      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.72/0.90         (~ (v1_funct_2 @ X44 @ X42 @ X43)
% 0.72/0.90          | ((X42) = (k1_relset_1 @ X42 @ X43 @ X44))
% 0.72/0.90          | ~ (zip_tseitin_1 @ X44 @ X43 @ X42))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.72/0.90  thf('6', plain,
% 0.72/0.90      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.72/0.90        | ((k1_tarski @ sk_A)
% 0.72/0.90            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)))),
% 0.72/0.90      inference('sup-', [status(thm)], ['4', '5'])).
% 0.72/0.90  thf(zf_stmt_2, axiom,
% 0.72/0.90    (![B:$i,A:$i]:
% 0.72/0.90     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.72/0.90       ( zip_tseitin_0 @ B @ A ) ))).
% 0.72/0.90  thf('7', plain,
% 0.72/0.90      (![X40 : $i, X41 : $i]:
% 0.72/0.90         ((zip_tseitin_0 @ X40 @ X41) | ((X40) = (k1_xboole_0)))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.72/0.90  thf('8', plain,
% 0.72/0.90      ((m1_subset_1 @ sk_C @ 
% 0.72/0.90        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.72/0.90  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.72/0.90  thf(zf_stmt_5, axiom,
% 0.72/0.90    (![A:$i,B:$i,C:$i]:
% 0.72/0.90     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.72/0.90       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.72/0.90         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.72/0.90           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.72/0.90             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.72/0.90  thf('9', plain,
% 0.72/0.90      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.72/0.90         (~ (zip_tseitin_0 @ X45 @ X46)
% 0.72/0.90          | (zip_tseitin_1 @ X47 @ X45 @ X46)
% 0.72/0.90          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45))))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.72/0.90  thf('10', plain,
% 0.72/0.90      (((zip_tseitin_1 @ sk_C @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.72/0.90        | ~ (zip_tseitin_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.72/0.90      inference('sup-', [status(thm)], ['8', '9'])).
% 0.72/0.90  thf('11', plain,
% 0.72/0.90      ((((sk_B_1) = (k1_xboole_0))
% 0.72/0.90        | (zip_tseitin_1 @ sk_C @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.72/0.90      inference('sup-', [status(thm)], ['7', '10'])).
% 0.72/0.90  thf('12', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf('13', plain, ((zip_tseitin_1 @ sk_C @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.72/0.90      inference('simplify_reflect-', [status(thm)], ['11', '12'])).
% 0.72/0.90  thf('14', plain,
% 0.72/0.90      (((k1_tarski @ sk_A) = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C))),
% 0.72/0.90      inference('demod', [status(thm)], ['6', '13'])).
% 0.72/0.90  thf('15', plain,
% 0.72/0.90      (![X0 : $i]:
% 0.72/0.90         ((r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ sk_C)) @ sk_C)
% 0.72/0.90          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.72/0.90          | ((k1_tarski @ sk_A) != (k1_tarski @ sk_A)))),
% 0.72/0.90      inference('demod', [status(thm)], ['3', '14'])).
% 0.72/0.90  thf('16', plain,
% 0.72/0.90      (![X0 : $i]:
% 0.72/0.90         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.72/0.90          | (r2_hidden @ (k4_tarski @ X0 @ (sk_E @ X0 @ sk_C)) @ sk_C))),
% 0.72/0.90      inference('simplify', [status(thm)], ['15'])).
% 0.72/0.90  thf('17', plain,
% 0.72/0.90      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.72/0.90        | (r2_hidden @ 
% 0.72/0.90           (k4_tarski @ (sk_B @ (k1_tarski @ sk_A)) @ 
% 0.72/0.90            (sk_E @ (sk_B @ (k1_tarski @ sk_A)) @ sk_C)) @ 
% 0.72/0.90           sk_C))),
% 0.72/0.90      inference('sup-', [status(thm)], ['0', '16'])).
% 0.72/0.90  thf(t7_ordinal1, axiom,
% 0.72/0.90    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.72/0.90  thf('18', plain,
% 0.72/0.90      (![X20 : $i, X21 : $i]:
% 0.72/0.90         (~ (r2_hidden @ X20 @ X21) | ~ (r1_tarski @ X21 @ X20))),
% 0.72/0.90      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.72/0.90  thf('19', plain,
% 0.72/0.90      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.72/0.90        | ~ (r1_tarski @ sk_C @ 
% 0.72/0.90             (k4_tarski @ (sk_B @ (k1_tarski @ sk_A)) @ 
% 0.72/0.90              (sk_E @ (sk_B @ (k1_tarski @ sk_A)) @ sk_C))))),
% 0.72/0.90      inference('sup-', [status(thm)], ['17', '18'])).
% 0.72/0.90  thf('20', plain,
% 0.72/0.90      ((m1_subset_1 @ sk_C @ 
% 0.72/0.90        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf(cc2_relset_1, axiom,
% 0.72/0.90    (![A:$i,B:$i,C:$i]:
% 0.72/0.90     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.72/0.90       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.72/0.90  thf('21', plain,
% 0.72/0.90      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.72/0.90         ((v4_relat_1 @ X25 @ X26)
% 0.72/0.90          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.72/0.90      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.72/0.90  thf('22', plain, ((v4_relat_1 @ sk_C @ (k1_tarski @ sk_A))),
% 0.72/0.90      inference('sup-', [status(thm)], ['20', '21'])).
% 0.72/0.90  thf(d18_relat_1, axiom,
% 0.72/0.90    (![A:$i,B:$i]:
% 0.72/0.90     ( ( v1_relat_1 @ B ) =>
% 0.72/0.90       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.72/0.90  thf('23', plain,
% 0.72/0.90      (![X15 : $i, X16 : $i]:
% 0.72/0.90         (~ (v4_relat_1 @ X15 @ X16)
% 0.72/0.90          | (r1_tarski @ (k1_relat_1 @ X15) @ X16)
% 0.72/0.90          | ~ (v1_relat_1 @ X15))),
% 0.72/0.90      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.72/0.90  thf('24', plain,
% 0.72/0.90      ((~ (v1_relat_1 @ sk_C)
% 0.72/0.90        | (r1_tarski @ (k1_relat_1 @ sk_C) @ (k1_tarski @ sk_A)))),
% 0.72/0.90      inference('sup-', [status(thm)], ['22', '23'])).
% 0.72/0.90  thf('25', plain,
% 0.72/0.90      ((m1_subset_1 @ sk_C @ 
% 0.72/0.90        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf(cc1_relset_1, axiom,
% 0.72/0.90    (![A:$i,B:$i,C:$i]:
% 0.72/0.90     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.72/0.90       ( v1_relat_1 @ C ) ))).
% 0.72/0.90  thf('26', plain,
% 0.72/0.90      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.72/0.90         ((v1_relat_1 @ X22)
% 0.72/0.90          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.72/0.90      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.72/0.90  thf('27', plain, ((v1_relat_1 @ sk_C)),
% 0.72/0.90      inference('sup-', [status(thm)], ['25', '26'])).
% 0.72/0.90  thf('28', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ (k1_tarski @ sk_A))),
% 0.72/0.90      inference('demod', [status(thm)], ['24', '27'])).
% 0.72/0.90  thf(t69_enumset1, axiom,
% 0.72/0.90    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.72/0.90  thf('29', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.72/0.90      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.72/0.90  thf(l45_zfmisc_1, axiom,
% 0.72/0.90    (![A:$i,B:$i,C:$i]:
% 0.72/0.90     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.72/0.90       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.72/0.90            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.72/0.90  thf('30', plain,
% 0.72/0.90      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.72/0.90         (((X9) = (k2_tarski @ X7 @ X8))
% 0.72/0.90          | ((X9) = (k1_tarski @ X8))
% 0.72/0.90          | ((X9) = (k1_tarski @ X7))
% 0.72/0.90          | ((X9) = (k1_xboole_0))
% 0.72/0.90          | ~ (r1_tarski @ X9 @ (k2_tarski @ X7 @ X8)))),
% 0.72/0.90      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.72/0.90  thf('31', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]:
% 0.72/0.90         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.72/0.90          | ((X1) = (k1_xboole_0))
% 0.72/0.90          | ((X1) = (k1_tarski @ X0))
% 0.72/0.90          | ((X1) = (k1_tarski @ X0))
% 0.72/0.90          | ((X1) = (k2_tarski @ X0 @ X0)))),
% 0.72/0.90      inference('sup-', [status(thm)], ['29', '30'])).
% 0.72/0.90  thf('32', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]:
% 0.72/0.90         (((X1) = (k2_tarski @ X0 @ X0))
% 0.72/0.90          | ((X1) = (k1_tarski @ X0))
% 0.72/0.90          | ((X1) = (k1_xboole_0))
% 0.72/0.90          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 0.72/0.90      inference('simplify', [status(thm)], ['31'])).
% 0.72/0.90  thf('33', plain,
% 0.72/0.90      ((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 0.72/0.90        | ((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A))
% 0.72/0.90        | ((k1_relat_1 @ sk_C) = (k2_tarski @ sk_A @ sk_A)))),
% 0.72/0.90      inference('sup-', [status(thm)], ['28', '32'])).
% 0.72/0.90  thf('34', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.72/0.90      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.72/0.90  thf('35', plain,
% 0.72/0.90      ((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 0.72/0.90        | ((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A))
% 0.72/0.90        | ((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A)))),
% 0.72/0.90      inference('demod', [status(thm)], ['33', '34'])).
% 0.72/0.90  thf('36', plain,
% 0.72/0.90      ((((k1_relat_1 @ sk_C) = (k1_tarski @ sk_A))
% 0.72/0.90        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.72/0.90      inference('simplify', [status(thm)], ['35'])).
% 0.72/0.90  thf(t14_funct_1, axiom,
% 0.72/0.90    (![A:$i,B:$i]:
% 0.72/0.90     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.72/0.90       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.72/0.90         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.72/0.90  thf('37', plain,
% 0.72/0.90      (![X18 : $i, X19 : $i]:
% 0.72/0.90         (((k1_relat_1 @ X19) != (k1_tarski @ X18))
% 0.72/0.90          | ((k2_relat_1 @ X19) = (k1_tarski @ (k1_funct_1 @ X19 @ X18)))
% 0.72/0.90          | ~ (v1_funct_1 @ X19)
% 0.72/0.90          | ~ (v1_relat_1 @ X19))),
% 0.72/0.90      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.72/0.90  thf('38', plain,
% 0.72/0.90      (![X0 : $i]:
% 0.72/0.90         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_C))
% 0.72/0.90          | ((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 0.72/0.90          | ~ (v1_relat_1 @ X0)
% 0.72/0.90          | ~ (v1_funct_1 @ X0)
% 0.72/0.90          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.72/0.90      inference('sup-', [status(thm)], ['36', '37'])).
% 0.72/0.90  thf('39', plain,
% 0.72/0.90      ((((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 0.72/0.90        | ~ (v1_funct_1 @ sk_C)
% 0.72/0.90        | ~ (v1_relat_1 @ sk_C)
% 0.72/0.90        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.72/0.90      inference('eq_res', [status(thm)], ['38'])).
% 0.72/0.90  thf('40', plain, ((v1_funct_1 @ sk_C)),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf('41', plain, ((v1_relat_1 @ sk_C)),
% 0.72/0.90      inference('sup-', [status(thm)], ['25', '26'])).
% 0.72/0.90  thf('42', plain,
% 0.72/0.90      ((((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 0.72/0.90        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.72/0.90      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.72/0.90  thf('43', plain,
% 0.72/0.90      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 0.72/0.90         != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf('44', plain,
% 0.72/0.90      ((m1_subset_1 @ sk_C @ 
% 0.72/0.90        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf(redefinition_k2_relset_1, axiom,
% 0.72/0.90    (![A:$i,B:$i,C:$i]:
% 0.72/0.90     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.72/0.90       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.72/0.90  thf('45', plain,
% 0.72/0.90      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.72/0.90         (((k2_relset_1 @ X29 @ X30 @ X28) = (k2_relat_1 @ X28))
% 0.72/0.90          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.72/0.90      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.72/0.90  thf('46', plain,
% 0.72/0.90      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 0.72/0.90         = (k2_relat_1 @ sk_C))),
% 0.72/0.90      inference('sup-', [status(thm)], ['44', '45'])).
% 0.72/0.90  thf('47', plain,
% 0.72/0.90      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.72/0.90      inference('demod', [status(thm)], ['43', '46'])).
% 0.72/0.90  thf('48', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.72/0.90      inference('simplify_reflect-', [status(thm)], ['42', '47'])).
% 0.72/0.90  thf(t64_relat_1, axiom,
% 0.72/0.90    (![A:$i]:
% 0.72/0.90     ( ( v1_relat_1 @ A ) =>
% 0.72/0.90       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.72/0.90           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.72/0.90         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.72/0.90  thf('49', plain,
% 0.72/0.90      (![X17 : $i]:
% 0.72/0.90         (((k1_relat_1 @ X17) != (k1_xboole_0))
% 0.72/0.90          | ((X17) = (k1_xboole_0))
% 0.72/0.90          | ~ (v1_relat_1 @ X17))),
% 0.72/0.90      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.72/0.90  thf('50', plain,
% 0.72/0.90      ((((k1_xboole_0) != (k1_xboole_0))
% 0.72/0.90        | ~ (v1_relat_1 @ sk_C)
% 0.72/0.90        | ((sk_C) = (k1_xboole_0)))),
% 0.72/0.90      inference('sup-', [status(thm)], ['48', '49'])).
% 0.72/0.90  thf('51', plain, ((v1_relat_1 @ sk_C)),
% 0.72/0.90      inference('sup-', [status(thm)], ['25', '26'])).
% 0.72/0.90  thf('52', plain,
% 0.72/0.90      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.72/0.90      inference('demod', [status(thm)], ['50', '51'])).
% 0.72/0.90  thf('53', plain, (((sk_C) = (k1_xboole_0))),
% 0.72/0.90      inference('simplify', [status(thm)], ['52'])).
% 0.72/0.90  thf('54', plain, (((sk_C) = (k1_xboole_0))),
% 0.72/0.90      inference('simplify', [status(thm)], ['52'])).
% 0.72/0.90  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.72/0.90  thf('55', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.72/0.90      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.72/0.90  thf('56', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.72/0.90      inference('demod', [status(thm)], ['19', '53', '54', '55'])).
% 0.72/0.90  thf('57', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.72/0.90      inference('simplify_reflect-', [status(thm)], ['42', '47'])).
% 0.72/0.90  thf('58', plain,
% 0.72/0.90      (![X18 : $i, X19 : $i]:
% 0.72/0.90         (((k1_relat_1 @ X19) != (k1_tarski @ X18))
% 0.72/0.90          | ((k2_relat_1 @ X19) = (k1_tarski @ (k1_funct_1 @ X19 @ X18)))
% 0.72/0.90          | ~ (v1_funct_1 @ X19)
% 0.72/0.90          | ~ (v1_relat_1 @ X19))),
% 0.72/0.90      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.72/0.90  thf('59', plain,
% 0.72/0.90      (![X0 : $i]:
% 0.72/0.90         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.72/0.90          | ~ (v1_relat_1 @ sk_C)
% 0.72/0.90          | ~ (v1_funct_1 @ sk_C)
% 0.72/0.90          | ((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ X0))))),
% 0.72/0.90      inference('sup-', [status(thm)], ['57', '58'])).
% 0.72/0.90  thf('60', plain, ((v1_relat_1 @ sk_C)),
% 0.72/0.90      inference('sup-', [status(thm)], ['25', '26'])).
% 0.72/0.90  thf('61', plain, ((v1_funct_1 @ sk_C)),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf('62', plain,
% 0.72/0.90      (![X0 : $i]:
% 0.72/0.90         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.72/0.90          | ((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ X0))))),
% 0.72/0.90      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.72/0.90  thf('63', plain, (((sk_C) = (k1_xboole_0))),
% 0.72/0.90      inference('simplify', [status(thm)], ['52'])).
% 0.72/0.90  thf('64', plain, (((sk_C) = (k1_xboole_0))),
% 0.72/0.90      inference('simplify', [status(thm)], ['52'])).
% 0.72/0.90  thf('65', plain,
% 0.72/0.90      (![X0 : $i]:
% 0.72/0.90         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.72/0.90          | ((k2_relat_1 @ k1_xboole_0)
% 0.72/0.90              = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ X0))))),
% 0.72/0.90      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.72/0.90  thf('66', plain,
% 0.72/0.90      ((((k1_xboole_0) != (k1_xboole_0))
% 0.72/0.90        | ((k2_relat_1 @ k1_xboole_0)
% 0.72/0.90            = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A))))),
% 0.72/0.90      inference('sup-', [status(thm)], ['56', '65'])).
% 0.72/0.90  thf('67', plain,
% 0.72/0.90      (((k2_relat_1 @ k1_xboole_0)
% 0.72/0.90         = (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A)))),
% 0.72/0.90      inference('simplify', [status(thm)], ['66'])).
% 0.72/0.90  thf('68', plain,
% 0.72/0.90      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.72/0.90      inference('demod', [status(thm)], ['43', '46'])).
% 0.72/0.90  thf('69', plain, (((sk_C) = (k1_xboole_0))),
% 0.72/0.90      inference('simplify', [status(thm)], ['52'])).
% 0.72/0.90  thf('70', plain, (((sk_C) = (k1_xboole_0))),
% 0.72/0.90      inference('simplify', [status(thm)], ['52'])).
% 0.72/0.90  thf('71', plain,
% 0.72/0.90      (((k2_relat_1 @ k1_xboole_0)
% 0.72/0.90         != (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A)))),
% 0.72/0.90      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.72/0.90  thf('72', plain, ($false),
% 0.72/0.90      inference('simplify_reflect-', [status(thm)], ['67', '71'])).
% 0.72/0.90  
% 0.72/0.90  % SZS output end Refutation
% 0.72/0.90  
% 0.72/0.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
