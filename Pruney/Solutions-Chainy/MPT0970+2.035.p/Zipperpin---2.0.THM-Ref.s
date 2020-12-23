%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IT4l7TOeKo

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:21 EST 2020

% Result     : Theorem 10.79s
% Output     : Refutation 10.79s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 253 expanded)
%              Number of leaves         :   37 (  90 expanded)
%              Depth                    :   19
%              Number of atoms          :  806 (3226 expanded)
%              Number of equality atoms :   64 ( 226 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(t16_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ! [E: $i] :
                  ~ ( ( r2_hidden @ E @ A )
                    & ( D
                      = ( k1_funct_1 @ C @ E ) ) ) )
       => ( ( k2_relset_1 @ A @ B @ C )
          = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ! [D: $i] :
              ~ ( ( r2_hidden @ D @ B )
                & ! [E: $i] :
                    ~ ( ( r2_hidden @ E @ A )
                      & ( D
                        = ( k1_funct_1 @ C @ E ) ) ) )
         => ( ( k2_relset_1 @ A @ B @ C )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t16_funct_2])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X13 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('3',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('5',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k2_relset_1 @ X20 @ X21 @ X19 )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('6',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','6'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('8',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ sk_C_1 ) @ X0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ sk_C_1 ) @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','9'])).

thf('11',plain,
    ( ( sk_B
      = ( k2_relat_1 @ sk_C_1 ) )
    | ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ) @ sk_B ) ),
    inference(eq_fact,[status(thm)],['10'])).

thf('12',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('14',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != sk_B ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    r2_hidden @ ( sk_C @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X30: $i] :
      ( ~ ( r2_hidden @ X30 @ sk_B )
      | ( r2_hidden @ ( sk_E @ X30 ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    r2_hidden @ ( sk_E @ ( sk_C @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ) ) @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('18',plain,(
    ! [X2: $i] :
      ( r1_tarski @ k1_xboole_0 @ X2 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('20',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X0 = X1 )
      | ~ ( r1_tarski @ X0 @ ( sk_C @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('24',plain,
    ( ( k1_xboole_0
      = ( k2_relat_1 @ sk_C_1 ) )
    | ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ sk_C_1 ) @ k1_xboole_0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['22','23'])).

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
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('25',plain,(
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X1 @ k1_xboole_0 ) @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ( k1_xboole_0 = X1 ) ) ),
    inference('sup-',[status(thm)],['25','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( k1_xboole_0
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( k1_xboole_0
        = ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('35',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k1_xboole_0
      = ( k2_relat_1 @ sk_C_1 ) )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ( X24
        = ( k1_relset_1 @ X24 @ X25 @ X26 ) )
      | ~ ( zip_tseitin_1 @ X26 @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('39',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('41',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('42',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['39','42'])).

thf('44',plain,
    ( ( k1_xboole_0
      = ( k2_relat_1 @ sk_C_1 ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['36','43'])).

thf('45',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != sk_B ),
    inference(demod,[status(thm)],['12','13'])).

thf('46',plain,
    ( ( k1_xboole_0 != sk_B )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('48',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('49',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['39','42'])).

thf('51',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['46','51'])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('53',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k1_relat_1 @ X7 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X7 @ X6 ) @ ( k2_relat_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('56',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('57',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['54','57','58'])).

thf('60',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C_1 @ ( sk_E @ ( sk_C @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ) ) ) @ ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['17','59'])).

thf('61',plain,(
    r2_hidden @ ( sk_C @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['11','14'])).

thf('62',plain,(
    ! [X30: $i] :
      ( ~ ( r2_hidden @ X30 @ sk_B )
      | ( X30
        = ( k1_funct_1 @ sk_C_1 @ ( sk_E @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( sk_C @ ( k2_relat_1 @ sk_C_1 ) @ sk_B )
    = ( k1_funct_1 @ sk_C_1 @ ( sk_E @ ( sk_C @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    r2_hidden @ ( sk_C @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ) @ ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('66',plain,
    ( ~ ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ) @ sk_B )
    | ( sk_B
      = ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    r2_hidden @ ( sk_C @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['11','14'])).

thf('68',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != sk_B ),
    inference(demod,[status(thm)],['12','13'])).

thf('70',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['68','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IT4l7TOeKo
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:54:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 10.79/11.00  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 10.79/11.00  % Solved by: fo/fo7.sh
% 10.79/11.00  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 10.79/11.00  % done 1872 iterations in 10.545s
% 10.79/11.00  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 10.79/11.00  % SZS output start Refutation
% 10.79/11.00  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 10.79/11.00  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 10.79/11.00  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 10.79/11.00  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 10.79/11.00  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 10.79/11.00  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 10.79/11.00  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 10.79/11.00  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 10.79/11.00  thf(sk_B_type, type, sk_B: $i).
% 10.79/11.00  thf(sk_A_type, type, sk_A: $i).
% 10.79/11.00  thf(sk_E_type, type, sk_E: $i > $i).
% 10.79/11.00  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 10.79/11.00  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 10.79/11.00  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 10.79/11.00  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 10.79/11.00  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 10.79/11.00  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 10.79/11.00  thf(sk_C_1_type, type, sk_C_1: $i).
% 10.79/11.00  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 10.79/11.00  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 10.79/11.00  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 10.79/11.00  thf(t2_tarski, axiom,
% 10.79/11.00    (![A:$i,B:$i]:
% 10.79/11.00     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 10.79/11.00       ( ( A ) = ( B ) ) ))).
% 10.79/11.00  thf('0', plain,
% 10.79/11.00      (![X0 : $i, X1 : $i]:
% 10.79/11.00         (((X1) = (X0))
% 10.79/11.00          | (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 10.79/11.00          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 10.79/11.00      inference('cnf', [status(esa)], [t2_tarski])).
% 10.79/11.00  thf(t16_funct_2, conjecture,
% 10.79/11.00    (![A:$i,B:$i,C:$i]:
% 10.79/11.00     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 10.79/11.00         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.79/11.00       ( ( ![D:$i]:
% 10.79/11.00           ( ~( ( r2_hidden @ D @ B ) & 
% 10.79/11.00                ( ![E:$i]:
% 10.79/11.00                  ( ~( ( r2_hidden @ E @ A ) & 
% 10.79/11.00                       ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 10.79/11.00         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 10.79/11.00  thf(zf_stmt_0, negated_conjecture,
% 10.79/11.00    (~( ![A:$i,B:$i,C:$i]:
% 10.79/11.00        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 10.79/11.00            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.79/11.00          ( ( ![D:$i]:
% 10.79/11.00              ( ~( ( r2_hidden @ D @ B ) & 
% 10.79/11.00                   ( ![E:$i]:
% 10.79/11.00                     ( ~( ( r2_hidden @ E @ A ) & 
% 10.79/11.00                          ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 10.79/11.00            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 10.79/11.00    inference('cnf.neg', [status(esa)], [t16_funct_2])).
% 10.79/11.00  thf('1', plain,
% 10.79/11.00      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.79/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.79/11.00  thf(dt_k2_relset_1, axiom,
% 10.79/11.00    (![A:$i,B:$i,C:$i]:
% 10.79/11.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.79/11.00       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 10.79/11.00  thf('2', plain,
% 10.79/11.00      (![X13 : $i, X14 : $i, X15 : $i]:
% 10.79/11.00         ((m1_subset_1 @ (k2_relset_1 @ X13 @ X14 @ X15) @ (k1_zfmisc_1 @ X14))
% 10.79/11.00          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 10.79/11.00      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 10.79/11.00  thf('3', plain,
% 10.79/11.00      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_C_1) @ 
% 10.79/11.00        (k1_zfmisc_1 @ sk_B))),
% 10.79/11.00      inference('sup-', [status(thm)], ['1', '2'])).
% 10.79/11.00  thf('4', plain,
% 10.79/11.00      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.79/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.79/11.00  thf(redefinition_k2_relset_1, axiom,
% 10.79/11.00    (![A:$i,B:$i,C:$i]:
% 10.79/11.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.79/11.00       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 10.79/11.00  thf('5', plain,
% 10.79/11.00      (![X19 : $i, X20 : $i, X21 : $i]:
% 10.79/11.00         (((k2_relset_1 @ X20 @ X21 @ X19) = (k2_relat_1 @ X19))
% 10.79/11.00          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 10.79/11.00      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 10.79/11.00  thf('6', plain,
% 10.79/11.00      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 10.79/11.00      inference('sup-', [status(thm)], ['4', '5'])).
% 10.79/11.00  thf('7', plain,
% 10.79/11.00      ((m1_subset_1 @ (k2_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ sk_B))),
% 10.79/11.00      inference('demod', [status(thm)], ['3', '6'])).
% 10.79/11.00  thf(l3_subset_1, axiom,
% 10.79/11.00    (![A:$i,B:$i]:
% 10.79/11.00     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 10.79/11.00       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 10.79/11.00  thf('8', plain,
% 10.79/11.00      (![X3 : $i, X4 : $i, X5 : $i]:
% 10.79/11.00         (~ (r2_hidden @ X3 @ X4)
% 10.79/11.00          | (r2_hidden @ X3 @ X5)
% 10.79/11.00          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 10.79/11.00      inference('cnf', [status(esa)], [l3_subset_1])).
% 10.79/11.00  thf('9', plain,
% 10.79/11.00      (![X0 : $i]:
% 10.79/11.00         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_1)))),
% 10.79/11.00      inference('sup-', [status(thm)], ['7', '8'])).
% 10.79/11.00  thf('10', plain,
% 10.79/11.00      (![X0 : $i]:
% 10.79/11.00         ((r2_hidden @ (sk_C @ (k2_relat_1 @ sk_C_1) @ X0) @ X0)
% 10.79/11.00          | ((X0) = (k2_relat_1 @ sk_C_1))
% 10.79/11.00          | (r2_hidden @ (sk_C @ (k2_relat_1 @ sk_C_1) @ X0) @ sk_B))),
% 10.79/11.00      inference('sup-', [status(thm)], ['0', '9'])).
% 10.79/11.00  thf('11', plain,
% 10.79/11.00      ((((sk_B) = (k2_relat_1 @ sk_C_1))
% 10.79/11.00        | (r2_hidden @ (sk_C @ (k2_relat_1 @ sk_C_1) @ sk_B) @ sk_B))),
% 10.79/11.00      inference('eq_fact', [status(thm)], ['10'])).
% 10.79/11.00  thf('12', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) != (sk_B))),
% 10.79/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.79/11.00  thf('13', plain,
% 10.79/11.00      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 10.79/11.00      inference('sup-', [status(thm)], ['4', '5'])).
% 10.79/11.00  thf('14', plain, (((k2_relat_1 @ sk_C_1) != (sk_B))),
% 10.79/11.00      inference('demod', [status(thm)], ['12', '13'])).
% 10.79/11.00  thf('15', plain,
% 10.79/11.00      ((r2_hidden @ (sk_C @ (k2_relat_1 @ sk_C_1) @ sk_B) @ sk_B)),
% 10.79/11.00      inference('simplify_reflect-', [status(thm)], ['11', '14'])).
% 10.79/11.00  thf('16', plain,
% 10.79/11.00      (![X30 : $i]:
% 10.79/11.00         (~ (r2_hidden @ X30 @ sk_B) | (r2_hidden @ (sk_E @ X30) @ sk_A))),
% 10.79/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.79/11.00  thf('17', plain,
% 10.79/11.00      ((r2_hidden @ (sk_E @ (sk_C @ (k2_relat_1 @ sk_C_1) @ sk_B)) @ sk_A)),
% 10.79/11.00      inference('sup-', [status(thm)], ['15', '16'])).
% 10.79/11.00  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 10.79/11.00  thf('18', plain, (![X2 : $i]: (r1_tarski @ k1_xboole_0 @ X2)),
% 10.79/11.00      inference('cnf', [status(esa)], [t2_xboole_1])).
% 10.79/11.00  thf('19', plain,
% 10.79/11.00      (![X0 : $i, X1 : $i]:
% 10.79/11.00         (((X1) = (X0))
% 10.79/11.00          | (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 10.79/11.00          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 10.79/11.00      inference('cnf', [status(esa)], [t2_tarski])).
% 10.79/11.00  thf(t7_ordinal1, axiom,
% 10.79/11.00    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 10.79/11.00  thf('20', plain,
% 10.79/11.00      (![X8 : $i, X9 : $i]: (~ (r2_hidden @ X8 @ X9) | ~ (r1_tarski @ X9 @ X8))),
% 10.79/11.00      inference('cnf', [status(esa)], [t7_ordinal1])).
% 10.79/11.00  thf('21', plain,
% 10.79/11.00      (![X0 : $i, X1 : $i]:
% 10.79/11.00         ((r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 10.79/11.00          | ((X0) = (X1))
% 10.79/11.00          | ~ (r1_tarski @ X0 @ (sk_C @ X1 @ X0)))),
% 10.79/11.00      inference('sup-', [status(thm)], ['19', '20'])).
% 10.79/11.00  thf('22', plain,
% 10.79/11.00      (![X0 : $i]:
% 10.79/11.00         (((k1_xboole_0) = (X0)) | (r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0))),
% 10.79/11.00      inference('sup-', [status(thm)], ['18', '21'])).
% 10.79/11.00  thf('23', plain,
% 10.79/11.00      (![X0 : $i]:
% 10.79/11.00         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_1)))),
% 10.79/11.00      inference('sup-', [status(thm)], ['7', '8'])).
% 10.79/11.00  thf('24', plain,
% 10.79/11.00      ((((k1_xboole_0) = (k2_relat_1 @ sk_C_1))
% 10.79/11.00        | (r2_hidden @ (sk_C @ (k2_relat_1 @ sk_C_1) @ k1_xboole_0) @ sk_B))),
% 10.79/11.00      inference('sup-', [status(thm)], ['22', '23'])).
% 10.79/11.00  thf(d1_funct_2, axiom,
% 10.79/11.00    (![A:$i,B:$i,C:$i]:
% 10.79/11.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.79/11.00       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 10.79/11.00           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 10.79/11.00             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 10.79/11.00         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 10.79/11.00           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 10.79/11.00             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 10.79/11.00  thf(zf_stmt_1, axiom,
% 10.79/11.00    (![B:$i,A:$i]:
% 10.79/11.00     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 10.79/11.00       ( zip_tseitin_0 @ B @ A ) ))).
% 10.79/11.00  thf('25', plain,
% 10.79/11.00      (![X22 : $i, X23 : $i]:
% 10.79/11.00         ((zip_tseitin_0 @ X22 @ X23) | ((X22) = (k1_xboole_0)))),
% 10.79/11.00      inference('cnf', [status(esa)], [zf_stmt_1])).
% 10.79/11.00  thf('26', plain,
% 10.79/11.00      (![X0 : $i]:
% 10.79/11.00         (((k1_xboole_0) = (X0)) | (r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0))),
% 10.79/11.00      inference('sup-', [status(thm)], ['18', '21'])).
% 10.79/11.00  thf('27', plain,
% 10.79/11.00      (![X0 : $i, X1 : $i]:
% 10.79/11.00         (((X1) = (X0))
% 10.79/11.00          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 10.79/11.00          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 10.79/11.00      inference('cnf', [status(esa)], [t2_tarski])).
% 10.79/11.00  thf('28', plain,
% 10.79/11.00      (![X0 : $i]:
% 10.79/11.00         (((k1_xboole_0) = (X0))
% 10.79/11.00          | ~ (r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 10.79/11.00          | ((k1_xboole_0) = (X0)))),
% 10.79/11.00      inference('sup-', [status(thm)], ['26', '27'])).
% 10.79/11.00  thf('29', plain,
% 10.79/11.00      (![X0 : $i]:
% 10.79/11.00         (~ (r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 10.79/11.00          | ((k1_xboole_0) = (X0)))),
% 10.79/11.00      inference('simplify', [status(thm)], ['28'])).
% 10.79/11.00  thf('30', plain,
% 10.79/11.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.79/11.00         (~ (r2_hidden @ (sk_C @ X1 @ k1_xboole_0) @ X0)
% 10.79/11.00          | (zip_tseitin_0 @ X0 @ X2)
% 10.79/11.00          | ((k1_xboole_0) = (X1)))),
% 10.79/11.00      inference('sup-', [status(thm)], ['25', '29'])).
% 10.79/11.00  thf('31', plain,
% 10.79/11.00      (![X0 : $i]:
% 10.79/11.00         (((k1_xboole_0) = (k2_relat_1 @ sk_C_1))
% 10.79/11.00          | ((k1_xboole_0) = (k2_relat_1 @ sk_C_1))
% 10.79/11.00          | (zip_tseitin_0 @ sk_B @ X0))),
% 10.79/11.00      inference('sup-', [status(thm)], ['24', '30'])).
% 10.79/11.00  thf('32', plain,
% 10.79/11.00      (![X0 : $i]:
% 10.79/11.00         ((zip_tseitin_0 @ sk_B @ X0) | ((k1_xboole_0) = (k2_relat_1 @ sk_C_1)))),
% 10.79/11.00      inference('simplify', [status(thm)], ['31'])).
% 10.79/11.00  thf('33', plain,
% 10.79/11.00      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.79/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.79/11.00  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 10.79/11.00  thf(zf_stmt_3, axiom,
% 10.79/11.00    (![C:$i,B:$i,A:$i]:
% 10.79/11.00     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 10.79/11.00       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 10.79/11.00  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 10.79/11.00  thf(zf_stmt_5, axiom,
% 10.79/11.00    (![A:$i,B:$i,C:$i]:
% 10.79/11.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.79/11.00       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 10.79/11.00         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 10.79/11.00           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 10.79/11.00             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 10.79/11.00  thf('34', plain,
% 10.79/11.00      (![X27 : $i, X28 : $i, X29 : $i]:
% 10.79/11.00         (~ (zip_tseitin_0 @ X27 @ X28)
% 10.79/11.00          | (zip_tseitin_1 @ X29 @ X27 @ X28)
% 10.79/11.00          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 10.79/11.00      inference('cnf', [status(esa)], [zf_stmt_5])).
% 10.79/11.00  thf('35', plain,
% 10.79/11.00      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 10.79/11.00        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 10.79/11.00      inference('sup-', [status(thm)], ['33', '34'])).
% 10.79/11.00  thf('36', plain,
% 10.79/11.00      ((((k1_xboole_0) = (k2_relat_1 @ sk_C_1))
% 10.79/11.00        | (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A))),
% 10.79/11.00      inference('sup-', [status(thm)], ['32', '35'])).
% 10.79/11.00  thf('37', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 10.79/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.79/11.00  thf('38', plain,
% 10.79/11.00      (![X24 : $i, X25 : $i, X26 : $i]:
% 10.79/11.00         (~ (v1_funct_2 @ X26 @ X24 @ X25)
% 10.79/11.00          | ((X24) = (k1_relset_1 @ X24 @ X25 @ X26))
% 10.79/11.00          | ~ (zip_tseitin_1 @ X26 @ X25 @ X24))),
% 10.79/11.00      inference('cnf', [status(esa)], [zf_stmt_3])).
% 10.79/11.00  thf('39', plain,
% 10.79/11.00      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 10.79/11.00        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 10.79/11.00      inference('sup-', [status(thm)], ['37', '38'])).
% 10.79/11.00  thf('40', plain,
% 10.79/11.00      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.79/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.79/11.00  thf(redefinition_k1_relset_1, axiom,
% 10.79/11.00    (![A:$i,B:$i,C:$i]:
% 10.79/11.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.79/11.00       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 10.79/11.00  thf('41', plain,
% 10.79/11.00      (![X16 : $i, X17 : $i, X18 : $i]:
% 10.79/11.00         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 10.79/11.00          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 10.79/11.00      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 10.79/11.00  thf('42', plain,
% 10.79/11.00      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 10.79/11.00      inference('sup-', [status(thm)], ['40', '41'])).
% 10.79/11.00  thf('43', plain,
% 10.79/11.00      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 10.79/11.00        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 10.79/11.00      inference('demod', [status(thm)], ['39', '42'])).
% 10.79/11.00  thf('44', plain,
% 10.79/11.00      ((((k1_xboole_0) = (k2_relat_1 @ sk_C_1))
% 10.79/11.00        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 10.79/11.00      inference('sup-', [status(thm)], ['36', '43'])).
% 10.79/11.00  thf('45', plain, (((k2_relat_1 @ sk_C_1) != (sk_B))),
% 10.79/11.00      inference('demod', [status(thm)], ['12', '13'])).
% 10.79/11.00  thf('46', plain,
% 10.79/11.00      ((((k1_xboole_0) != (sk_B)) | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 10.79/11.00      inference('sup-', [status(thm)], ['44', '45'])).
% 10.79/11.00  thf('47', plain,
% 10.79/11.00      (![X22 : $i, X23 : $i]:
% 10.79/11.00         ((zip_tseitin_0 @ X22 @ X23) | ((X22) = (k1_xboole_0)))),
% 10.79/11.00      inference('cnf', [status(esa)], [zf_stmt_1])).
% 10.79/11.00  thf('48', plain,
% 10.79/11.00      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 10.79/11.00        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 10.79/11.00      inference('sup-', [status(thm)], ['33', '34'])).
% 10.79/11.00  thf('49', plain,
% 10.79/11.00      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A))),
% 10.79/11.00      inference('sup-', [status(thm)], ['47', '48'])).
% 10.79/11.00  thf('50', plain,
% 10.79/11.00      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 10.79/11.00        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 10.79/11.00      inference('demod', [status(thm)], ['39', '42'])).
% 10.79/11.00  thf('51', plain,
% 10.79/11.00      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 10.79/11.00      inference('sup-', [status(thm)], ['49', '50'])).
% 10.79/11.00  thf('52', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 10.79/11.00      inference('clc', [status(thm)], ['46', '51'])).
% 10.79/11.00  thf(t12_funct_1, axiom,
% 10.79/11.00    (![A:$i,B:$i]:
% 10.79/11.00     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 10.79/11.00       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 10.79/11.00         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 10.79/11.00  thf('53', plain,
% 10.79/11.00      (![X6 : $i, X7 : $i]:
% 10.79/11.00         (~ (r2_hidden @ X6 @ (k1_relat_1 @ X7))
% 10.79/11.00          | (r2_hidden @ (k1_funct_1 @ X7 @ X6) @ (k2_relat_1 @ X7))
% 10.79/11.00          | ~ (v1_funct_1 @ X7)
% 10.79/11.00          | ~ (v1_relat_1 @ X7))),
% 10.79/11.00      inference('cnf', [status(esa)], [t12_funct_1])).
% 10.79/11.00  thf('54', plain,
% 10.79/11.00      (![X0 : $i]:
% 10.79/11.00         (~ (r2_hidden @ X0 @ sk_A)
% 10.79/11.00          | ~ (v1_relat_1 @ sk_C_1)
% 10.79/11.00          | ~ (v1_funct_1 @ sk_C_1)
% 10.79/11.00          | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ (k2_relat_1 @ sk_C_1)))),
% 10.79/11.00      inference('sup-', [status(thm)], ['52', '53'])).
% 10.79/11.00  thf('55', plain,
% 10.79/11.00      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.79/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.79/11.00  thf(cc1_relset_1, axiom,
% 10.79/11.00    (![A:$i,B:$i,C:$i]:
% 10.79/11.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.79/11.00       ( v1_relat_1 @ C ) ))).
% 10.79/11.00  thf('56', plain,
% 10.79/11.00      (![X10 : $i, X11 : $i, X12 : $i]:
% 10.79/11.00         ((v1_relat_1 @ X10)
% 10.79/11.00          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 10.79/11.00      inference('cnf', [status(esa)], [cc1_relset_1])).
% 10.79/11.00  thf('57', plain, ((v1_relat_1 @ sk_C_1)),
% 10.79/11.00      inference('sup-', [status(thm)], ['55', '56'])).
% 10.79/11.00  thf('58', plain, ((v1_funct_1 @ sk_C_1)),
% 10.79/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.79/11.00  thf('59', plain,
% 10.79/11.00      (![X0 : $i]:
% 10.79/11.00         (~ (r2_hidden @ X0 @ sk_A)
% 10.79/11.00          | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ (k2_relat_1 @ sk_C_1)))),
% 10.79/11.00      inference('demod', [status(thm)], ['54', '57', '58'])).
% 10.79/11.00  thf('60', plain,
% 10.79/11.00      ((r2_hidden @ 
% 10.79/11.00        (k1_funct_1 @ sk_C_1 @ (sk_E @ (sk_C @ (k2_relat_1 @ sk_C_1) @ sk_B))) @ 
% 10.79/11.00        (k2_relat_1 @ sk_C_1))),
% 10.79/11.00      inference('sup-', [status(thm)], ['17', '59'])).
% 10.79/11.00  thf('61', plain,
% 10.79/11.00      ((r2_hidden @ (sk_C @ (k2_relat_1 @ sk_C_1) @ sk_B) @ sk_B)),
% 10.79/11.00      inference('simplify_reflect-', [status(thm)], ['11', '14'])).
% 10.79/11.00  thf('62', plain,
% 10.79/11.00      (![X30 : $i]:
% 10.79/11.00         (~ (r2_hidden @ X30 @ sk_B)
% 10.79/11.00          | ((X30) = (k1_funct_1 @ sk_C_1 @ (sk_E @ X30))))),
% 10.79/11.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.79/11.00  thf('63', plain,
% 10.79/11.00      (((sk_C @ (k2_relat_1 @ sk_C_1) @ sk_B)
% 10.79/11.00         = (k1_funct_1 @ sk_C_1 @ 
% 10.79/11.00            (sk_E @ (sk_C @ (k2_relat_1 @ sk_C_1) @ sk_B))))),
% 10.79/11.00      inference('sup-', [status(thm)], ['61', '62'])).
% 10.79/11.00  thf('64', plain,
% 10.79/11.00      ((r2_hidden @ (sk_C @ (k2_relat_1 @ sk_C_1) @ sk_B) @ 
% 10.79/11.00        (k2_relat_1 @ sk_C_1))),
% 10.79/11.00      inference('demod', [status(thm)], ['60', '63'])).
% 10.79/11.00  thf('65', plain,
% 10.79/11.00      (![X0 : $i, X1 : $i]:
% 10.79/11.00         (((X1) = (X0))
% 10.79/11.00          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 10.79/11.00          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 10.79/11.00      inference('cnf', [status(esa)], [t2_tarski])).
% 10.79/11.00  thf('66', plain,
% 10.79/11.00      ((~ (r2_hidden @ (sk_C @ (k2_relat_1 @ sk_C_1) @ sk_B) @ sk_B)
% 10.79/11.00        | ((sk_B) = (k2_relat_1 @ sk_C_1)))),
% 10.79/11.00      inference('sup-', [status(thm)], ['64', '65'])).
% 10.79/11.00  thf('67', plain,
% 10.79/11.00      ((r2_hidden @ (sk_C @ (k2_relat_1 @ sk_C_1) @ sk_B) @ sk_B)),
% 10.79/11.00      inference('simplify_reflect-', [status(thm)], ['11', '14'])).
% 10.79/11.00  thf('68', plain, (((sk_B) = (k2_relat_1 @ sk_C_1))),
% 10.79/11.00      inference('demod', [status(thm)], ['66', '67'])).
% 10.79/11.00  thf('69', plain, (((k2_relat_1 @ sk_C_1) != (sk_B))),
% 10.79/11.00      inference('demod', [status(thm)], ['12', '13'])).
% 10.79/11.00  thf('70', plain, ($false),
% 10.79/11.00      inference('simplify_reflect-', [status(thm)], ['68', '69'])).
% 10.79/11.00  
% 10.79/11.00  % SZS output end Refutation
% 10.79/11.00  
% 10.79/11.01  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
