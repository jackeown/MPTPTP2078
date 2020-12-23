%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5S3AeJDvjU

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:43 EST 2020

% Result     : Theorem 1.03s
% Output     : Refutation 1.03s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 221 expanded)
%              Number of leaves         :   47 (  86 expanded)
%              Depth                    :   16
%              Number of atoms          :  860 (2363 expanded)
%              Number of equality atoms :   55 ( 102 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(t116_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
            & ! [F: $i] :
                ( ( m1_subset_1 @ F @ A )
               => ~ ( ( r2_hidden @ F @ C )
                    & ( E
                      = ( k1_funct_1 @ D @ F ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [E: $i] :
            ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
              & ! [F: $i] :
                  ( ( m1_subset_1 @ F @ A )
                 => ~ ( ( r2_hidden @ F @ C )
                      & ( E
                        = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t116_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_3 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ( ( k7_relset_1 @ X37 @ X38 @ X36 @ X39 )
        = ( k9_relat_1 @ X36 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_3 @ X0 )
      = ( k9_relat_1 @ sk_D_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_3 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('5',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X28 @ ( k9_relat_1 @ X29 @ X27 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X29 @ X27 @ X28 ) @ X28 ) @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_D_3 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E ) @ sk_E ) @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('8',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( v1_relat_1 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('10',plain,(
    ! [X24: $i,X25: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('11',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E ) @ sk_E ) @ sk_D_3 ),
    inference(demod,[status(thm)],['6','11'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('14',plain,(
    ~ ( v1_xboole_0 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['12','13'])).

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

thf('15',plain,(
    ! [X40: $i,X41: $i] :
      ( ( zip_tseitin_0 @ X40 @ X41 )
      | ( X40 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('16',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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

thf('19',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( zip_tseitin_0 @ X45 @ X46 )
      | ( zip_tseitin_1 @ X47 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('20',plain,
    ( ( zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    v1_funct_2 @ sk_D_3 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_2 @ X44 @ X42 @ X43 )
      | ( X42
        = ( k1_relset_1 @ X42 @ X43 @ X44 ) )
      | ~ ( zip_tseitin_1 @ X44 @ X43 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('24',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('26',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k1_relset_1 @ X34 @ X35 @ X33 )
        = ( k1_relat_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('27',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_3 )
    = ( k1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['21','28'])).

thf('30',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('31',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('33',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_zfmisc_1 @ X13 @ X14 )
        = k1_xboole_0 )
      | ( X14 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('34',plain,(
    ! [X13: $i] :
      ( ( k2_zfmisc_1 @ X13 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('37',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r2_hidden @ X19 @ X20 )
      | ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('38',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
    | ( r2_hidden @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('39',plain,(
    ! [X16: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('40',plain,(
    r2_hidden @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('42',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r2_hidden @ X7 @ X5 )
      | ( r2_hidden @ X7 @ X8 )
      | ( X8
       != ( k3_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('43',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ ( k3_tarski @ X6 ) )
      | ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k3_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,
    ( ( r2_hidden @ ( sk_B @ sk_D_3 ) @ ( k3_tarski @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) )
    | ( v1_xboole_0 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['40','44'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('46',plain,(
    ! [X15: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('47',plain,
    ( ( r2_hidden @ ( sk_B @ sk_D_3 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('49',plain,
    ( ( v1_xboole_0 @ sk_D_3 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['35','49'])).

thf('51',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('52',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D_3 ) )
    | ( v1_xboole_0 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['29','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('55',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D_3 ) )
    | ( k1_xboole_0 = sk_D_3 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_3 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('57',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X28 @ ( k9_relat_1 @ X29 @ X27 ) )
      | ( r2_hidden @ ( sk_D_2 @ X29 @ X27 @ X28 ) @ ( k1_relat_1 @ X29 ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('58',plain,
    ( ~ ( v1_relat_1 @ sk_D_3 )
    | ( r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E ) @ ( k1_relat_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['9','10'])).

thf('60',plain,(
    r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E ) @ ( k1_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('61',plain,(
    ! [X17: $i,X18: $i] :
      ( ( m1_subset_1 @ X17 @ X18 )
      | ~ ( r2_hidden @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('62',plain,(
    m1_subset_1 @ ( sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E ) @ ( k1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( m1_subset_1 @ ( sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E ) @ sk_A )
    | ( k1_xboole_0 = sk_D_3 ) ),
    inference('sup+',[status(thm)],['55','62'])).

thf('64',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_3 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('65',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X28 @ ( k9_relat_1 @ X29 @ X27 ) )
      | ( r2_hidden @ ( sk_D_2 @ X29 @ X27 @ X28 ) @ X27 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('66',plain,
    ( ~ ( v1_relat_1 @ sk_D_3 )
    | ( r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['9','10'])).

thf('68',plain,(
    r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E ) @ sk_C_1 ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X48: $i] :
      ( ( sk_E
       != ( k1_funct_1 @ sk_D_3 @ X48 ) )
      | ~ ( r2_hidden @ X48 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X48 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E ) @ sk_A )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_3 @ ( sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k1_xboole_0 = sk_D_3 )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_3 @ ( sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['63','70'])).

thf('72',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E ) @ sk_E ) @ sk_D_3 ),
    inference(demod,[status(thm)],['6','11'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('73',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X30 @ X32 ) @ X31 )
      | ( X32
        = ( k1_funct_1 @ X31 @ X30 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('74',plain,
    ( ~ ( v1_relat_1 @ sk_D_3 )
    | ~ ( v1_funct_1 @ sk_D_3 )
    | ( sk_E
      = ( k1_funct_1 @ sk_D_3 @ ( sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['9','10'])).

thf('76',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( sk_E
    = ( k1_funct_1 @ sk_D_3 @ ( sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,
    ( ( k1_xboole_0 = sk_D_3 )
    | ( sk_E != sk_E ) ),
    inference(demod,[status(thm)],['71','77'])).

thf('79',plain,(
    k1_xboole_0 = sk_D_3 ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('81',plain,(
    $false ),
    inference(demod,[status(thm)],['14','79','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5S3AeJDvjU
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:51:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.03/1.23  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.03/1.23  % Solved by: fo/fo7.sh
% 1.03/1.23  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.03/1.23  % done 837 iterations in 0.780s
% 1.03/1.23  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.03/1.23  % SZS output start Refutation
% 1.03/1.23  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.03/1.23  thf(sk_A_type, type, sk_A: $i).
% 1.03/1.23  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.03/1.23  thf(sk_D_3_type, type, sk_D_3: $i).
% 1.03/1.23  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.03/1.23  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.03/1.23  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.03/1.23  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.03/1.23  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 1.03/1.23  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.03/1.23  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 1.03/1.23  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.03/1.23  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.03/1.23  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.03/1.23  thf(sk_B_type, type, sk_B: $i > $i).
% 1.03/1.23  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.03/1.23  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.03/1.23  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.03/1.23  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.03/1.23  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.03/1.23  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.03/1.23  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.03/1.23  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.03/1.23  thf(sk_E_type, type, sk_E: $i).
% 1.03/1.23  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.03/1.23  thf(t116_funct_2, conjecture,
% 1.03/1.23    (![A:$i,B:$i,C:$i,D:$i]:
% 1.03/1.23     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.03/1.23         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.03/1.23       ( ![E:$i]:
% 1.03/1.23         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 1.03/1.23              ( ![F:$i]:
% 1.03/1.23                ( ( m1_subset_1 @ F @ A ) =>
% 1.03/1.23                  ( ~( ( r2_hidden @ F @ C ) & 
% 1.03/1.23                       ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ))).
% 1.03/1.23  thf(zf_stmt_0, negated_conjecture,
% 1.03/1.23    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.03/1.23        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.03/1.23            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.03/1.23          ( ![E:$i]:
% 1.03/1.23            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 1.03/1.23                 ( ![F:$i]:
% 1.03/1.23                   ( ( m1_subset_1 @ F @ A ) =>
% 1.03/1.23                     ( ~( ( r2_hidden @ F @ C ) & 
% 1.03/1.23                          ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) )),
% 1.03/1.23    inference('cnf.neg', [status(esa)], [t116_funct_2])).
% 1.03/1.23  thf('0', plain,
% 1.03/1.23      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_3 @ sk_C_1))),
% 1.03/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.23  thf('1', plain,
% 1.03/1.23      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.03/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.23  thf(redefinition_k7_relset_1, axiom,
% 1.03/1.23    (![A:$i,B:$i,C:$i,D:$i]:
% 1.03/1.23     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.03/1.23       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 1.03/1.23  thf('2', plain,
% 1.03/1.23      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 1.03/1.23         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 1.03/1.23          | ((k7_relset_1 @ X37 @ X38 @ X36 @ X39) = (k9_relat_1 @ X36 @ X39)))),
% 1.03/1.23      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 1.03/1.23  thf('3', plain,
% 1.03/1.23      (![X0 : $i]:
% 1.03/1.23         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_3 @ X0)
% 1.03/1.23           = (k9_relat_1 @ sk_D_3 @ X0))),
% 1.03/1.23      inference('sup-', [status(thm)], ['1', '2'])).
% 1.03/1.23  thf('4', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_3 @ sk_C_1))),
% 1.03/1.23      inference('demod', [status(thm)], ['0', '3'])).
% 1.03/1.23  thf(t143_relat_1, axiom,
% 1.03/1.23    (![A:$i,B:$i,C:$i]:
% 1.03/1.23     ( ( v1_relat_1 @ C ) =>
% 1.03/1.23       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 1.03/1.23         ( ?[D:$i]:
% 1.03/1.23           ( ( r2_hidden @ D @ B ) & 
% 1.03/1.23             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 1.03/1.23             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 1.03/1.23  thf('5', plain,
% 1.03/1.23      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.03/1.23         (~ (r2_hidden @ X28 @ (k9_relat_1 @ X29 @ X27))
% 1.03/1.23          | (r2_hidden @ (k4_tarski @ (sk_D_2 @ X29 @ X27 @ X28) @ X28) @ X29)
% 1.03/1.23          | ~ (v1_relat_1 @ X29))),
% 1.03/1.23      inference('cnf', [status(esa)], [t143_relat_1])).
% 1.03/1.23  thf('6', plain,
% 1.03/1.23      ((~ (v1_relat_1 @ sk_D_3)
% 1.03/1.23        | (r2_hidden @ 
% 1.03/1.23           (k4_tarski @ (sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E) @ sk_E) @ sk_D_3))),
% 1.03/1.23      inference('sup-', [status(thm)], ['4', '5'])).
% 1.03/1.23  thf('7', plain,
% 1.03/1.23      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.03/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.23  thf(cc2_relat_1, axiom,
% 1.03/1.23    (![A:$i]:
% 1.03/1.23     ( ( v1_relat_1 @ A ) =>
% 1.03/1.23       ( ![B:$i]:
% 1.03/1.23         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.03/1.23  thf('8', plain,
% 1.03/1.23      (![X22 : $i, X23 : $i]:
% 1.03/1.23         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 1.03/1.23          | (v1_relat_1 @ X22)
% 1.03/1.23          | ~ (v1_relat_1 @ X23))),
% 1.03/1.23      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.03/1.23  thf('9', plain,
% 1.03/1.23      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_D_3))),
% 1.03/1.23      inference('sup-', [status(thm)], ['7', '8'])).
% 1.03/1.23  thf(fc6_relat_1, axiom,
% 1.03/1.23    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.03/1.23  thf('10', plain,
% 1.03/1.23      (![X24 : $i, X25 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X24 @ X25))),
% 1.03/1.23      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.03/1.23  thf('11', plain, ((v1_relat_1 @ sk_D_3)),
% 1.03/1.23      inference('demod', [status(thm)], ['9', '10'])).
% 1.03/1.23  thf('12', plain,
% 1.03/1.23      ((r2_hidden @ (k4_tarski @ (sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E) @ sk_E) @ 
% 1.03/1.23        sk_D_3)),
% 1.03/1.23      inference('demod', [status(thm)], ['6', '11'])).
% 1.03/1.23  thf(d1_xboole_0, axiom,
% 1.03/1.23    (![A:$i]:
% 1.03/1.23     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.03/1.23  thf('13', plain,
% 1.03/1.23      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.03/1.23      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.03/1.23  thf('14', plain, (~ (v1_xboole_0 @ sk_D_3)),
% 1.03/1.23      inference('sup-', [status(thm)], ['12', '13'])).
% 1.03/1.23  thf(d1_funct_2, axiom,
% 1.03/1.23    (![A:$i,B:$i,C:$i]:
% 1.03/1.23     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.03/1.23       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.03/1.23           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.03/1.23             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.03/1.23         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.03/1.23           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.03/1.23             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.03/1.23  thf(zf_stmt_1, axiom,
% 1.03/1.23    (![B:$i,A:$i]:
% 1.03/1.23     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.03/1.23       ( zip_tseitin_0 @ B @ A ) ))).
% 1.03/1.23  thf('15', plain,
% 1.03/1.23      (![X40 : $i, X41 : $i]:
% 1.03/1.23         ((zip_tseitin_0 @ X40 @ X41) | ((X40) = (k1_xboole_0)))),
% 1.03/1.23      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.03/1.23  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.03/1.23  thf('16', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.03/1.23      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.03/1.23  thf('17', plain,
% 1.03/1.23      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 1.03/1.23      inference('sup+', [status(thm)], ['15', '16'])).
% 1.03/1.23  thf('18', plain,
% 1.03/1.23      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.03/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.23  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.03/1.23  thf(zf_stmt_3, axiom,
% 1.03/1.23    (![C:$i,B:$i,A:$i]:
% 1.03/1.23     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.03/1.23       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.03/1.23  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.03/1.23  thf(zf_stmt_5, axiom,
% 1.03/1.23    (![A:$i,B:$i,C:$i]:
% 1.03/1.23     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.03/1.23       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.03/1.23         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.03/1.23           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.03/1.23             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.03/1.23  thf('19', plain,
% 1.03/1.23      (![X45 : $i, X46 : $i, X47 : $i]:
% 1.03/1.23         (~ (zip_tseitin_0 @ X45 @ X46)
% 1.03/1.23          | (zip_tseitin_1 @ X47 @ X45 @ X46)
% 1.03/1.23          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45))))),
% 1.03/1.23      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.03/1.23  thf('20', plain,
% 1.03/1.23      (((zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A)
% 1.03/1.23        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 1.03/1.23      inference('sup-', [status(thm)], ['18', '19'])).
% 1.03/1.23  thf('21', plain,
% 1.03/1.23      (((v1_xboole_0 @ sk_B_1) | (zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A))),
% 1.03/1.23      inference('sup-', [status(thm)], ['17', '20'])).
% 1.03/1.23  thf('22', plain, ((v1_funct_2 @ sk_D_3 @ sk_A @ sk_B_1)),
% 1.03/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.23  thf('23', plain,
% 1.03/1.23      (![X42 : $i, X43 : $i, X44 : $i]:
% 1.03/1.23         (~ (v1_funct_2 @ X44 @ X42 @ X43)
% 1.03/1.23          | ((X42) = (k1_relset_1 @ X42 @ X43 @ X44))
% 1.03/1.23          | ~ (zip_tseitin_1 @ X44 @ X43 @ X42))),
% 1.03/1.23      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.03/1.23  thf('24', plain,
% 1.03/1.23      ((~ (zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A)
% 1.03/1.23        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_3)))),
% 1.03/1.23      inference('sup-', [status(thm)], ['22', '23'])).
% 1.03/1.23  thf('25', plain,
% 1.03/1.23      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.03/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.23  thf(redefinition_k1_relset_1, axiom,
% 1.03/1.23    (![A:$i,B:$i,C:$i]:
% 1.03/1.23     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.03/1.23       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.03/1.23  thf('26', plain,
% 1.03/1.23      (![X33 : $i, X34 : $i, X35 : $i]:
% 1.03/1.23         (((k1_relset_1 @ X34 @ X35 @ X33) = (k1_relat_1 @ X33))
% 1.03/1.23          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 1.03/1.23      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.03/1.23  thf('27', plain,
% 1.03/1.23      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_3) = (k1_relat_1 @ sk_D_3))),
% 1.03/1.23      inference('sup-', [status(thm)], ['25', '26'])).
% 1.03/1.23  thf('28', plain,
% 1.03/1.23      ((~ (zip_tseitin_1 @ sk_D_3 @ sk_B_1 @ sk_A)
% 1.03/1.23        | ((sk_A) = (k1_relat_1 @ sk_D_3)))),
% 1.03/1.23      inference('demod', [status(thm)], ['24', '27'])).
% 1.03/1.23  thf('29', plain,
% 1.03/1.23      (((v1_xboole_0 @ sk_B_1) | ((sk_A) = (k1_relat_1 @ sk_D_3)))),
% 1.03/1.23      inference('sup-', [status(thm)], ['21', '28'])).
% 1.03/1.23  thf('30', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.03/1.23      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.03/1.23  thf(t8_boole, axiom,
% 1.03/1.23    (![A:$i,B:$i]:
% 1.03/1.23     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 1.03/1.23  thf('31', plain,
% 1.03/1.23      (![X3 : $i, X4 : $i]:
% 1.03/1.23         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 1.03/1.23      inference('cnf', [status(esa)], [t8_boole])).
% 1.03/1.23  thf('32', plain,
% 1.03/1.23      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.03/1.23      inference('sup-', [status(thm)], ['30', '31'])).
% 1.03/1.23  thf(t113_zfmisc_1, axiom,
% 1.03/1.23    (![A:$i,B:$i]:
% 1.03/1.23     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.03/1.23       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.03/1.23  thf('33', plain,
% 1.03/1.23      (![X13 : $i, X14 : $i]:
% 1.03/1.23         (((k2_zfmisc_1 @ X13 @ X14) = (k1_xboole_0))
% 1.03/1.23          | ((X14) != (k1_xboole_0)))),
% 1.03/1.23      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.03/1.23  thf('34', plain,
% 1.03/1.23      (![X13 : $i]: ((k2_zfmisc_1 @ X13 @ k1_xboole_0) = (k1_xboole_0))),
% 1.03/1.23      inference('simplify', [status(thm)], ['33'])).
% 1.03/1.23  thf('35', plain,
% 1.03/1.23      (![X0 : $i, X1 : $i]:
% 1.03/1.23         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.03/1.23      inference('sup+', [status(thm)], ['32', '34'])).
% 1.03/1.23  thf('36', plain,
% 1.03/1.23      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.03/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.23  thf(t2_subset, axiom,
% 1.03/1.23    (![A:$i,B:$i]:
% 1.03/1.23     ( ( m1_subset_1 @ A @ B ) =>
% 1.03/1.23       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 1.03/1.23  thf('37', plain,
% 1.03/1.23      (![X19 : $i, X20 : $i]:
% 1.03/1.23         ((r2_hidden @ X19 @ X20)
% 1.03/1.23          | (v1_xboole_0 @ X20)
% 1.03/1.23          | ~ (m1_subset_1 @ X19 @ X20))),
% 1.03/1.23      inference('cnf', [status(esa)], [t2_subset])).
% 1.03/1.23  thf('38', plain,
% 1.03/1.23      (((v1_xboole_0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 1.03/1.23        | (r2_hidden @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))),
% 1.03/1.23      inference('sup-', [status(thm)], ['36', '37'])).
% 1.03/1.23  thf(fc1_subset_1, axiom,
% 1.03/1.23    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.03/1.23  thf('39', plain, (![X16 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X16))),
% 1.03/1.23      inference('cnf', [status(esa)], [fc1_subset_1])).
% 1.03/1.23  thf('40', plain,
% 1.03/1.23      ((r2_hidden @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.03/1.23      inference('clc', [status(thm)], ['38', '39'])).
% 1.03/1.23  thf('41', plain,
% 1.03/1.23      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.03/1.23      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.03/1.23  thf(d4_tarski, axiom,
% 1.03/1.23    (![A:$i,B:$i]:
% 1.03/1.23     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 1.03/1.23       ( ![C:$i]:
% 1.03/1.23         ( ( r2_hidden @ C @ B ) <=>
% 1.03/1.23           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 1.03/1.23  thf('42', plain,
% 1.03/1.23      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 1.03/1.23         (~ (r2_hidden @ X5 @ X6)
% 1.03/1.23          | ~ (r2_hidden @ X7 @ X5)
% 1.03/1.23          | (r2_hidden @ X7 @ X8)
% 1.03/1.23          | ((X8) != (k3_tarski @ X6)))),
% 1.03/1.23      inference('cnf', [status(esa)], [d4_tarski])).
% 1.03/1.23  thf('43', plain,
% 1.03/1.23      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.03/1.23         ((r2_hidden @ X7 @ (k3_tarski @ X6))
% 1.03/1.23          | ~ (r2_hidden @ X7 @ X5)
% 1.03/1.23          | ~ (r2_hidden @ X5 @ X6))),
% 1.03/1.23      inference('simplify', [status(thm)], ['42'])).
% 1.03/1.23  thf('44', plain,
% 1.03/1.23      (![X0 : $i, X1 : $i]:
% 1.03/1.23         ((v1_xboole_0 @ X0)
% 1.03/1.23          | ~ (r2_hidden @ X0 @ X1)
% 1.03/1.23          | (r2_hidden @ (sk_B @ X0) @ (k3_tarski @ X1)))),
% 1.03/1.23      inference('sup-', [status(thm)], ['41', '43'])).
% 1.03/1.23  thf('45', plain,
% 1.03/1.23      (((r2_hidden @ (sk_B @ sk_D_3) @ 
% 1.03/1.23         (k3_tarski @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))))
% 1.03/1.23        | (v1_xboole_0 @ sk_D_3))),
% 1.03/1.23      inference('sup-', [status(thm)], ['40', '44'])).
% 1.03/1.23  thf(t99_zfmisc_1, axiom,
% 1.03/1.23    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 1.03/1.23  thf('46', plain, (![X15 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X15)) = (X15))),
% 1.03/1.23      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 1.03/1.23  thf('47', plain,
% 1.03/1.23      (((r2_hidden @ (sk_B @ sk_D_3) @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 1.03/1.23        | (v1_xboole_0 @ sk_D_3))),
% 1.03/1.23      inference('demod', [status(thm)], ['45', '46'])).
% 1.03/1.23  thf('48', plain,
% 1.03/1.23      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.03/1.23      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.03/1.23  thf('49', plain,
% 1.03/1.23      (((v1_xboole_0 @ sk_D_3)
% 1.03/1.23        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.03/1.23      inference('sup-', [status(thm)], ['47', '48'])).
% 1.03/1.23  thf('50', plain,
% 1.03/1.23      ((~ (v1_xboole_0 @ k1_xboole_0)
% 1.03/1.23        | ~ (v1_xboole_0 @ sk_B_1)
% 1.03/1.23        | (v1_xboole_0 @ sk_D_3))),
% 1.03/1.23      inference('sup-', [status(thm)], ['35', '49'])).
% 1.03/1.23  thf('51', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.03/1.23      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.03/1.23  thf('52', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_D_3))),
% 1.03/1.23      inference('demod', [status(thm)], ['50', '51'])).
% 1.03/1.23  thf('53', plain,
% 1.03/1.23      ((((sk_A) = (k1_relat_1 @ sk_D_3)) | (v1_xboole_0 @ sk_D_3))),
% 1.03/1.23      inference('sup-', [status(thm)], ['29', '52'])).
% 1.03/1.23  thf('54', plain,
% 1.03/1.23      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.03/1.23      inference('sup-', [status(thm)], ['30', '31'])).
% 1.03/1.23  thf('55', plain,
% 1.03/1.23      ((((sk_A) = (k1_relat_1 @ sk_D_3)) | ((k1_xboole_0) = (sk_D_3)))),
% 1.03/1.23      inference('sup-', [status(thm)], ['53', '54'])).
% 1.03/1.23  thf('56', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_3 @ sk_C_1))),
% 1.03/1.23      inference('demod', [status(thm)], ['0', '3'])).
% 1.03/1.23  thf('57', plain,
% 1.03/1.23      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.03/1.23         (~ (r2_hidden @ X28 @ (k9_relat_1 @ X29 @ X27))
% 1.03/1.23          | (r2_hidden @ (sk_D_2 @ X29 @ X27 @ X28) @ (k1_relat_1 @ X29))
% 1.03/1.23          | ~ (v1_relat_1 @ X29))),
% 1.03/1.23      inference('cnf', [status(esa)], [t143_relat_1])).
% 1.03/1.23  thf('58', plain,
% 1.03/1.23      ((~ (v1_relat_1 @ sk_D_3)
% 1.03/1.23        | (r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E) @ 
% 1.03/1.23           (k1_relat_1 @ sk_D_3)))),
% 1.03/1.23      inference('sup-', [status(thm)], ['56', '57'])).
% 1.03/1.23  thf('59', plain, ((v1_relat_1 @ sk_D_3)),
% 1.03/1.23      inference('demod', [status(thm)], ['9', '10'])).
% 1.03/1.23  thf('60', plain,
% 1.03/1.23      ((r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E) @ (k1_relat_1 @ sk_D_3))),
% 1.03/1.23      inference('demod', [status(thm)], ['58', '59'])).
% 1.03/1.23  thf(t1_subset, axiom,
% 1.03/1.23    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 1.03/1.23  thf('61', plain,
% 1.03/1.23      (![X17 : $i, X18 : $i]:
% 1.03/1.23         ((m1_subset_1 @ X17 @ X18) | ~ (r2_hidden @ X17 @ X18))),
% 1.03/1.23      inference('cnf', [status(esa)], [t1_subset])).
% 1.03/1.23  thf('62', plain,
% 1.03/1.23      ((m1_subset_1 @ (sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E) @ (k1_relat_1 @ sk_D_3))),
% 1.03/1.23      inference('sup-', [status(thm)], ['60', '61'])).
% 1.03/1.23  thf('63', plain,
% 1.03/1.23      (((m1_subset_1 @ (sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E) @ sk_A)
% 1.03/1.23        | ((k1_xboole_0) = (sk_D_3)))),
% 1.03/1.23      inference('sup+', [status(thm)], ['55', '62'])).
% 1.03/1.23  thf('64', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_3 @ sk_C_1))),
% 1.03/1.23      inference('demod', [status(thm)], ['0', '3'])).
% 1.03/1.23  thf('65', plain,
% 1.03/1.23      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.03/1.23         (~ (r2_hidden @ X28 @ (k9_relat_1 @ X29 @ X27))
% 1.03/1.23          | (r2_hidden @ (sk_D_2 @ X29 @ X27 @ X28) @ X27)
% 1.03/1.23          | ~ (v1_relat_1 @ X29))),
% 1.03/1.23      inference('cnf', [status(esa)], [t143_relat_1])).
% 1.03/1.23  thf('66', plain,
% 1.03/1.23      ((~ (v1_relat_1 @ sk_D_3)
% 1.03/1.23        | (r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E) @ sk_C_1))),
% 1.03/1.23      inference('sup-', [status(thm)], ['64', '65'])).
% 1.03/1.23  thf('67', plain, ((v1_relat_1 @ sk_D_3)),
% 1.03/1.23      inference('demod', [status(thm)], ['9', '10'])).
% 1.03/1.23  thf('68', plain, ((r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E) @ sk_C_1)),
% 1.03/1.23      inference('demod', [status(thm)], ['66', '67'])).
% 1.03/1.23  thf('69', plain,
% 1.03/1.23      (![X48 : $i]:
% 1.03/1.23         (((sk_E) != (k1_funct_1 @ sk_D_3 @ X48))
% 1.03/1.23          | ~ (r2_hidden @ X48 @ sk_C_1)
% 1.03/1.23          | ~ (m1_subset_1 @ X48 @ sk_A))),
% 1.03/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.23  thf('70', plain,
% 1.03/1.23      ((~ (m1_subset_1 @ (sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E) @ sk_A)
% 1.03/1.23        | ((sk_E) != (k1_funct_1 @ sk_D_3 @ (sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E))))),
% 1.03/1.23      inference('sup-', [status(thm)], ['68', '69'])).
% 1.03/1.23  thf('71', plain,
% 1.03/1.23      ((((k1_xboole_0) = (sk_D_3))
% 1.03/1.23        | ((sk_E) != (k1_funct_1 @ sk_D_3 @ (sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E))))),
% 1.03/1.23      inference('sup-', [status(thm)], ['63', '70'])).
% 1.03/1.23  thf('72', plain,
% 1.03/1.23      ((r2_hidden @ (k4_tarski @ (sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E) @ sk_E) @ 
% 1.03/1.23        sk_D_3)),
% 1.03/1.23      inference('demod', [status(thm)], ['6', '11'])).
% 1.03/1.23  thf(t8_funct_1, axiom,
% 1.03/1.23    (![A:$i,B:$i,C:$i]:
% 1.03/1.23     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.03/1.23       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 1.03/1.23         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 1.03/1.23           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 1.03/1.23  thf('73', plain,
% 1.03/1.23      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.03/1.23         (~ (r2_hidden @ (k4_tarski @ X30 @ X32) @ X31)
% 1.03/1.23          | ((X32) = (k1_funct_1 @ X31 @ X30))
% 1.03/1.23          | ~ (v1_funct_1 @ X31)
% 1.03/1.23          | ~ (v1_relat_1 @ X31))),
% 1.03/1.23      inference('cnf', [status(esa)], [t8_funct_1])).
% 1.03/1.23  thf('74', plain,
% 1.03/1.23      ((~ (v1_relat_1 @ sk_D_3)
% 1.03/1.23        | ~ (v1_funct_1 @ sk_D_3)
% 1.03/1.23        | ((sk_E) = (k1_funct_1 @ sk_D_3 @ (sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E))))),
% 1.03/1.23      inference('sup-', [status(thm)], ['72', '73'])).
% 1.03/1.23  thf('75', plain, ((v1_relat_1 @ sk_D_3)),
% 1.03/1.23      inference('demod', [status(thm)], ['9', '10'])).
% 1.03/1.23  thf('76', plain, ((v1_funct_1 @ sk_D_3)),
% 1.03/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.23  thf('77', plain,
% 1.03/1.23      (((sk_E) = (k1_funct_1 @ sk_D_3 @ (sk_D_2 @ sk_D_3 @ sk_C_1 @ sk_E)))),
% 1.03/1.23      inference('demod', [status(thm)], ['74', '75', '76'])).
% 1.03/1.23  thf('78', plain, ((((k1_xboole_0) = (sk_D_3)) | ((sk_E) != (sk_E)))),
% 1.03/1.23      inference('demod', [status(thm)], ['71', '77'])).
% 1.03/1.23  thf('79', plain, (((k1_xboole_0) = (sk_D_3))),
% 1.03/1.23      inference('simplify', [status(thm)], ['78'])).
% 1.03/1.23  thf('80', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.03/1.23      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.03/1.23  thf('81', plain, ($false),
% 1.03/1.23      inference('demod', [status(thm)], ['14', '79', '80'])).
% 1.03/1.23  
% 1.03/1.23  % SZS output end Refutation
% 1.03/1.23  
% 1.07/1.24  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
