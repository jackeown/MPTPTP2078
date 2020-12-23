%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.I2NN8RgoZd

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:28 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 197 expanded)
%              Number of leaves         :   41 (  77 expanded)
%              Depth                    :   16
%              Number of atoms          :  656 (2204 expanded)
%              Number of equality atoms :   57 ( 146 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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

thf('0',plain,(
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

thf('1',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ~ ( v1_funct_2 @ X55 @ X53 @ X54 )
      | ( X53
        = ( k1_relset_1 @ X53 @ X54 @ X55 ) )
      | ~ ( zip_tseitin_1 @ X55 @ X54 @ X53 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X51: $i,X52: $i] :
      ( ( zip_tseitin_0 @ X51 @ X52 )
      | ( X51 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ~ ( zip_tseitin_0 @ X56 @ X57 )
      | ( zip_tseitin_1 @ X58 @ X56 @ X57 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X57 @ X56 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    zip_tseitin_1 @ sk_C @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( ( k1_relset_1 @ X39 @ X40 @ X38 )
        = ( k1_relat_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('12',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('14',plain,(
    ! [X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = X1 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(l35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('15',plain,(
    ! [X30: $i,X31: $i] :
      ( ( r2_hidden @ X30 @ X31 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X30 ) @ X31 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l35_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != k1_xboole_0 )
      | ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','16'])).

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

thf('18',plain,(
    ! [X47: $i] :
      ( ( X47 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X47 ) @ X47 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('20',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( r2_hidden @ X33 @ X34 )
      | ( r2_hidden @ X33 @ X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf(t12_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) )
     => ( ( ( k1_mcart_1 @ A )
          = B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('23',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( ( k1_mcart_1 @ X45 )
        = X44 )
      | ~ ( r2_hidden @ X45 @ ( k2_zfmisc_1 @ ( k1_tarski @ X44 ) @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[t12_mcart_1])).

thf('24',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k1_mcart_1 @ ( sk_B @ sk_C ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('26',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X41 ) @ X42 )
      | ~ ( r2_hidden @ X41 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('27',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r2_hidden @ ( k1_mcart_1 @ ( sk_B @ sk_C ) ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','27'])).

thf('29',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('31',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('34',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(t7_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf('35',plain,(
    ! [X59: $i,X60: $i,X61: $i,X62: $i] :
      ( ~ ( r2_hidden @ X59 @ X60 )
      | ( X61 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X62 )
      | ~ ( v1_funct_2 @ X62 @ X60 @ X61 )
      | ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X60 @ X61 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X62 @ X59 ) @ X61 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_1 )
      | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_C )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('39',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ sk_B_1 ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['36','39','40'])).

thf('42',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['31','43'])).

thf('45',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    sk_C = k1_xboole_0 ),
    inference(clc,[status(thm)],['44','45'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('47',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('48',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','46','47'])).

thf('49',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['48'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('50',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( r2_hidden @ X36 @ X37 )
      | ~ ( r1_tarski @ X37 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('51',plain,(
    ~ ( r1_tarski @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('52',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['51','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.I2NN8RgoZd
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:40:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.56  % Solved by: fo/fo7.sh
% 0.38/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.56  % done 158 iterations in 0.109s
% 0.38/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.56  % SZS output start Refutation
% 0.38/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.56  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.38/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.56  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.38/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.56  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.38/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.38/0.56  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.38/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.56  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.38/0.56  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.38/0.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.56  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.38/0.56  thf(sk_B_type, type, sk_B: $i > $i).
% 0.38/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.56  thf(t61_funct_2, conjecture,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.38/0.56         ( m1_subset_1 @
% 0.38/0.56           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.38/0.56       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.38/0.56         ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ))).
% 0.38/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.56    (~( ![A:$i,B:$i,C:$i]:
% 0.38/0.56        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.38/0.56            ( m1_subset_1 @
% 0.38/0.56              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.38/0.56          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.38/0.56            ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )),
% 0.38/0.56    inference('cnf.neg', [status(esa)], [t61_funct_2])).
% 0.38/0.56  thf('0', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(d1_funct_2, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.56       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.38/0.56           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.38/0.56             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.38/0.56         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.38/0.56           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.38/0.56             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.38/0.56  thf(zf_stmt_1, axiom,
% 0.38/0.56    (![C:$i,B:$i,A:$i]:
% 0.38/0.56     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.38/0.56       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.38/0.56  thf('1', plain,
% 0.38/0.56      (![X53 : $i, X54 : $i, X55 : $i]:
% 0.38/0.56         (~ (v1_funct_2 @ X55 @ X53 @ X54)
% 0.38/0.56          | ((X53) = (k1_relset_1 @ X53 @ X54 @ X55))
% 0.38/0.56          | ~ (zip_tseitin_1 @ X55 @ X54 @ X53))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.38/0.56  thf('2', plain,
% 0.38/0.56      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.38/0.56        | ((k1_tarski @ sk_A)
% 0.38/0.56            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['0', '1'])).
% 0.38/0.56  thf(zf_stmt_2, axiom,
% 0.38/0.56    (![B:$i,A:$i]:
% 0.38/0.56     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.38/0.56       ( zip_tseitin_0 @ B @ A ) ))).
% 0.38/0.56  thf('3', plain,
% 0.38/0.56      (![X51 : $i, X52 : $i]:
% 0.38/0.56         ((zip_tseitin_0 @ X51 @ X52) | ((X51) = (k1_xboole_0)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.38/0.56  thf('4', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_C @ 
% 0.38/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.38/0.56  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.38/0.56  thf(zf_stmt_5, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.56       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.38/0.56         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.38/0.56           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.38/0.56             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.38/0.56  thf('5', plain,
% 0.38/0.56      (![X56 : $i, X57 : $i, X58 : $i]:
% 0.38/0.56         (~ (zip_tseitin_0 @ X56 @ X57)
% 0.38/0.56          | (zip_tseitin_1 @ X58 @ X56 @ X57)
% 0.38/0.56          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X57 @ X56))))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.38/0.56  thf('6', plain,
% 0.38/0.56      (((zip_tseitin_1 @ sk_C @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.38/0.56        | ~ (zip_tseitin_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['4', '5'])).
% 0.38/0.56  thf('7', plain,
% 0.38/0.56      ((((sk_B_1) = (k1_xboole_0))
% 0.38/0.56        | (zip_tseitin_1 @ sk_C @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['3', '6'])).
% 0.38/0.56  thf('8', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('9', plain, ((zip_tseitin_1 @ sk_C @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.38/0.56      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.38/0.56  thf('10', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_C @ 
% 0.38/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(redefinition_k1_relset_1, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.56       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.38/0.56  thf('11', plain,
% 0.38/0.56      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.38/0.56         (((k1_relset_1 @ X39 @ X40 @ X38) = (k1_relat_1 @ X38))
% 0.38/0.56          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40))))),
% 0.38/0.56      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.38/0.56  thf('12', plain,
% 0.38/0.56      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 0.38/0.56         = (k1_relat_1 @ sk_C))),
% 0.38/0.56      inference('sup-', [status(thm)], ['10', '11'])).
% 0.38/0.56  thf('13', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.38/0.56      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.38/0.56  thf(t3_boole, axiom,
% 0.38/0.56    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.38/0.56  thf('14', plain, (![X1 : $i]: ((k4_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 0.38/0.56      inference('cnf', [status(esa)], [t3_boole])).
% 0.38/0.56  thf(l35_zfmisc_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.38/0.56       ( r2_hidden @ A @ B ) ))).
% 0.38/0.56  thf('15', plain,
% 0.38/0.56      (![X30 : $i, X31 : $i]:
% 0.38/0.56         ((r2_hidden @ X30 @ X31)
% 0.38/0.56          | ((k4_xboole_0 @ (k1_tarski @ X30) @ X31) != (k1_xboole_0)))),
% 0.38/0.56      inference('cnf', [status(esa)], [l35_zfmisc_1])).
% 0.38/0.56  thf('16', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (((k1_tarski @ X0) != (k1_xboole_0)) | (r2_hidden @ X0 @ k1_xboole_0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['14', '15'])).
% 0.38/0.56  thf('17', plain,
% 0.38/0.56      ((((k1_relat_1 @ sk_C) != (k1_xboole_0))
% 0.38/0.56        | (r2_hidden @ sk_A @ k1_xboole_0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['13', '16'])).
% 0.38/0.56  thf(t29_mcart_1, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.38/0.56          ( ![B:$i]:
% 0.38/0.56            ( ~( ( r2_hidden @ B @ A ) & 
% 0.38/0.56                 ( ![C:$i,D:$i,E:$i]:
% 0.38/0.56                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.38/0.56                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.56  thf('18', plain,
% 0.38/0.56      (![X47 : $i]:
% 0.38/0.56         (((X47) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X47) @ X47))),
% 0.38/0.56      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.38/0.56  thf('19', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_C @ 
% 0.38/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(l3_subset_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.38/0.56  thf('20', plain,
% 0.38/0.56      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X33 @ X34)
% 0.38/0.56          | (r2_hidden @ X33 @ X35)
% 0.38/0.56          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35)))),
% 0.38/0.56      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.38/0.56  thf('21', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1))
% 0.38/0.56          | ~ (r2_hidden @ X0 @ sk_C))),
% 0.38/0.56      inference('sup-', [status(thm)], ['19', '20'])).
% 0.38/0.56  thf('22', plain,
% 0.38/0.56      ((((sk_C) = (k1_xboole_0))
% 0.38/0.56        | (r2_hidden @ (sk_B @ sk_C) @ 
% 0.38/0.56           (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['18', '21'])).
% 0.38/0.56  thf(t12_mcart_1, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) =>
% 0.38/0.56       ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 0.38/0.56         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.38/0.56  thf('23', plain,
% 0.38/0.56      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.38/0.56         (((k1_mcart_1 @ X45) = (X44))
% 0.38/0.56          | ~ (r2_hidden @ X45 @ (k2_zfmisc_1 @ (k1_tarski @ X44) @ X46)))),
% 0.38/0.56      inference('cnf', [status(esa)], [t12_mcart_1])).
% 0.38/0.56  thf('24', plain,
% 0.38/0.56      ((((sk_C) = (k1_xboole_0)) | ((k1_mcart_1 @ (sk_B @ sk_C)) = (sk_A)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['22', '23'])).
% 0.38/0.56  thf('25', plain,
% 0.38/0.56      ((((sk_C) = (k1_xboole_0))
% 0.38/0.56        | (r2_hidden @ (sk_B @ sk_C) @ 
% 0.38/0.56           (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['18', '21'])).
% 0.38/0.56  thf(t10_mcart_1, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.38/0.56       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.38/0.56         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.38/0.56  thf('26', plain,
% 0.38/0.56      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.38/0.56         ((r2_hidden @ (k1_mcart_1 @ X41) @ X42)
% 0.38/0.56          | ~ (r2_hidden @ X41 @ (k2_zfmisc_1 @ X42 @ X43)))),
% 0.38/0.56      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.38/0.56  thf('27', plain,
% 0.38/0.56      ((((sk_C) = (k1_xboole_0))
% 0.38/0.56        | (r2_hidden @ (k1_mcart_1 @ (sk_B @ sk_C)) @ (k1_tarski @ sk_A)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['25', '26'])).
% 0.38/0.56  thf('28', plain,
% 0.38/0.56      (((r2_hidden @ sk_A @ (k1_tarski @ sk_A))
% 0.38/0.56        | ((sk_C) = (k1_xboole_0))
% 0.38/0.56        | ((sk_C) = (k1_xboole_0)))),
% 0.38/0.56      inference('sup+', [status(thm)], ['24', '27'])).
% 0.38/0.56  thf('29', plain,
% 0.38/0.56      ((((sk_C) = (k1_xboole_0)) | (r2_hidden @ sk_A @ (k1_tarski @ sk_A)))),
% 0.38/0.56      inference('simplify', [status(thm)], ['28'])).
% 0.38/0.56  thf('30', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.38/0.56      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.38/0.56  thf('31', plain,
% 0.38/0.56      ((((sk_C) = (k1_xboole_0)) | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C)))),
% 0.38/0.56      inference('demod', [status(thm)], ['29', '30'])).
% 0.38/0.56  thf('32', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_C @ 
% 0.38/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('33', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.38/0.56      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.38/0.56  thf('34', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_C @ 
% 0.38/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B_1)))),
% 0.38/0.56      inference('demod', [status(thm)], ['32', '33'])).
% 0.38/0.56  thf(t7_funct_2, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.56     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.38/0.56         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.56       ( ( r2_hidden @ C @ A ) =>
% 0.38/0.56         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.38/0.56           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.38/0.56  thf('35', plain,
% 0.38/0.56      (![X59 : $i, X60 : $i, X61 : $i, X62 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X59 @ X60)
% 0.38/0.56          | ((X61) = (k1_xboole_0))
% 0.38/0.56          | ~ (v1_funct_1 @ X62)
% 0.38/0.56          | ~ (v1_funct_2 @ X62 @ X60 @ X61)
% 0.38/0.56          | ~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X60 @ X61)))
% 0.38/0.56          | (r2_hidden @ (k1_funct_1 @ X62 @ X59) @ X61))),
% 0.38/0.56      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.38/0.56  thf('36', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_1)
% 0.38/0.56          | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ sk_B_1)
% 0.38/0.56          | ~ (v1_funct_1 @ sk_C)
% 0.38/0.56          | ((sk_B_1) = (k1_xboole_0))
% 0.38/0.56          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['34', '35'])).
% 0.38/0.56  thf('37', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('38', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.38/0.56      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.38/0.56  thf('39', plain, ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ sk_B_1)),
% 0.38/0.56      inference('demod', [status(thm)], ['37', '38'])).
% 0.38/0.56  thf('40', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('41', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_1)
% 0.38/0.56          | ((sk_B_1) = (k1_xboole_0))
% 0.38/0.56          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C)))),
% 0.38/0.56      inference('demod', [status(thm)], ['36', '39', '40'])).
% 0.38/0.56  thf('42', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('43', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_1)
% 0.38/0.56          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C)))),
% 0.38/0.56      inference('simplify_reflect-', [status(thm)], ['41', '42'])).
% 0.38/0.56  thf('44', plain,
% 0.38/0.56      ((((sk_C) = (k1_xboole_0))
% 0.38/0.56        | (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B_1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['31', '43'])).
% 0.38/0.56  thf('45', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B_1)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('46', plain, (((sk_C) = (k1_xboole_0))),
% 0.38/0.56      inference('clc', [status(thm)], ['44', '45'])).
% 0.38/0.56  thf(t60_relat_1, axiom,
% 0.38/0.56    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.38/0.56     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.38/0.56  thf('47', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.56      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.38/0.56  thf('48', plain,
% 0.38/0.56      ((((k1_xboole_0) != (k1_xboole_0)) | (r2_hidden @ sk_A @ k1_xboole_0))),
% 0.38/0.56      inference('demod', [status(thm)], ['17', '46', '47'])).
% 0.38/0.56  thf('49', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 0.38/0.56      inference('simplify', [status(thm)], ['48'])).
% 0.38/0.56  thf(t7_ordinal1, axiom,
% 0.38/0.56    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.56  thf('50', plain,
% 0.38/0.56      (![X36 : $i, X37 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X36 @ X37) | ~ (r1_tarski @ X37 @ X36))),
% 0.38/0.56      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.38/0.56  thf('51', plain, (~ (r1_tarski @ k1_xboole_0 @ sk_A)),
% 0.38/0.56      inference('sup-', [status(thm)], ['49', '50'])).
% 0.38/0.56  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.38/0.56  thf('52', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.38/0.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.38/0.56  thf('53', plain, ($false), inference('demod', [status(thm)], ['51', '52'])).
% 0.38/0.56  
% 0.38/0.56  % SZS output end Refutation
% 0.38/0.56  
% 0.38/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
