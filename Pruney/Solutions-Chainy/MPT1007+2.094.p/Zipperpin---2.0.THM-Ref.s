%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0hSRoNBB38

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:28 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 250 expanded)
%              Number of leaves         :   40 (  93 expanded)
%              Depth                    :   13
%              Number of atoms          :  686 (2938 expanded)
%              Number of equality atoms :   62 ( 196 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( v1_funct_2 @ X51 @ X49 @ X50 )
      | ( X49
        = ( k1_relset_1 @ X49 @ X50 @ X51 ) )
      | ~ ( zip_tseitin_1 @ X51 @ X50 @ X49 ) ) ),
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
    ! [X47: $i,X48: $i] :
      ( ( zip_tseitin_0 @ X47 @ X48 )
      | ( X47 = k1_xboole_0 ) ) ),
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
    ! [X52: $i,X53: $i,X54: $i] :
      ( ~ ( zip_tseitin_0 @ X52 @ X53 )
      | ( zip_tseitin_1 @ X54 @ X52 @ X53 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X52 ) ) ) ) ),
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
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k1_relset_1 @ X34 @ X35 @ X33 )
        = ( k1_relat_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('12',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(fc3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ A @ B ) ) )).

thf('15',plain,(
    ! [X28: $i,X29: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) ) ),
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
    ! [X43: $i] :
      ( ( X43 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X43 ) @ X43 ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( r2_hidden @ X30 @ X31 )
      | ( r2_hidden @ X30 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
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

thf('23',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('24',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t15_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ D ) )
     => ( ( ( ( k1_mcart_1 @ A )
            = B )
          | ( ( k1_mcart_1 @ A )
            = C ) )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ D ) ) ) )).

thf('27',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( ( k1_mcart_1 @ X40 )
        = X39 )
      | ( ( k1_mcart_1 @ X40 )
        = X41 )
      | ~ ( r2_hidden @ X40 @ ( k2_zfmisc_1 @ ( k2_tarski @ X41 @ X39 ) @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t15_mcart_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( k1_mcart_1 @ X2 )
        = X0 )
      | ( ( k1_mcart_1 @ X2 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_mcart_1 @ X2 )
        = X0 )
      | ~ ( r2_hidden @ X2 @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ X0 ) )
      | ( ( k1_mcart_1 @ X1 )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['25','29'])).

thf('31',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k1_mcart_1 @ ( sk_B @ sk_C ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['24','30'])).

thf('32',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_C ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('33',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X36 ) @ X37 )
      | ~ ( r2_hidden @ X36 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('34',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r2_hidden @ ( k1_mcart_1 @ ( sk_B @ sk_C ) ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('36',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r2_hidden @ ( k1_mcart_1 @ ( sk_B @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['31','36'])).

thf('38',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf(t7_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf('42',plain,(
    ! [X55: $i,X56: $i,X57: $i,X58: $i] :
      ( ~ ( r2_hidden @ X55 @ X56 )
      | ( X57 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X58 )
      | ~ ( v1_funct_2 @ X58 @ X56 @ X57 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X57 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X58 @ X55 ) @ X57 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_1 )
      | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_C )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('46',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ sk_B_1 ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['43','46','47'])).

thf('49',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C @ X0 ) @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['38','50'])).

thf('52',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_A ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    sk_C = k1_xboole_0 ),
    inference(clc,[status(thm)],['51','52'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('54',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('55',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['17','53','54','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0hSRoNBB38
% 0.15/0.35  % Computer   : n016.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 20:45:19 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.21/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 0.42/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.42/0.59  % Solved by: fo/fo7.sh
% 0.42/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.59  % done 133 iterations in 0.132s
% 0.42/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.42/0.59  % SZS output start Refutation
% 0.42/0.59  thf(sk_B_type, type, sk_B: $i > $i).
% 0.42/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.42/0.59  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.42/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.42/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.42/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.42/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.42/0.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.42/0.59  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.42/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.42/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.59  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.42/0.59  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.42/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.42/0.59  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.42/0.59  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.42/0.59  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.42/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.42/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.59  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.42/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.59  thf(t61_funct_2, conjecture,
% 0.42/0.59    (![A:$i,B:$i,C:$i]:
% 0.42/0.59     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.42/0.59         ( m1_subset_1 @
% 0.42/0.59           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.42/0.59       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.42/0.59         ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ))).
% 0.42/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.59    (~( ![A:$i,B:$i,C:$i]:
% 0.42/0.59        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.42/0.59            ( m1_subset_1 @
% 0.42/0.59              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.42/0.59          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.42/0.59            ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )),
% 0.42/0.59    inference('cnf.neg', [status(esa)], [t61_funct_2])).
% 0.42/0.59  thf('0', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf(d1_funct_2, axiom,
% 0.42/0.59    (![A:$i,B:$i,C:$i]:
% 0.42/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.59       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.42/0.59           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.42/0.59             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.42/0.59         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.42/0.59           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.42/0.59             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.42/0.59  thf(zf_stmt_1, axiom,
% 0.42/0.59    (![C:$i,B:$i,A:$i]:
% 0.42/0.59     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.42/0.59       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.42/0.59  thf('1', plain,
% 0.42/0.59      (![X49 : $i, X50 : $i, X51 : $i]:
% 0.42/0.59         (~ (v1_funct_2 @ X51 @ X49 @ X50)
% 0.42/0.59          | ((X49) = (k1_relset_1 @ X49 @ X50 @ X51))
% 0.42/0.59          | ~ (zip_tseitin_1 @ X51 @ X50 @ X49))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.59  thf('2', plain,
% 0.42/0.59      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.42/0.59        | ((k1_tarski @ sk_A)
% 0.42/0.59            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)))),
% 0.42/0.59      inference('sup-', [status(thm)], ['0', '1'])).
% 0.42/0.59  thf(zf_stmt_2, axiom,
% 0.42/0.59    (![B:$i,A:$i]:
% 0.42/0.59     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.42/0.59       ( zip_tseitin_0 @ B @ A ) ))).
% 0.42/0.59  thf('3', plain,
% 0.42/0.59      (![X47 : $i, X48 : $i]:
% 0.42/0.59         ((zip_tseitin_0 @ X47 @ X48) | ((X47) = (k1_xboole_0)))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.42/0.59  thf('4', plain,
% 0.42/0.59      ((m1_subset_1 @ sk_C @ 
% 0.42/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.42/0.59  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.42/0.59  thf(zf_stmt_5, axiom,
% 0.42/0.59    (![A:$i,B:$i,C:$i]:
% 0.42/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.59       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.42/0.59         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.42/0.59           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.42/0.59             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.42/0.59  thf('5', plain,
% 0.42/0.59      (![X52 : $i, X53 : $i, X54 : $i]:
% 0.42/0.59         (~ (zip_tseitin_0 @ X52 @ X53)
% 0.42/0.59          | (zip_tseitin_1 @ X54 @ X52 @ X53)
% 0.42/0.59          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X52))))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.42/0.59  thf('6', plain,
% 0.42/0.59      (((zip_tseitin_1 @ sk_C @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.42/0.59        | ~ (zip_tseitin_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.42/0.59      inference('sup-', [status(thm)], ['4', '5'])).
% 0.42/0.59  thf('7', plain,
% 0.42/0.59      ((((sk_B_1) = (k1_xboole_0))
% 0.42/0.59        | (zip_tseitin_1 @ sk_C @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.42/0.59      inference('sup-', [status(thm)], ['3', '6'])).
% 0.42/0.59  thf('8', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('9', plain, ((zip_tseitin_1 @ sk_C @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.42/0.59      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.42/0.59  thf('10', plain,
% 0.42/0.59      ((m1_subset_1 @ sk_C @ 
% 0.42/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf(redefinition_k1_relset_1, axiom,
% 0.42/0.59    (![A:$i,B:$i,C:$i]:
% 0.42/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.59       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.42/0.59  thf('11', plain,
% 0.42/0.59      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.42/0.59         (((k1_relset_1 @ X34 @ X35 @ X33) = (k1_relat_1 @ X33))
% 0.42/0.59          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.42/0.59      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.42/0.59  thf('12', plain,
% 0.42/0.59      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C)
% 0.42/0.59         = (k1_relat_1 @ sk_C))),
% 0.42/0.59      inference('sup-', [status(thm)], ['10', '11'])).
% 0.42/0.59  thf('13', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.42/0.59      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.42/0.59  thf(t69_enumset1, axiom,
% 0.42/0.59    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.42/0.59  thf('14', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.42/0.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.42/0.59  thf(fc3_xboole_0, axiom,
% 0.42/0.59    (![A:$i,B:$i]: ( ~( v1_xboole_0 @ ( k2_tarski @ A @ B ) ) ))).
% 0.42/0.59  thf('15', plain,
% 0.42/0.59      (![X28 : $i, X29 : $i]: ~ (v1_xboole_0 @ (k2_tarski @ X28 @ X29))),
% 0.42/0.59      inference('cnf', [status(esa)], [fc3_xboole_0])).
% 0.42/0.59  thf('16', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.42/0.59      inference('sup-', [status(thm)], ['14', '15'])).
% 0.42/0.59  thf('17', plain, (~ (v1_xboole_0 @ (k1_relat_1 @ sk_C))),
% 0.42/0.59      inference('sup-', [status(thm)], ['13', '16'])).
% 0.42/0.59  thf(t29_mcart_1, axiom,
% 0.42/0.59    (![A:$i]:
% 0.42/0.59     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.42/0.59          ( ![B:$i]:
% 0.42/0.59            ( ~( ( r2_hidden @ B @ A ) & 
% 0.42/0.59                 ( ![C:$i,D:$i,E:$i]:
% 0.42/0.59                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.42/0.59                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 0.42/0.59  thf('18', plain,
% 0.42/0.59      (![X43 : $i]:
% 0.42/0.59         (((X43) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X43) @ X43))),
% 0.42/0.59      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.42/0.59  thf('19', plain,
% 0.42/0.59      ((m1_subset_1 @ sk_C @ 
% 0.42/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf(l3_subset_1, axiom,
% 0.42/0.59    (![A:$i,B:$i]:
% 0.42/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.42/0.59       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.42/0.59  thf('20', plain,
% 0.42/0.59      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.42/0.59         (~ (r2_hidden @ X30 @ X31)
% 0.42/0.59          | (r2_hidden @ X30 @ X32)
% 0.42/0.59          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32)))),
% 0.42/0.59      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.42/0.59  thf('21', plain,
% 0.42/0.59      (![X0 : $i]:
% 0.42/0.59         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1))
% 0.42/0.59          | ~ (r2_hidden @ X0 @ sk_C))),
% 0.42/0.59      inference('sup-', [status(thm)], ['19', '20'])).
% 0.42/0.59  thf('22', plain,
% 0.42/0.59      ((((sk_C) = (k1_xboole_0))
% 0.42/0.59        | (r2_hidden @ (sk_B @ sk_C) @ 
% 0.42/0.59           (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.42/0.59      inference('sup-', [status(thm)], ['18', '21'])).
% 0.42/0.59  thf('23', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.42/0.59      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.42/0.59  thf('24', plain,
% 0.42/0.59      ((((sk_C) = (k1_xboole_0))
% 0.42/0.59        | (r2_hidden @ (sk_B @ sk_C) @ 
% 0.42/0.59           (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B_1)))),
% 0.42/0.59      inference('demod', [status(thm)], ['22', '23'])).
% 0.42/0.59  thf('25', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.42/0.59      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.42/0.59  thf('26', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.42/0.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.42/0.59  thf(t15_mcart_1, axiom,
% 0.42/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.59     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ D ) ) =>
% 0.42/0.59       ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.42/0.59         ( r2_hidden @ ( k2_mcart_1 @ A ) @ D ) ) ))).
% 0.42/0.59  thf('27', plain,
% 0.42/0.59      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.42/0.59         (((k1_mcart_1 @ X40) = (X39))
% 0.42/0.59          | ((k1_mcart_1 @ X40) = (X41))
% 0.42/0.59          | ~ (r2_hidden @ X40 @ (k2_zfmisc_1 @ (k2_tarski @ X41 @ X39) @ X42)))),
% 0.42/0.59      inference('cnf', [status(esa)], [t15_mcart_1])).
% 0.42/0.59  thf('28', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.59         (~ (r2_hidden @ X2 @ (k2_zfmisc_1 @ (k1_tarski @ X0) @ X1))
% 0.42/0.59          | ((k1_mcart_1 @ X2) = (X0))
% 0.42/0.59          | ((k1_mcart_1 @ X2) = (X0)))),
% 0.42/0.59      inference('sup-', [status(thm)], ['26', '27'])).
% 0.42/0.59  thf('29', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.59         (((k1_mcart_1 @ X2) = (X0))
% 0.42/0.59          | ~ (r2_hidden @ X2 @ (k2_zfmisc_1 @ (k1_tarski @ X0) @ X1)))),
% 0.42/0.59      inference('simplify', [status(thm)], ['28'])).
% 0.42/0.59  thf('30', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i]:
% 0.42/0.59         (~ (r2_hidden @ X1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ X0))
% 0.42/0.59          | ((k1_mcart_1 @ X1) = (sk_A)))),
% 0.42/0.59      inference('sup-', [status(thm)], ['25', '29'])).
% 0.42/0.59  thf('31', plain,
% 0.42/0.59      ((((sk_C) = (k1_xboole_0)) | ((k1_mcart_1 @ (sk_B @ sk_C)) = (sk_A)))),
% 0.42/0.59      inference('sup-', [status(thm)], ['24', '30'])).
% 0.42/0.59  thf('32', plain,
% 0.42/0.59      ((((sk_C) = (k1_xboole_0))
% 0.42/0.59        | (r2_hidden @ (sk_B @ sk_C) @ 
% 0.42/0.59           (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.42/0.59      inference('sup-', [status(thm)], ['18', '21'])).
% 0.42/0.59  thf(t10_mcart_1, axiom,
% 0.42/0.59    (![A:$i,B:$i,C:$i]:
% 0.42/0.59     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.42/0.59       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.42/0.59         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.42/0.59  thf('33', plain,
% 0.42/0.59      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.42/0.59         ((r2_hidden @ (k1_mcart_1 @ X36) @ X37)
% 0.42/0.59          | ~ (r2_hidden @ X36 @ (k2_zfmisc_1 @ X37 @ X38)))),
% 0.42/0.59      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.42/0.59  thf('34', plain,
% 0.42/0.59      ((((sk_C) = (k1_xboole_0))
% 0.42/0.59        | (r2_hidden @ (k1_mcart_1 @ (sk_B @ sk_C)) @ (k1_tarski @ sk_A)))),
% 0.42/0.59      inference('sup-', [status(thm)], ['32', '33'])).
% 0.42/0.59  thf('35', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.42/0.59      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.42/0.59  thf('36', plain,
% 0.42/0.59      ((((sk_C) = (k1_xboole_0))
% 0.42/0.59        | (r2_hidden @ (k1_mcart_1 @ (sk_B @ sk_C)) @ (k1_relat_1 @ sk_C)))),
% 0.42/0.59      inference('demod', [status(thm)], ['34', '35'])).
% 0.42/0.59  thf('37', plain,
% 0.42/0.59      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))
% 0.42/0.59        | ((sk_C) = (k1_xboole_0))
% 0.42/0.59        | ((sk_C) = (k1_xboole_0)))),
% 0.42/0.59      inference('sup+', [status(thm)], ['31', '36'])).
% 0.42/0.59  thf('38', plain,
% 0.42/0.59      ((((sk_C) = (k1_xboole_0)) | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C)))),
% 0.42/0.59      inference('simplify', [status(thm)], ['37'])).
% 0.42/0.59  thf('39', plain,
% 0.42/0.59      ((m1_subset_1 @ sk_C @ 
% 0.42/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('40', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.42/0.59      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.42/0.59  thf('41', plain,
% 0.42/0.59      ((m1_subset_1 @ sk_C @ 
% 0.42/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B_1)))),
% 0.42/0.59      inference('demod', [status(thm)], ['39', '40'])).
% 0.42/0.59  thf(t7_funct_2, axiom,
% 0.42/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.59     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.42/0.59         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.42/0.59       ( ( r2_hidden @ C @ A ) =>
% 0.42/0.59         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.42/0.59           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.42/0.59  thf('42', plain,
% 0.42/0.59      (![X55 : $i, X56 : $i, X57 : $i, X58 : $i]:
% 0.42/0.59         (~ (r2_hidden @ X55 @ X56)
% 0.42/0.59          | ((X57) = (k1_xboole_0))
% 0.42/0.59          | ~ (v1_funct_1 @ X58)
% 0.42/0.59          | ~ (v1_funct_2 @ X58 @ X56 @ X57)
% 0.42/0.59          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X57)))
% 0.42/0.59          | (r2_hidden @ (k1_funct_1 @ X58 @ X55) @ X57))),
% 0.42/0.59      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.42/0.59  thf('43', plain,
% 0.42/0.59      (![X0 : $i]:
% 0.42/0.59         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_1)
% 0.42/0.59          | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ sk_B_1)
% 0.42/0.59          | ~ (v1_funct_1 @ sk_C)
% 0.42/0.59          | ((sk_B_1) = (k1_xboole_0))
% 0.42/0.59          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C)))),
% 0.42/0.59      inference('sup-', [status(thm)], ['41', '42'])).
% 0.42/0.59  thf('44', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('45', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.42/0.59      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.42/0.59  thf('46', plain, ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ sk_B_1)),
% 0.42/0.59      inference('demod', [status(thm)], ['44', '45'])).
% 0.42/0.59  thf('47', plain, ((v1_funct_1 @ sk_C)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('48', plain,
% 0.42/0.59      (![X0 : $i]:
% 0.42/0.59         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_1)
% 0.42/0.59          | ((sk_B_1) = (k1_xboole_0))
% 0.42/0.59          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C)))),
% 0.42/0.59      inference('demod', [status(thm)], ['43', '46', '47'])).
% 0.42/0.59  thf('49', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('50', plain,
% 0.42/0.59      (![X0 : $i]:
% 0.42/0.59         ((r2_hidden @ (k1_funct_1 @ sk_C @ X0) @ sk_B_1)
% 0.42/0.59          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C)))),
% 0.42/0.59      inference('simplify_reflect-', [status(thm)], ['48', '49'])).
% 0.42/0.59  thf('51', plain,
% 0.42/0.59      ((((sk_C) = (k1_xboole_0))
% 0.42/0.59        | (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B_1))),
% 0.42/0.59      inference('sup-', [status(thm)], ['38', '50'])).
% 0.42/0.59  thf('52', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C @ sk_A) @ sk_B_1)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('53', plain, (((sk_C) = (k1_xboole_0))),
% 0.42/0.59      inference('clc', [status(thm)], ['51', '52'])).
% 0.42/0.59  thf(t60_relat_1, axiom,
% 0.42/0.59    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.42/0.59     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.42/0.59  thf('54', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.42/0.59      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.42/0.59  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.42/0.59  thf('55', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.42/0.59      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.42/0.59  thf('56', plain, ($false),
% 0.42/0.59      inference('demod', [status(thm)], ['17', '53', '54', '55'])).
% 0.42/0.59  
% 0.42/0.59  % SZS output end Refutation
% 0.42/0.59  
% 0.42/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
