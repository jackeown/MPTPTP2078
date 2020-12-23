%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rB9DpMNgXK

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 185 expanded)
%              Number of leaves         :   53 (  78 expanded)
%              Depth                    :   16
%              Number of atoms          :  776 (1752 expanded)
%              Number of equality atoms :   56 ( 106 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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
    v1_funct_2 @ sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
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
    ! [X54: $i,X55: $i,X56: $i] :
      ( ~ ( v1_funct_2 @ X56 @ X54 @ X55 )
      | ( X54
        = ( k1_relset_1 @ X54 @ X55 @ X56 ) )
      | ~ ( zip_tseitin_1 @ X56 @ X55 @ X54 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X52: $i,X53: $i] :
      ( ( zip_tseitin_0 @ X52 @ X53 )
      | ( X52 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('4',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
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
    ! [X57: $i,X58: $i,X59: $i] :
      ( ~ ( zip_tseitin_0 @ X57 @ X58 )
      | ( zip_tseitin_1 @ X59 @ X57 @ X58 )
      | ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X58 @ X57 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k1_relset_1 @ X38 @ X39 @ X37 )
        = ( k1_relat_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('12',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r2_hidden @ X21 @ X22 )
      | ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('16',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('17',plain,(
    ! [X17: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('18',plain,(
    r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['16','17'])).

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

thf('19',plain,(
    ! [X46: $i] :
      ( ( X46 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X46 ) @ X46 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('20',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r2_hidden @ X9 @ X7 )
      | ( r2_hidden @ X9 @ X10 )
      | ( X10
       != ( k3_tarski @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('21',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X9 @ ( k3_tarski @ X8 ) )
      | ~ ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k3_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,
    ( ( r2_hidden @ ( sk_B @ sk_C_1 ) @ ( k3_tarski @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('24',plain,(
    ! [X16: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('25',plain,
    ( ( r2_hidden @ ( sk_B @ sk_C_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(t12_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) )
     => ( ( ( k1_mcart_1 @ A )
          = B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('26',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( ( k1_mcart_1 @ X44 )
        = X43 )
      | ~ ( r2_hidden @ X44 @ ( k2_zfmisc_1 @ ( k1_tarski @ X43 ) @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[t12_mcart_1])).

thf('27',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k1_mcart_1 @ ( sk_B @ sk_C_1 ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( r2_hidden @ ( sk_B @ sk_C_1 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('29',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X40 ) @ X41 )
      | ~ ( r2_hidden @ X40 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('30',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( k1_mcart_1 @ ( sk_B @ sk_C_1 ) ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('34',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('35',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X32 @ ( k1_relat_1 @ X33 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X33 @ X32 ) @ ( k2_relat_1 @ X33 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('36',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('38',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) )
      | ( v1_relat_1 @ X26 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('40',plain,(
    ! [X30: $i,X31: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('41',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['36','41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('45',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v5_relat_1 @ X34 @ X36 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('46',plain,(
    v5_relat_1 @ sk_C_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['44','45'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('47',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v5_relat_1 @ X28 @ X29 )
      | ( r1_tarski @ ( k2_relat_1 @ X28 ) @ X29 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('48',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['39','40'])).

thf('50',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['48','49'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('51',plain,(
    ! [X23: $i,X25: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( r1_tarski @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('52',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('53',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ( r2_hidden @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['43','54'])).

thf('56',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ sk_A ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['55','56'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('58',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('59',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['13','57','58'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('61',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X14 ) @ X15 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['59','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rB9DpMNgXK
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 21:09:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.59  % Solved by: fo/fo7.sh
% 0.21/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.59  % done 274 iterations in 0.137s
% 0.21/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.59  % SZS output start Refutation
% 0.21/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.59  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.59  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.59  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.59  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.21/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.59  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.59  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.59  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.59  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.59  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.60  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.21/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.60  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.60  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.60  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.60  thf(t61_funct_2, conjecture,
% 0.21/0.60    (![A:$i,B:$i,C:$i]:
% 0.21/0.60     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.21/0.60         ( m1_subset_1 @
% 0.21/0.60           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.21/0.60       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.21/0.60         ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ))).
% 0.21/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.60    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.60        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.21/0.60            ( m1_subset_1 @
% 0.21/0.60              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.21/0.60          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.21/0.60            ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) )),
% 0.21/0.60    inference('cnf.neg', [status(esa)], [t61_funct_2])).
% 0.21/0.60  thf('0', plain, ((v1_funct_2 @ sk_C_1 @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf(d1_funct_2, axiom,
% 0.21/0.60    (![A:$i,B:$i,C:$i]:
% 0.21/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.60       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.60           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.21/0.60             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.60         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.60           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.21/0.60             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.21/0.60  thf(zf_stmt_1, axiom,
% 0.21/0.60    (![C:$i,B:$i,A:$i]:
% 0.21/0.60     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.21/0.60       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.21/0.60  thf('1', plain,
% 0.21/0.60      (![X54 : $i, X55 : $i, X56 : $i]:
% 0.21/0.60         (~ (v1_funct_2 @ X56 @ X54 @ X55)
% 0.21/0.60          | ((X54) = (k1_relset_1 @ X54 @ X55 @ X56))
% 0.21/0.60          | ~ (zip_tseitin_1 @ X56 @ X55 @ X54))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.60  thf('2', plain,
% 0.21/0.60      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.21/0.60        | ((k1_tarski @ sk_A)
% 0.21/0.60            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C_1)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.60  thf(zf_stmt_2, axiom,
% 0.21/0.60    (![B:$i,A:$i]:
% 0.21/0.60     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.60       ( zip_tseitin_0 @ B @ A ) ))).
% 0.21/0.60  thf('3', plain,
% 0.21/0.60      (![X52 : $i, X53 : $i]:
% 0.21/0.60         ((zip_tseitin_0 @ X52 @ X53) | ((X52) = (k1_xboole_0)))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.60  thf('4', plain,
% 0.21/0.60      ((m1_subset_1 @ sk_C_1 @ 
% 0.21/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.21/0.60  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.21/0.60  thf(zf_stmt_5, axiom,
% 0.21/0.60    (![A:$i,B:$i,C:$i]:
% 0.21/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.60       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.21/0.60         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.60           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.60             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.21/0.60  thf('5', plain,
% 0.21/0.60      (![X57 : $i, X58 : $i, X59 : $i]:
% 0.21/0.60         (~ (zip_tseitin_0 @ X57 @ X58)
% 0.21/0.60          | (zip_tseitin_1 @ X59 @ X57 @ X58)
% 0.21/0.60          | ~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X58 @ X57))))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.60  thf('6', plain,
% 0.21/0.60      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.21/0.60        | ~ (zip_tseitin_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.60  thf('7', plain,
% 0.21/0.60      ((((sk_B_1) = (k1_xboole_0))
% 0.21/0.60        | (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['3', '6'])).
% 0.21/0.60  thf('8', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('9', plain, ((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.21/0.60      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.21/0.60  thf('10', plain,
% 0.21/0.60      ((m1_subset_1 @ sk_C_1 @ 
% 0.21/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.60    (![A:$i,B:$i,C:$i]:
% 0.21/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.60       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.60  thf('11', plain,
% 0.21/0.60      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.21/0.60         (((k1_relset_1 @ X38 @ X39 @ X37) = (k1_relat_1 @ X37))
% 0.21/0.60          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 0.21/0.60      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.60  thf('12', plain,
% 0.21/0.60      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_C_1)
% 0.21/0.60         = (k1_relat_1 @ sk_C_1))),
% 0.21/0.60      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.60  thf('13', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.21/0.60      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.21/0.60  thf('14', plain,
% 0.21/0.60      ((m1_subset_1 @ sk_C_1 @ 
% 0.21/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf(t2_subset, axiom,
% 0.21/0.60    (![A:$i,B:$i]:
% 0.21/0.60     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.60       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.60  thf('15', plain,
% 0.21/0.60      (![X21 : $i, X22 : $i]:
% 0.21/0.60         ((r2_hidden @ X21 @ X22)
% 0.21/0.60          | (v1_xboole_0 @ X22)
% 0.21/0.60          | ~ (m1_subset_1 @ X21 @ X22))),
% 0.21/0.60      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.60  thf('16', plain,
% 0.21/0.60      (((v1_xboole_0 @ 
% 0.21/0.60         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))
% 0.21/0.60        | (r2_hidden @ sk_C_1 @ 
% 0.21/0.60           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1))))),
% 0.21/0.60      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.60  thf(fc1_subset_1, axiom,
% 0.21/0.60    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.60  thf('17', plain, (![X17 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X17))),
% 0.21/0.60      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.21/0.60  thf('18', plain,
% 0.21/0.60      ((r2_hidden @ sk_C_1 @ 
% 0.21/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.21/0.60      inference('clc', [status(thm)], ['16', '17'])).
% 0.21/0.60  thf(t6_mcart_1, axiom,
% 0.21/0.60    (![A:$i]:
% 0.21/0.60     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.60          ( ![B:$i]:
% 0.21/0.60            ( ~( ( r2_hidden @ B @ A ) & 
% 0.21/0.60                 ( ![C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.21/0.60                   ( ( ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ E ) & 
% 0.21/0.60                       ( r2_hidden @ E @ F ) & ( r2_hidden @ F @ G ) & 
% 0.21/0.60                       ( r2_hidden @ G @ B ) ) =>
% 0.21/0.60                     ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 0.21/0.60  thf('19', plain,
% 0.21/0.60      (![X46 : $i]:
% 0.21/0.60         (((X46) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X46) @ X46))),
% 0.21/0.60      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.21/0.60  thf(d4_tarski, axiom,
% 0.21/0.60    (![A:$i,B:$i]:
% 0.21/0.60     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 0.21/0.60       ( ![C:$i]:
% 0.21/0.60         ( ( r2_hidden @ C @ B ) <=>
% 0.21/0.60           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 0.21/0.60  thf('20', plain,
% 0.21/0.60      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.60         (~ (r2_hidden @ X7 @ X8)
% 0.21/0.60          | ~ (r2_hidden @ X9 @ X7)
% 0.21/0.60          | (r2_hidden @ X9 @ X10)
% 0.21/0.60          | ((X10) != (k3_tarski @ X8)))),
% 0.21/0.60      inference('cnf', [status(esa)], [d4_tarski])).
% 0.21/0.60  thf('21', plain,
% 0.21/0.60      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.60         ((r2_hidden @ X9 @ (k3_tarski @ X8))
% 0.21/0.60          | ~ (r2_hidden @ X9 @ X7)
% 0.21/0.60          | ~ (r2_hidden @ X7 @ X8))),
% 0.21/0.60      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.60  thf('22', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i]:
% 0.21/0.60         (((X0) = (k1_xboole_0))
% 0.21/0.60          | ~ (r2_hidden @ X0 @ X1)
% 0.21/0.60          | (r2_hidden @ (sk_B @ X0) @ (k3_tarski @ X1)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['19', '21'])).
% 0.21/0.60  thf('23', plain,
% 0.21/0.60      (((r2_hidden @ (sk_B @ sk_C_1) @ 
% 0.21/0.60         (k3_tarski @ 
% 0.21/0.60          (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1))))
% 0.21/0.60        | ((sk_C_1) = (k1_xboole_0)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['18', '22'])).
% 0.21/0.60  thf(t99_zfmisc_1, axiom,
% 0.21/0.60    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.21/0.60  thf('24', plain, (![X16 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X16)) = (X16))),
% 0.21/0.60      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.21/0.60  thf('25', plain,
% 0.21/0.60      (((r2_hidden @ (sk_B @ sk_C_1) @ 
% 0.21/0.60         (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1))
% 0.21/0.60        | ((sk_C_1) = (k1_xboole_0)))),
% 0.21/0.60      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.60  thf(t12_mcart_1, axiom,
% 0.21/0.60    (![A:$i,B:$i,C:$i]:
% 0.21/0.60     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) =>
% 0.21/0.60       ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 0.21/0.60         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.21/0.60  thf('26', plain,
% 0.21/0.60      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.21/0.60         (((k1_mcart_1 @ X44) = (X43))
% 0.21/0.60          | ~ (r2_hidden @ X44 @ (k2_zfmisc_1 @ (k1_tarski @ X43) @ X45)))),
% 0.21/0.60      inference('cnf', [status(esa)], [t12_mcart_1])).
% 0.21/0.60  thf('27', plain,
% 0.21/0.60      ((((sk_C_1) = (k1_xboole_0)) | ((k1_mcart_1 @ (sk_B @ sk_C_1)) = (sk_A)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.60  thf('28', plain,
% 0.21/0.60      (((r2_hidden @ (sk_B @ sk_C_1) @ 
% 0.21/0.60         (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1))
% 0.21/0.60        | ((sk_C_1) = (k1_xboole_0)))),
% 0.21/0.60      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.60  thf(t10_mcart_1, axiom,
% 0.21/0.60    (![A:$i,B:$i,C:$i]:
% 0.21/0.60     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.21/0.60       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.21/0.60         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.21/0.60  thf('29', plain,
% 0.21/0.60      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.21/0.60         ((r2_hidden @ (k1_mcart_1 @ X40) @ X41)
% 0.21/0.60          | ~ (r2_hidden @ X40 @ (k2_zfmisc_1 @ X41 @ X42)))),
% 0.21/0.60      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.60  thf('30', plain,
% 0.21/0.60      ((((sk_C_1) = (k1_xboole_0))
% 0.21/0.60        | (r2_hidden @ (k1_mcart_1 @ (sk_B @ sk_C_1)) @ (k1_tarski @ sk_A)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.60  thf('31', plain,
% 0.21/0.60      (((r2_hidden @ sk_A @ (k1_tarski @ sk_A))
% 0.21/0.60        | ((sk_C_1) = (k1_xboole_0))
% 0.21/0.60        | ((sk_C_1) = (k1_xboole_0)))),
% 0.21/0.60      inference('sup+', [status(thm)], ['27', '30'])).
% 0.21/0.60  thf('32', plain,
% 0.21/0.60      ((((sk_C_1) = (k1_xboole_0)) | (r2_hidden @ sk_A @ (k1_tarski @ sk_A)))),
% 0.21/0.60      inference('simplify', [status(thm)], ['31'])).
% 0.21/0.60  thf('33', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.21/0.60      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.21/0.60  thf('34', plain,
% 0.21/0.60      ((((sk_C_1) = (k1_xboole_0)) | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1)))),
% 0.21/0.60      inference('demod', [status(thm)], ['32', '33'])).
% 0.21/0.60  thf(t12_funct_1, axiom,
% 0.21/0.60    (![A:$i,B:$i]:
% 0.21/0.60     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.60       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.21/0.60         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 0.21/0.60  thf('35', plain,
% 0.21/0.60      (![X32 : $i, X33 : $i]:
% 0.21/0.60         (~ (r2_hidden @ X32 @ (k1_relat_1 @ X33))
% 0.21/0.60          | (r2_hidden @ (k1_funct_1 @ X33 @ X32) @ (k2_relat_1 @ X33))
% 0.21/0.60          | ~ (v1_funct_1 @ X33)
% 0.21/0.60          | ~ (v1_relat_1 @ X33))),
% 0.21/0.60      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.21/0.60  thf('36', plain,
% 0.21/0.60      ((((sk_C_1) = (k1_xboole_0))
% 0.21/0.60        | ~ (v1_relat_1 @ sk_C_1)
% 0.21/0.60        | ~ (v1_funct_1 @ sk_C_1)
% 0.21/0.60        | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ (k2_relat_1 @ sk_C_1)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.60  thf('37', plain,
% 0.21/0.60      ((m1_subset_1 @ sk_C_1 @ 
% 0.21/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf(cc2_relat_1, axiom,
% 0.21/0.60    (![A:$i]:
% 0.21/0.60     ( ( v1_relat_1 @ A ) =>
% 0.21/0.60       ( ![B:$i]:
% 0.21/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.21/0.60  thf('38', plain,
% 0.21/0.60      (![X26 : $i, X27 : $i]:
% 0.21/0.60         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27))
% 0.21/0.60          | (v1_relat_1 @ X26)
% 0.21/0.60          | ~ (v1_relat_1 @ X27))),
% 0.21/0.60      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.60  thf('39', plain,
% 0.21/0.60      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1))
% 0.21/0.60        | (v1_relat_1 @ sk_C_1))),
% 0.21/0.60      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.60  thf(fc6_relat_1, axiom,
% 0.21/0.60    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.60  thf('40', plain,
% 0.21/0.60      (![X30 : $i, X31 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X30 @ X31))),
% 0.21/0.60      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.60  thf('41', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.60      inference('demod', [status(thm)], ['39', '40'])).
% 0.21/0.60  thf('42', plain, ((v1_funct_1 @ sk_C_1)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('43', plain,
% 0.21/0.60      ((((sk_C_1) = (k1_xboole_0))
% 0.21/0.60        | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ (k2_relat_1 @ sk_C_1)))),
% 0.21/0.60      inference('demod', [status(thm)], ['36', '41', '42'])).
% 0.21/0.60  thf('44', plain,
% 0.21/0.60      ((m1_subset_1 @ sk_C_1 @ 
% 0.21/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf(cc2_relset_1, axiom,
% 0.21/0.60    (![A:$i,B:$i,C:$i]:
% 0.21/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.60       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.60  thf('45', plain,
% 0.21/0.60      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.21/0.60         ((v5_relat_1 @ X34 @ X36)
% 0.21/0.60          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.21/0.60      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.60  thf('46', plain, ((v5_relat_1 @ sk_C_1 @ sk_B_1)),
% 0.21/0.60      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.60  thf(d19_relat_1, axiom,
% 0.21/0.60    (![A:$i,B:$i]:
% 0.21/0.60     ( ( v1_relat_1 @ B ) =>
% 0.21/0.60       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.60  thf('47', plain,
% 0.21/0.60      (![X28 : $i, X29 : $i]:
% 0.21/0.60         (~ (v5_relat_1 @ X28 @ X29)
% 0.21/0.60          | (r1_tarski @ (k2_relat_1 @ X28) @ X29)
% 0.21/0.60          | ~ (v1_relat_1 @ X28))),
% 0.21/0.60      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.21/0.60  thf('48', plain,
% 0.21/0.60      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1))),
% 0.21/0.60      inference('sup-', [status(thm)], ['46', '47'])).
% 0.21/0.60  thf('49', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.60      inference('demod', [status(thm)], ['39', '40'])).
% 0.21/0.60  thf('50', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)),
% 0.21/0.60      inference('demod', [status(thm)], ['48', '49'])).
% 0.21/0.60  thf(t3_subset, axiom,
% 0.21/0.60    (![A:$i,B:$i]:
% 0.21/0.60     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.60  thf('51', plain,
% 0.21/0.60      (![X23 : $i, X25 : $i]:
% 0.21/0.60         ((m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X25)) | ~ (r1_tarski @ X23 @ X25))),
% 0.21/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.60  thf('52', plain,
% 0.21/0.60      ((m1_subset_1 @ (k2_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ sk_B_1))),
% 0.21/0.60      inference('sup-', [status(thm)], ['50', '51'])).
% 0.21/0.60  thf(l3_subset_1, axiom,
% 0.21/0.60    (![A:$i,B:$i]:
% 0.21/0.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.60       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.21/0.60  thf('53', plain,
% 0.21/0.60      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.60         (~ (r2_hidden @ X18 @ X19)
% 0.21/0.60          | (r2_hidden @ X18 @ X20)
% 0.21/0.60          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 0.21/0.60      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.21/0.60  thf('54', plain,
% 0.21/0.60      (![X0 : $i]:
% 0.21/0.60         ((r2_hidden @ X0 @ sk_B_1)
% 0.21/0.60          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_1)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.60  thf('55', plain,
% 0.21/0.60      ((((sk_C_1) = (k1_xboole_0))
% 0.21/0.60        | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B_1))),
% 0.21/0.60      inference('sup-', [status(thm)], ['43', '54'])).
% 0.21/0.60  thf('56', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_C_1 @ sk_A) @ sk_B_1)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('57', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.21/0.60      inference('clc', [status(thm)], ['55', '56'])).
% 0.21/0.60  thf(t60_relat_1, axiom,
% 0.21/0.60    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.60     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.60  thf('58', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.60      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.60  thf('59', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.21/0.60      inference('demod', [status(thm)], ['13', '57', '58'])).
% 0.21/0.60  thf(t1_boole, axiom,
% 0.21/0.60    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.60  thf('60', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.60      inference('cnf', [status(esa)], [t1_boole])).
% 0.21/0.60  thf(t49_zfmisc_1, axiom,
% 0.21/0.60    (![A:$i,B:$i]:
% 0.21/0.60     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.21/0.60  thf('61', plain,
% 0.21/0.60      (![X14 : $i, X15 : $i]:
% 0.21/0.60         ((k2_xboole_0 @ (k1_tarski @ X14) @ X15) != (k1_xboole_0))),
% 0.21/0.60      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.21/0.60  thf('62', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.21/0.60      inference('sup-', [status(thm)], ['60', '61'])).
% 0.21/0.60  thf('63', plain, ($false),
% 0.21/0.60      inference('simplify_reflect-', [status(thm)], ['59', '62'])).
% 0.21/0.60  
% 0.21/0.60  % SZS output end Refutation
% 0.21/0.60  
% 0.21/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
