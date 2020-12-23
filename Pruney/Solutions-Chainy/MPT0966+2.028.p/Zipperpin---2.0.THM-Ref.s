%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.myRsMcmwdi

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:10 EST 2020

% Result     : Theorem 3.82s
% Output     : Refutation 3.82s
% Verified   : 
% Statistics : Number of formulae       :  197 (2503 expanded)
%              Number of leaves         :   38 ( 723 expanded)
%              Depth                    :   22
%              Number of atoms          : 1340 (31388 expanded)
%              Number of equality atoms :  121 (2505 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('1',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('2',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('4',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('5',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('7',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','7'])).

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

thf(zf_stmt_0,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('9',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( X32
       != ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(zf_stmt_1,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X31 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('13',plain,(
    ! [X30: $i] :
      ( zip_tseitin_0 @ X30 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['11','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ X0 @ k1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ X2 @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['0','19'])).

thf(t8_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ C )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_5,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C )
         => ( ( ( B = k1_xboole_0 )
              & ( A != k1_xboole_0 ) )
            | ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ C )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t8_funct_2])).

thf('21',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('22',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,
    ( ( ~ ( v1_xboole_0 @ sk_D )
      | ~ ( v1_xboole_0 @ sk_A ) )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('25',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('28',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('29',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('32',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ( X32
        = ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('35',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('36',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['33','36'])).

thf('38',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['30','37'])).

thf('39',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('40',plain,(
    ! [X30: $i] :
      ( zip_tseitin_0 @ X30 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( zip_tseitin_0 @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('46',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( X35 != k1_xboole_0 )
      | ( X36 = k1_xboole_0 )
      | ( v1_funct_2 @ X37 @ X36 @ X35 )
      | ( X37 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('47',plain,(
    ! [X36: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X36 @ k1_xboole_0 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('48',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('49',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('51',plain,(
    ! [X36: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X36 @ k1_xboole_0 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['47','49','50'])).

thf('52',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ( X32
        = ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0
        = ( k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_1 @ X0 @ k1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['45','56'])).

thf('58',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','57'])).

thf('59',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('60',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('62',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['61'])).

thf('63',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('64',plain,
    ( ~ ( v1_funct_1 @ sk_D )
   <= ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['21'])).

thf('65',plain,(
    v1_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['11','17'])).

thf('67',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('68',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['61'])).

thf('70',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('71',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['68','71'])).

thf('73',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('74',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('76',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf('79',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['61'])).

thf('80',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['21'])).

thf('81',plain,
    ( ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','82'])).

thf('84',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('85',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['67'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['61'])).

thf('88',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['21'])).

thf('89',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['68','71'])).

thf('92',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('93',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['21'])).

thf('95',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['61'])).

thf('96',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['65','83','93','94','95'])).

thf('97',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['62','96'])).

thf('98',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['60','97'])).

thf('99',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('100',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['98','103'])).

thf('105',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['23','104'])).

thf('106',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('107',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('108',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X26 @ X24 )
        = ( k2_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('109',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C ),
    inference(demod,[status(thm)],['106','109'])).

thf('111',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('112',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['111'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('113',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X27 ) @ X28 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X27 ) @ X29 )
      | ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['110','114'])).

thf('116',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['60','97'])).

thf('117',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('118',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('119',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('120',plain,(
    ! [X19: $i,X20: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('121',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['115','116','121'])).

thf('123',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['21'])).

thf('124',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['21'])).

thf('126',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['65','124','125'])).

thf('127',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['105','126'])).

thf('128',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['115','116','121'])).

thf('129',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('130',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('132',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_C ) @ sk_D )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_C )
      = sk_D ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('134',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['115','116','121'])).

thf('135',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('136',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['115','116','121'])).

thf('138',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('139',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['60','97'])).

thf('141',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( X32
       != ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['21'])).

thf('146',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['65','124','125'])).

thf('147',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['145','146'])).

thf('148',plain,(
    ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['144','147'])).

thf('149',plain,(
    ~ ( zip_tseitin_0 @ sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['136','148'])).

thf('150',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['133','149'])).

thf('151',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('152',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('153',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['133','149'])).

thf('154',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('155',plain,(
    k1_xboole_0 = sk_D ),
    inference(demod,[status(thm)],['132','150','151','152','153','154'])).

thf('156',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('157',plain,(
    $false ),
    inference(demod,[status(thm)],['127','155','156'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.myRsMcmwdi
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:03:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.82/3.98  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.82/3.98  % Solved by: fo/fo7.sh
% 3.82/3.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.82/3.98  % done 3365 iterations in 3.516s
% 3.82/3.98  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.82/3.98  % SZS output start Refutation
% 3.82/3.98  thf(sk_A_type, type, sk_A: $i).
% 3.82/3.98  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.82/3.98  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.82/3.98  thf(sk_B_1_type, type, sk_B_1: $i).
% 3.82/3.98  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.82/3.98  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 3.82/3.98  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.82/3.98  thf(sk_C_type, type, sk_C: $i).
% 3.82/3.98  thf(sk_D_type, type, sk_D: $i).
% 3.82/3.98  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.82/3.98  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.82/3.98  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.82/3.98  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.82/3.98  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.82/3.98  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.82/3.98  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.82/3.98  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.82/3.98  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.82/3.98  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.82/3.98  thf(l13_xboole_0, axiom,
% 3.82/3.98    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 3.82/3.98  thf('0', plain,
% 3.82/3.98      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 3.82/3.98      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.82/3.98  thf('1', plain,
% 3.82/3.98      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 3.82/3.98      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.82/3.98  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 3.82/3.98  thf('2', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 3.82/3.98      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.82/3.98  thf(t3_subset, axiom,
% 3.82/3.98    (![A:$i,B:$i]:
% 3.82/3.98     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.82/3.98  thf('3', plain,
% 3.82/3.98      (![X11 : $i, X13 : $i]:
% 3.82/3.98         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 3.82/3.98      inference('cnf', [status(esa)], [t3_subset])).
% 3.82/3.98  thf('4', plain,
% 3.82/3.98      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 3.82/3.98      inference('sup-', [status(thm)], ['2', '3'])).
% 3.82/3.98  thf(redefinition_k1_relset_1, axiom,
% 3.82/3.98    (![A:$i,B:$i,C:$i]:
% 3.82/3.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.82/3.98       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 3.82/3.98  thf('5', plain,
% 3.82/3.98      (![X21 : $i, X22 : $i, X23 : $i]:
% 3.82/3.98         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 3.82/3.98          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 3.82/3.98      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.82/3.98  thf('6', plain,
% 3.82/3.98      (![X0 : $i, X1 : $i]:
% 3.82/3.98         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 3.82/3.98      inference('sup-', [status(thm)], ['4', '5'])).
% 3.82/3.98  thf(t60_relat_1, axiom,
% 3.82/3.98    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 3.82/3.98     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 3.82/3.98  thf('7', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.82/3.98      inference('cnf', [status(esa)], [t60_relat_1])).
% 3.82/3.98  thf('8', plain,
% 3.82/3.98      (![X0 : $i, X1 : $i]:
% 3.82/3.98         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 3.82/3.98      inference('demod', [status(thm)], ['6', '7'])).
% 3.82/3.98  thf(d1_funct_2, axiom,
% 3.82/3.98    (![A:$i,B:$i,C:$i]:
% 3.82/3.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.82/3.98       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.82/3.98           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 3.82/3.98             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 3.82/3.98         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.82/3.98           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 3.82/3.98             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 3.82/3.98  thf(zf_stmt_0, axiom,
% 3.82/3.98    (![C:$i,B:$i,A:$i]:
% 3.82/3.98     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 3.82/3.98       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.82/3.98  thf('9', plain,
% 3.82/3.98      (![X32 : $i, X33 : $i, X34 : $i]:
% 3.82/3.98         (((X32) != (k1_relset_1 @ X32 @ X33 @ X34))
% 3.82/3.98          | (v1_funct_2 @ X34 @ X32 @ X33)
% 3.82/3.98          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 3.82/3.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.82/3.98  thf('10', plain,
% 3.82/3.98      (![X0 : $i, X1 : $i]:
% 3.82/3.98         (((X1) != (k1_xboole_0))
% 3.82/3.98          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 3.82/3.98          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 3.82/3.98      inference('sup-', [status(thm)], ['8', '9'])).
% 3.82/3.98  thf('11', plain,
% 3.82/3.98      (![X0 : $i]:
% 3.82/3.98         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 3.82/3.98          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 3.82/3.98      inference('simplify', [status(thm)], ['10'])).
% 3.82/3.98  thf(zf_stmt_1, axiom,
% 3.82/3.98    (![B:$i,A:$i]:
% 3.82/3.98     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.82/3.98       ( zip_tseitin_0 @ B @ A ) ))).
% 3.82/3.98  thf('12', plain,
% 3.82/3.98      (![X30 : $i, X31 : $i]:
% 3.82/3.98         ((zip_tseitin_0 @ X30 @ X31) | ((X31) != (k1_xboole_0)))),
% 3.82/3.98      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.82/3.98  thf('13', plain, (![X30 : $i]: (zip_tseitin_0 @ X30 @ k1_xboole_0)),
% 3.82/3.98      inference('simplify', [status(thm)], ['12'])).
% 3.82/3.98  thf('14', plain,
% 3.82/3.98      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 3.82/3.98      inference('sup-', [status(thm)], ['2', '3'])).
% 3.82/3.98  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 3.82/3.98  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 3.82/3.98  thf(zf_stmt_4, axiom,
% 3.82/3.98    (![A:$i,B:$i,C:$i]:
% 3.82/3.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.82/3.98       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 3.82/3.98         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.82/3.98           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 3.82/3.98             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 3.82/3.98  thf('15', plain,
% 3.82/3.98      (![X35 : $i, X36 : $i, X37 : $i]:
% 3.82/3.98         (~ (zip_tseitin_0 @ X35 @ X36)
% 3.82/3.98          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 3.82/3.98          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 3.82/3.98      inference('cnf', [status(esa)], [zf_stmt_4])).
% 3.82/3.98  thf('16', plain,
% 3.82/3.98      (![X0 : $i, X1 : $i]:
% 3.82/3.98         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 3.82/3.98      inference('sup-', [status(thm)], ['14', '15'])).
% 3.82/3.98  thf('17', plain,
% 3.82/3.98      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 3.82/3.98      inference('sup-', [status(thm)], ['13', '16'])).
% 3.82/3.98  thf('18', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 3.82/3.98      inference('demod', [status(thm)], ['11', '17'])).
% 3.82/3.98  thf('19', plain,
% 3.82/3.98      (![X0 : $i, X1 : $i]:
% 3.82/3.98         ((v1_funct_2 @ X0 @ k1_xboole_0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 3.82/3.98      inference('sup+', [status(thm)], ['1', '18'])).
% 3.82/3.98  thf('20', plain,
% 3.82/3.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.82/3.98         ((v1_funct_2 @ X2 @ X0 @ X1)
% 3.82/3.98          | ~ (v1_xboole_0 @ X0)
% 3.82/3.98          | ~ (v1_xboole_0 @ X2))),
% 3.82/3.98      inference('sup+', [status(thm)], ['0', '19'])).
% 3.82/3.98  thf(t8_funct_2, conjecture,
% 3.82/3.98    (![A:$i,B:$i,C:$i,D:$i]:
% 3.82/3.98     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.82/3.98         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.82/3.98       ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 3.82/3.98         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 3.82/3.98           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 3.82/3.98             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 3.82/3.98  thf(zf_stmt_5, negated_conjecture,
% 3.82/3.98    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 3.82/3.98        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.82/3.98            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.82/3.98          ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 3.82/3.98            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 3.82/3.98              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 3.82/3.98                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 3.82/3.98    inference('cnf.neg', [status(esa)], [t8_funct_2])).
% 3.82/3.98  thf('21', plain,
% 3.82/3.98      ((~ (v1_funct_1 @ sk_D)
% 3.82/3.98        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)
% 3.82/3.98        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 3.82/3.98      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.82/3.98  thf('22', plain,
% 3.82/3.98      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 3.82/3.98         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 3.82/3.98      inference('split', [status(esa)], ['21'])).
% 3.82/3.98  thf('23', plain,
% 3.82/3.98      (((~ (v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_A)))
% 3.82/3.98         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 3.82/3.98      inference('sup-', [status(thm)], ['20', '22'])).
% 3.82/3.98  thf('24', plain,
% 3.82/3.98      (![X30 : $i, X31 : $i]:
% 3.82/3.98         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 3.82/3.98      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.82/3.98  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.82/3.98  thf('25', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.82/3.98      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.82/3.98  thf('26', plain,
% 3.82/3.98      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 3.82/3.98      inference('sup+', [status(thm)], ['24', '25'])).
% 3.82/3.98  thf('27', plain,
% 3.82/3.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.82/3.98      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.82/3.98  thf('28', plain,
% 3.82/3.98      (![X35 : $i, X36 : $i, X37 : $i]:
% 3.82/3.98         (~ (zip_tseitin_0 @ X35 @ X36)
% 3.82/3.98          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 3.82/3.98          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 3.82/3.98      inference('cnf', [status(esa)], [zf_stmt_4])).
% 3.82/3.98  thf('29', plain,
% 3.82/3.98      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 3.82/3.98        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 3.82/3.98      inference('sup-', [status(thm)], ['27', '28'])).
% 3.82/3.98  thf('30', plain,
% 3.82/3.98      (((v1_xboole_0 @ sk_B_1) | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 3.82/3.98      inference('sup-', [status(thm)], ['26', '29'])).
% 3.82/3.98  thf('31', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 3.82/3.98      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.82/3.98  thf('32', plain,
% 3.82/3.98      (![X32 : $i, X33 : $i, X34 : $i]:
% 3.82/3.98         (~ (v1_funct_2 @ X34 @ X32 @ X33)
% 3.82/3.98          | ((X32) = (k1_relset_1 @ X32 @ X33 @ X34))
% 3.82/3.98          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 3.82/3.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.82/3.98  thf('33', plain,
% 3.82/3.98      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 3.82/3.98        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 3.82/3.98      inference('sup-', [status(thm)], ['31', '32'])).
% 3.82/3.98  thf('34', plain,
% 3.82/3.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.82/3.98      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.82/3.98  thf('35', plain,
% 3.82/3.98      (![X21 : $i, X22 : $i, X23 : $i]:
% 3.82/3.98         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 3.82/3.98          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 3.82/3.98      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.82/3.98  thf('36', plain,
% 3.82/3.98      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 3.82/3.98      inference('sup-', [status(thm)], ['34', '35'])).
% 3.82/3.98  thf('37', plain,
% 3.82/3.98      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 3.82/3.98        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.82/3.98      inference('demod', [status(thm)], ['33', '36'])).
% 3.82/3.98  thf('38', plain, (((v1_xboole_0 @ sk_B_1) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.82/3.98      inference('sup-', [status(thm)], ['30', '37'])).
% 3.82/3.98  thf('39', plain,
% 3.82/3.98      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 3.82/3.98      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.82/3.98  thf('40', plain, (![X30 : $i]: (zip_tseitin_0 @ X30 @ k1_xboole_0)),
% 3.82/3.98      inference('simplify', [status(thm)], ['12'])).
% 3.82/3.98  thf('41', plain,
% 3.82/3.98      (![X0 : $i, X1 : $i]: ((zip_tseitin_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 3.82/3.98      inference('sup+', [status(thm)], ['39', '40'])).
% 3.82/3.98  thf('42', plain,
% 3.82/3.98      (![X0 : $i]:
% 3.82/3.98         (((sk_A) = (k1_relat_1 @ sk_D)) | (zip_tseitin_0 @ X0 @ sk_B_1))),
% 3.82/3.98      inference('sup-', [status(thm)], ['38', '41'])).
% 3.82/3.98  thf('43', plain,
% 3.82/3.98      (![X0 : $i, X1 : $i]:
% 3.82/3.98         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 3.82/3.98      inference('sup-', [status(thm)], ['14', '15'])).
% 3.82/3.98  thf('44', plain,
% 3.82/3.98      (![X0 : $i]:
% 3.82/3.98         (((sk_A) = (k1_relat_1 @ sk_D))
% 3.82/3.98          | (zip_tseitin_1 @ k1_xboole_0 @ X0 @ sk_B_1))),
% 3.82/3.98      inference('sup-', [status(thm)], ['42', '43'])).
% 3.82/3.98  thf('45', plain,
% 3.82/3.98      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 3.82/3.98      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.82/3.98  thf('46', plain,
% 3.82/3.98      (![X35 : $i, X36 : $i, X37 : $i]:
% 3.82/3.98         (((X35) != (k1_xboole_0))
% 3.82/3.98          | ((X36) = (k1_xboole_0))
% 3.82/3.98          | (v1_funct_2 @ X37 @ X36 @ X35)
% 3.82/3.98          | ((X37) != (k1_xboole_0))
% 3.82/3.98          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 3.82/3.98      inference('cnf', [status(esa)], [zf_stmt_4])).
% 3.82/3.98  thf('47', plain,
% 3.82/3.98      (![X36 : $i]:
% 3.82/3.98         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 3.82/3.98             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ k1_xboole_0)))
% 3.82/3.98          | (v1_funct_2 @ k1_xboole_0 @ X36 @ k1_xboole_0)
% 3.82/3.98          | ((X36) = (k1_xboole_0)))),
% 3.82/3.98      inference('simplify', [status(thm)], ['46'])).
% 3.82/3.98  thf(t113_zfmisc_1, axiom,
% 3.82/3.98    (![A:$i,B:$i]:
% 3.82/3.98     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 3.82/3.98       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 3.82/3.98  thf('48', plain,
% 3.82/3.98      (![X9 : $i, X10 : $i]:
% 3.82/3.98         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X10) != (k1_xboole_0)))),
% 3.82/3.98      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.82/3.98  thf('49', plain,
% 3.82/3.98      (![X9 : $i]: ((k2_zfmisc_1 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 3.82/3.98      inference('simplify', [status(thm)], ['48'])).
% 3.82/3.98  thf('50', plain,
% 3.82/3.98      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 3.82/3.98      inference('sup-', [status(thm)], ['2', '3'])).
% 3.82/3.98  thf('51', plain,
% 3.82/3.98      (![X36 : $i]:
% 3.82/3.98         ((v1_funct_2 @ k1_xboole_0 @ X36 @ k1_xboole_0)
% 3.82/3.98          | ((X36) = (k1_xboole_0)))),
% 3.82/3.98      inference('demod', [status(thm)], ['47', '49', '50'])).
% 3.82/3.98  thf('52', plain,
% 3.82/3.98      (![X32 : $i, X33 : $i, X34 : $i]:
% 3.82/3.98         (~ (v1_funct_2 @ X34 @ X32 @ X33)
% 3.82/3.98          | ((X32) = (k1_relset_1 @ X32 @ X33 @ X34))
% 3.82/3.98          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 3.82/3.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.82/3.98  thf('53', plain,
% 3.82/3.98      (![X0 : $i]:
% 3.82/3.98         (((X0) = (k1_xboole_0))
% 3.82/3.98          | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 3.82/3.98          | ((X0) = (k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0)))),
% 3.82/3.98      inference('sup-', [status(thm)], ['51', '52'])).
% 3.82/3.98  thf('54', plain,
% 3.82/3.98      (![X0 : $i, X1 : $i]:
% 3.82/3.98         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 3.82/3.98      inference('demod', [status(thm)], ['6', '7'])).
% 3.82/3.98  thf('55', plain,
% 3.82/3.98      (![X0 : $i]:
% 3.82/3.98         (((X0) = (k1_xboole_0))
% 3.82/3.98          | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 3.82/3.98          | ((X0) = (k1_xboole_0)))),
% 3.82/3.98      inference('demod', [status(thm)], ['53', '54'])).
% 3.82/3.98  thf('56', plain,
% 3.82/3.98      (![X0 : $i]:
% 3.82/3.98         (~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 3.82/3.98          | ((X0) = (k1_xboole_0)))),
% 3.82/3.98      inference('simplify', [status(thm)], ['55'])).
% 3.82/3.98  thf('57', plain,
% 3.82/3.98      (![X0 : $i, X1 : $i]:
% 3.82/3.98         (~ (zip_tseitin_1 @ X0 @ k1_xboole_0 @ X1)
% 3.82/3.98          | ~ (v1_xboole_0 @ X0)
% 3.82/3.98          | ((X1) = (k1_xboole_0)))),
% 3.82/3.98      inference('sup-', [status(thm)], ['45', '56'])).
% 3.82/3.98  thf('58', plain,
% 3.82/3.98      ((((sk_A) = (k1_relat_1 @ sk_D))
% 3.82/3.98        | ((sk_B_1) = (k1_xboole_0))
% 3.82/3.98        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 3.82/3.98      inference('sup-', [status(thm)], ['44', '57'])).
% 3.82/3.98  thf('59', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.82/3.98      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.82/3.98  thf('60', plain,
% 3.82/3.98      ((((sk_A) = (k1_relat_1 @ sk_D)) | ((sk_B_1) = (k1_xboole_0)))),
% 3.82/3.98      inference('demod', [status(thm)], ['58', '59'])).
% 3.82/3.98  thf('61', plain, ((((sk_B_1) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 3.82/3.98      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.82/3.98  thf('62', plain,
% 3.82/3.98      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 3.82/3.98      inference('split', [status(esa)], ['61'])).
% 3.82/3.98  thf('63', plain, ((v1_funct_1 @ sk_D)),
% 3.82/3.98      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.82/3.98  thf('64', plain, ((~ (v1_funct_1 @ sk_D)) <= (~ ((v1_funct_1 @ sk_D)))),
% 3.82/3.98      inference('split', [status(esa)], ['21'])).
% 3.82/3.98  thf('65', plain, (((v1_funct_1 @ sk_D))),
% 3.82/3.98      inference('sup-', [status(thm)], ['63', '64'])).
% 3.82/3.98  thf('66', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 3.82/3.98      inference('demod', [status(thm)], ['11', '17'])).
% 3.82/3.98  thf('67', plain,
% 3.82/3.98      (![X9 : $i, X10 : $i]:
% 3.82/3.98         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 3.82/3.98      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.82/3.98  thf('68', plain,
% 3.82/3.98      (![X10 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 3.82/3.98      inference('simplify', [status(thm)], ['67'])).
% 3.82/3.98  thf('69', plain,
% 3.82/3.98      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.82/3.98      inference('split', [status(esa)], ['61'])).
% 3.82/3.98  thf('70', plain,
% 3.82/3.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.82/3.98      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.82/3.98  thf('71', plain,
% 3.82/3.98      (((m1_subset_1 @ sk_D @ 
% 3.82/3.98         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 3.82/3.98         <= ((((sk_A) = (k1_xboole_0))))),
% 3.82/3.98      inference('sup+', [status(thm)], ['69', '70'])).
% 3.82/3.98  thf('72', plain,
% 3.82/3.98      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 3.82/3.98         <= ((((sk_A) = (k1_xboole_0))))),
% 3.82/3.98      inference('sup+', [status(thm)], ['68', '71'])).
% 3.82/3.98  thf('73', plain,
% 3.82/3.98      (![X11 : $i, X12 : $i]:
% 3.82/3.98         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 3.82/3.98      inference('cnf', [status(esa)], [t3_subset])).
% 3.82/3.98  thf('74', plain,
% 3.82/3.98      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 3.82/3.98      inference('sup-', [status(thm)], ['72', '73'])).
% 3.82/3.98  thf('75', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 3.82/3.98      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.82/3.98  thf(d10_xboole_0, axiom,
% 3.82/3.98    (![A:$i,B:$i]:
% 3.82/3.98     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.82/3.98  thf('76', plain,
% 3.82/3.98      (![X4 : $i, X6 : $i]:
% 3.82/3.98         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 3.82/3.98      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.82/3.98  thf('77', plain,
% 3.82/3.98      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 3.82/3.98      inference('sup-', [status(thm)], ['75', '76'])).
% 3.82/3.98  thf('78', plain,
% 3.82/3.98      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.82/3.98      inference('sup-', [status(thm)], ['74', '77'])).
% 3.82/3.98  thf('79', plain,
% 3.82/3.98      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.82/3.98      inference('split', [status(esa)], ['61'])).
% 3.82/3.98  thf('80', plain,
% 3.82/3.98      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 3.82/3.98         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 3.82/3.98      inference('split', [status(esa)], ['21'])).
% 3.82/3.98  thf('81', plain,
% 3.82/3.98      ((~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C))
% 3.82/3.98         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 3.82/3.98      inference('sup-', [status(thm)], ['79', '80'])).
% 3.82/3.98  thf('82', plain,
% 3.82/3.98      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C))
% 3.82/3.98         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 3.82/3.98      inference('sup-', [status(thm)], ['78', '81'])).
% 3.82/3.98  thf('83', plain,
% 3.82/3.98      (((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | ~ (((sk_A) = (k1_xboole_0)))),
% 3.82/3.98      inference('sup-', [status(thm)], ['66', '82'])).
% 3.82/3.98  thf('84', plain,
% 3.82/3.98      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 3.82/3.98      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.82/3.98  thf('85', plain,
% 3.82/3.98      (![X10 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 3.82/3.98      inference('simplify', [status(thm)], ['67'])).
% 3.82/3.98  thf('86', plain,
% 3.82/3.98      (![X0 : $i, X1 : $i]:
% 3.82/3.98         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.82/3.98      inference('sup+', [status(thm)], ['84', '85'])).
% 3.82/3.98  thf('87', plain,
% 3.82/3.98      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 3.82/3.98      inference('split', [status(esa)], ['61'])).
% 3.82/3.98  thf('88', plain,
% 3.82/3.98      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 3.82/3.98         <= (~
% 3.82/3.98             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 3.82/3.98      inference('split', [status(esa)], ['21'])).
% 3.82/3.98  thf('89', plain,
% 3.82/3.98      ((~ (m1_subset_1 @ sk_D @ 
% 3.82/3.98           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C))))
% 3.82/3.98         <= (~
% 3.82/3.98             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) & 
% 3.82/3.98             (((sk_A) = (k1_xboole_0))))),
% 3.82/3.98      inference('sup-', [status(thm)], ['87', '88'])).
% 3.82/3.98  thf('90', plain,
% 3.82/3.98      (((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0))
% 3.82/3.98         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 3.82/3.98         <= (~
% 3.82/3.98             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) & 
% 3.82/3.98             (((sk_A) = (k1_xboole_0))))),
% 3.82/3.98      inference('sup-', [status(thm)], ['86', '89'])).
% 3.82/3.98  thf('91', plain,
% 3.82/3.98      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 3.82/3.98         <= ((((sk_A) = (k1_xboole_0))))),
% 3.82/3.98      inference('sup+', [status(thm)], ['68', '71'])).
% 3.82/3.98  thf('92', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.82/3.98      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.82/3.98  thf('93', plain,
% 3.82/3.98      (~ (((sk_A) = (k1_xboole_0))) | 
% 3.82/3.98       ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 3.82/3.98      inference('demod', [status(thm)], ['90', '91', '92'])).
% 3.82/3.98  thf('94', plain,
% 3.82/3.98      (~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 3.82/3.98       ~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | ~ ((v1_funct_1 @ sk_D))),
% 3.82/3.98      inference('split', [status(esa)], ['21'])).
% 3.82/3.98  thf('95', plain,
% 3.82/3.98      (~ (((sk_B_1) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 3.82/3.98      inference('split', [status(esa)], ['61'])).
% 3.82/3.98  thf('96', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 3.82/3.98      inference('sat_resolution*', [status(thm)],
% 3.82/3.98                ['65', '83', '93', '94', '95'])).
% 3.82/3.98  thf('97', plain, (((sk_B_1) != (k1_xboole_0))),
% 3.82/3.98      inference('simpl_trail', [status(thm)], ['62', '96'])).
% 3.82/3.98  thf('98', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 3.82/3.98      inference('simplify_reflect-', [status(thm)], ['60', '97'])).
% 3.82/3.98  thf('99', plain,
% 3.82/3.98      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 3.82/3.98      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.82/3.98  thf('100', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.82/3.98      inference('cnf', [status(esa)], [t60_relat_1])).
% 3.82/3.98  thf('101', plain,
% 3.82/3.98      (![X0 : $i]: (((k1_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.82/3.98      inference('sup+', [status(thm)], ['99', '100'])).
% 3.82/3.98  thf('102', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.82/3.98      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.82/3.98  thf('103', plain,
% 3.82/3.98      (![X0 : $i]: ((v1_xboole_0 @ (k1_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 3.82/3.98      inference('sup+', [status(thm)], ['101', '102'])).
% 3.82/3.98  thf('104', plain, (((v1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ sk_D))),
% 3.82/3.98      inference('sup+', [status(thm)], ['98', '103'])).
% 3.82/3.98  thf('105', plain,
% 3.82/3.98      ((~ (v1_xboole_0 @ sk_D)) <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 3.82/3.98      inference('clc', [status(thm)], ['23', '104'])).
% 3.82/3.98  thf('106', plain,
% 3.82/3.98      ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_D) @ sk_C)),
% 3.82/3.98      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.82/3.98  thf('107', plain,
% 3.82/3.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.82/3.98      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.82/3.98  thf(redefinition_k2_relset_1, axiom,
% 3.82/3.98    (![A:$i,B:$i,C:$i]:
% 3.82/3.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.82/3.98       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 3.82/3.98  thf('108', plain,
% 3.82/3.98      (![X24 : $i, X25 : $i, X26 : $i]:
% 3.82/3.98         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 3.82/3.98          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 3.82/3.98      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.82/3.98  thf('109', plain,
% 3.82/3.98      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 3.82/3.98      inference('sup-', [status(thm)], ['107', '108'])).
% 3.82/3.98  thf('110', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C)),
% 3.82/3.98      inference('demod', [status(thm)], ['106', '109'])).
% 3.82/3.98  thf('111', plain,
% 3.82/3.98      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 3.82/3.98      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.82/3.98  thf('112', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 3.82/3.98      inference('simplify', [status(thm)], ['111'])).
% 3.82/3.98  thf(t11_relset_1, axiom,
% 3.82/3.98    (![A:$i,B:$i,C:$i]:
% 3.82/3.98     ( ( v1_relat_1 @ C ) =>
% 3.82/3.98       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 3.82/3.98           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 3.82/3.98         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 3.82/3.98  thf('113', plain,
% 3.82/3.98      (![X27 : $i, X28 : $i, X29 : $i]:
% 3.82/3.98         (~ (r1_tarski @ (k1_relat_1 @ X27) @ X28)
% 3.82/3.98          | ~ (r1_tarski @ (k2_relat_1 @ X27) @ X29)
% 3.82/3.98          | (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 3.82/3.98          | ~ (v1_relat_1 @ X27))),
% 3.82/3.98      inference('cnf', [status(esa)], [t11_relset_1])).
% 3.82/3.98  thf('114', plain,
% 3.82/3.98      (![X0 : $i, X1 : $i]:
% 3.82/3.98         (~ (v1_relat_1 @ X0)
% 3.82/3.98          | (m1_subset_1 @ X0 @ 
% 3.82/3.98             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 3.82/3.98          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 3.82/3.98      inference('sup-', [status(thm)], ['112', '113'])).
% 3.82/3.98  thf('115', plain,
% 3.82/3.98      (((m1_subset_1 @ sk_D @ 
% 3.82/3.98         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_C)))
% 3.82/3.98        | ~ (v1_relat_1 @ sk_D))),
% 3.82/3.98      inference('sup-', [status(thm)], ['110', '114'])).
% 3.82/3.98  thf('116', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 3.82/3.98      inference('simplify_reflect-', [status(thm)], ['60', '97'])).
% 3.82/3.98  thf('117', plain,
% 3.82/3.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.82/3.98      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.82/3.98  thf(cc2_relat_1, axiom,
% 3.82/3.98    (![A:$i]:
% 3.82/3.98     ( ( v1_relat_1 @ A ) =>
% 3.82/3.98       ( ![B:$i]:
% 3.82/3.98         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 3.82/3.98  thf('118', plain,
% 3.82/3.98      (![X17 : $i, X18 : $i]:
% 3.82/3.98         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 3.82/3.98          | (v1_relat_1 @ X17)
% 3.82/3.98          | ~ (v1_relat_1 @ X18))),
% 3.82/3.98      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.82/3.98  thf('119', plain,
% 3.82/3.98      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_D))),
% 3.82/3.98      inference('sup-', [status(thm)], ['117', '118'])).
% 3.82/3.98  thf(fc6_relat_1, axiom,
% 3.82/3.98    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 3.82/3.98  thf('120', plain,
% 3.82/3.98      (![X19 : $i, X20 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X19 @ X20))),
% 3.82/3.98      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.82/3.98  thf('121', plain, ((v1_relat_1 @ sk_D)),
% 3.82/3.98      inference('demod', [status(thm)], ['119', '120'])).
% 3.82/3.98  thf('122', plain,
% 3.82/3.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 3.82/3.98      inference('demod', [status(thm)], ['115', '116', '121'])).
% 3.82/3.98  thf('123', plain,
% 3.82/3.98      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 3.82/3.98         <= (~
% 3.82/3.98             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 3.82/3.98      inference('split', [status(esa)], ['21'])).
% 3.82/3.98  thf('124', plain,
% 3.82/3.98      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 3.82/3.98      inference('sup-', [status(thm)], ['122', '123'])).
% 3.82/3.98  thf('125', plain,
% 3.82/3.98      (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | 
% 3.82/3.98       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 3.82/3.98       ~ ((v1_funct_1 @ sk_D))),
% 3.82/3.98      inference('split', [status(esa)], ['21'])).
% 3.82/3.98  thf('126', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 3.82/3.98      inference('sat_resolution*', [status(thm)], ['65', '124', '125'])).
% 3.82/3.98  thf('127', plain, (~ (v1_xboole_0 @ sk_D)),
% 3.82/3.98      inference('simpl_trail', [status(thm)], ['105', '126'])).
% 3.82/3.98  thf('128', plain,
% 3.82/3.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 3.82/3.98      inference('demod', [status(thm)], ['115', '116', '121'])).
% 3.82/3.98  thf('129', plain,
% 3.82/3.98      (![X11 : $i, X12 : $i]:
% 3.82/3.98         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 3.82/3.98      inference('cnf', [status(esa)], [t3_subset])).
% 3.82/3.98  thf('130', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_C))),
% 3.82/3.98      inference('sup-', [status(thm)], ['128', '129'])).
% 3.82/3.98  thf('131', plain,
% 3.82/3.98      (![X4 : $i, X6 : $i]:
% 3.82/3.98         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 3.82/3.98      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.82/3.98  thf('132', plain,
% 3.82/3.98      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_C) @ sk_D)
% 3.82/3.98        | ((k2_zfmisc_1 @ sk_A @ sk_C) = (sk_D)))),
% 3.82/3.98      inference('sup-', [status(thm)], ['130', '131'])).
% 3.82/3.98  thf('133', plain,
% 3.82/3.98      (![X30 : $i, X31 : $i]:
% 3.82/3.98         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 3.82/3.98      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.82/3.98  thf('134', plain,
% 3.82/3.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 3.82/3.98      inference('demod', [status(thm)], ['115', '116', '121'])).
% 3.82/3.98  thf('135', plain,
% 3.82/3.98      (![X35 : $i, X36 : $i, X37 : $i]:
% 3.82/3.98         (~ (zip_tseitin_0 @ X35 @ X36)
% 3.82/3.98          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 3.82/3.98          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 3.82/3.98      inference('cnf', [status(esa)], [zf_stmt_4])).
% 3.82/3.98  thf('136', plain,
% 3.82/3.98      (((zip_tseitin_1 @ sk_D @ sk_C @ sk_A) | ~ (zip_tseitin_0 @ sk_C @ sk_A))),
% 3.82/3.98      inference('sup-', [status(thm)], ['134', '135'])).
% 3.82/3.98  thf('137', plain,
% 3.82/3.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 3.82/3.98      inference('demod', [status(thm)], ['115', '116', '121'])).
% 3.82/3.98  thf('138', plain,
% 3.82/3.98      (![X21 : $i, X22 : $i, X23 : $i]:
% 3.82/3.98         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 3.82/3.98          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 3.82/3.98      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.82/3.98  thf('139', plain,
% 3.82/3.98      (((k1_relset_1 @ sk_A @ sk_C @ sk_D) = (k1_relat_1 @ sk_D))),
% 3.82/3.98      inference('sup-', [status(thm)], ['137', '138'])).
% 3.82/3.98  thf('140', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 3.82/3.98      inference('simplify_reflect-', [status(thm)], ['60', '97'])).
% 3.82/3.98  thf('141', plain, (((k1_relset_1 @ sk_A @ sk_C @ sk_D) = (sk_A))),
% 3.82/3.98      inference('demod', [status(thm)], ['139', '140'])).
% 3.82/3.98  thf('142', plain,
% 3.82/3.98      (![X32 : $i, X33 : $i, X34 : $i]:
% 3.82/3.98         (((X32) != (k1_relset_1 @ X32 @ X33 @ X34))
% 3.82/3.98          | (v1_funct_2 @ X34 @ X32 @ X33)
% 3.82/3.98          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 3.82/3.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.82/3.98  thf('143', plain,
% 3.82/3.98      ((((sk_A) != (sk_A))
% 3.82/3.98        | ~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A)
% 3.82/3.98        | (v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 3.82/3.98      inference('sup-', [status(thm)], ['141', '142'])).
% 3.82/3.98  thf('144', plain,
% 3.82/3.98      (((v1_funct_2 @ sk_D @ sk_A @ sk_C)
% 3.82/3.98        | ~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A))),
% 3.82/3.98      inference('simplify', [status(thm)], ['143'])).
% 3.82/3.98  thf('145', plain,
% 3.82/3.98      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 3.82/3.98         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 3.82/3.98      inference('split', [status(esa)], ['21'])).
% 3.82/3.98  thf('146', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 3.82/3.98      inference('sat_resolution*', [status(thm)], ['65', '124', '125'])).
% 3.82/3.98  thf('147', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)),
% 3.82/3.98      inference('simpl_trail', [status(thm)], ['145', '146'])).
% 3.82/3.98  thf('148', plain, (~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A)),
% 3.82/3.98      inference('clc', [status(thm)], ['144', '147'])).
% 3.82/3.98  thf('149', plain, (~ (zip_tseitin_0 @ sk_C @ sk_A)),
% 3.82/3.98      inference('clc', [status(thm)], ['136', '148'])).
% 3.82/3.98  thf('150', plain, (((sk_C) = (k1_xboole_0))),
% 3.82/3.98      inference('sup-', [status(thm)], ['133', '149'])).
% 3.82/3.98  thf('151', plain,
% 3.82/3.98      (![X9 : $i]: ((k2_zfmisc_1 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 3.82/3.98      inference('simplify', [status(thm)], ['48'])).
% 3.82/3.98  thf('152', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 3.82/3.98      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.82/3.98  thf('153', plain, (((sk_C) = (k1_xboole_0))),
% 3.82/3.98      inference('sup-', [status(thm)], ['133', '149'])).
% 3.82/3.98  thf('154', plain,
% 3.82/3.98      (![X9 : $i]: ((k2_zfmisc_1 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 3.82/3.98      inference('simplify', [status(thm)], ['48'])).
% 3.82/3.98  thf('155', plain, (((k1_xboole_0) = (sk_D))),
% 3.82/3.98      inference('demod', [status(thm)],
% 3.82/3.98                ['132', '150', '151', '152', '153', '154'])).
% 3.82/3.98  thf('156', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.82/3.98      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.82/3.98  thf('157', plain, ($false),
% 3.82/3.98      inference('demod', [status(thm)], ['127', '155', '156'])).
% 3.82/3.98  
% 3.82/3.98  % SZS output end Refutation
% 3.82/3.98  
% 3.82/3.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
