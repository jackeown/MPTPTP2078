%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.m4DpzM64ZX

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:15 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 143 expanded)
%              Number of leaves         :   41 (  61 expanded)
%              Depth                    :   15
%              Number of atoms          :  598 (1532 expanded)
%              Number of equality atoms :   35 (  73 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(t190_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ B @ C )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
     => ~ ( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) )
          & ! [E: $i] :
              ( ( m1_subset_1 @ E @ B )
             => ( A
               != ( k1_funct_1 @ D @ E ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ B @ C )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
       => ~ ( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) )
            & ! [E: $i] :
                ( ( m1_subset_1 @ E @ B )
               => ( A
                 != ( k1_funct_1 @ D @ E ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t190_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k2_relset_1 @ sk_B_1 @ sk_C_2 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k2_relset_1 @ X28 @ X29 @ X27 )
        = ( k2_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_C_2 @ sk_D_2 )
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(d5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_relat_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ? [D: $i] :
                  ( ( C
                    = ( k1_funct_1 @ A @ D ) )
                  & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ( X14
       != ( k2_relat_1 @ X12 ) )
      | ( r2_hidden @ ( sk_D_1 @ X15 @ X12 ) @ ( k1_relat_1 @ X12 ) )
      | ~ ( r2_hidden @ X15 @ X14 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('6',plain,(
    ! [X12: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( r2_hidden @ X15 @ ( k2_relat_1 @ X12 ) )
      | ( r2_hidden @ ( sk_D_1 @ X15 @ X12 ) @ ( k1_relat_1 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_D_2 ) @ ( k1_relat_1 @ sk_D_2 ) )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    v1_funct_2 @ sk_D_2 @ sk_B_1 @ sk_C_2 ),
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

thf('9',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ( X32
        = ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('10',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ sk_C_2 @ sk_B_1 )
    | ( sk_B_1
      = ( k1_relset_1 @ sk_B_1 @ sk_C_2 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('12',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_2 ) ) ),
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

thf('15',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('16',plain,
    ( ( zip_tseitin_1 @ sk_D_2 @ sk_C_2 @ sk_B_1 )
    | ~ ( zip_tseitin_0 @ sk_C_2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ( zip_tseitin_1 @ sk_D_2 @ sk_C_2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('19',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('20',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v5_relat_1 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('21',plain,(
    v5_relat_1 @ sk_D_2 @ sk_C_2 ),
    inference('sup-',[status(thm)],['19','20'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('22',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v5_relat_1 @ X9 @ X10 )
      | ( r1_tarski @ ( k2_relat_1 @ X9 ) @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('23',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('25',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('26',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ sk_C_2 ),
    inference(demod,[status(thm)],['23','26'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('28',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_2 )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r2_hidden @ sk_A @ sk_C_2 ),
    inference('sup-',[status(thm)],['18','29'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('32',plain,(
    ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    zip_tseitin_1 @ sk_D_2 @ sk_C_2 @ sk_B_1 ),
    inference(clc,[status(thm)],['17','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('35',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k1_relset_1 @ X25 @ X26 @ X24 )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('36',plain,
    ( ( k1_relset_1 @ sk_B_1 @ sk_C_2 @ sk_D_2 )
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( sk_B_1
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['10','33','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('40',plain,(
    r2_hidden @ ( sk_D_1 @ sk_A @ sk_D_2 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['7','37','38','39'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('41',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ X7 @ X8 )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('42',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_A @ sk_D_2 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X38: $i] :
      ( ( sk_A
       != ( k1_funct_1 @ sk_D_2 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    sk_A
 != ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_A @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('46',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ( X14
       != ( k2_relat_1 @ X12 ) )
      | ( X15
        = ( k1_funct_1 @ X12 @ ( sk_D_1 @ X15 @ X12 ) ) )
      | ~ ( r2_hidden @ X15 @ X14 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('47',plain,(
    ! [X12: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( r2_hidden @ X15 @ ( k2_relat_1 @ X12 ) )
      | ( X15
        = ( k1_funct_1 @ X12 @ ( sk_D_1 @ X15 @ X12 ) ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( sk_A
      = ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_A @ sk_D_2 ) ) )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('51',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_A @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['44','51'])).

thf('53',plain,(
    $false ),
    inference(simplify,[status(thm)],['52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.m4DpzM64ZX
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:41:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.62  % Solved by: fo/fo7.sh
% 0.39/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.62  % done 134 iterations in 0.170s
% 0.39/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.62  % SZS output start Refutation
% 0.39/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.39/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.62  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.39/0.62  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.39/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.39/0.62  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.39/0.62  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.39/0.62  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.39/0.62  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.39/0.62  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.39/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.62  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.39/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.62  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.39/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.39/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.62  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.39/0.62  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.39/0.62  thf(t190_funct_2, conjecture,
% 0.39/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.62     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.39/0.62         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.39/0.62       ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.39/0.62            ( ![E:$i]:
% 0.39/0.62              ( ( m1_subset_1 @ E @ B ) => ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ))).
% 0.39/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.62    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.62        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.39/0.62            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.39/0.62          ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.39/0.62               ( ![E:$i]:
% 0.39/0.62                 ( ( m1_subset_1 @ E @ B ) =>
% 0.39/0.62                   ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) )),
% 0.39/0.62    inference('cnf.neg', [status(esa)], [t190_funct_2])).
% 0.39/0.62  thf('0', plain,
% 0.39/0.62      ((r2_hidden @ sk_A @ (k2_relset_1 @ sk_B_1 @ sk_C_2 @ sk_D_2))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('1', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_2)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(redefinition_k2_relset_1, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.62       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.39/0.62  thf('2', plain,
% 0.39/0.62      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.39/0.62         (((k2_relset_1 @ X28 @ X29 @ X27) = (k2_relat_1 @ X27))
% 0.39/0.62          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.39/0.62      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.39/0.62  thf('3', plain,
% 0.39/0.62      (((k2_relset_1 @ sk_B_1 @ sk_C_2 @ sk_D_2) = (k2_relat_1 @ sk_D_2))),
% 0.39/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.39/0.62  thf('4', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_2))),
% 0.39/0.62      inference('demod', [status(thm)], ['0', '3'])).
% 0.39/0.62  thf(d5_funct_1, axiom,
% 0.39/0.62    (![A:$i]:
% 0.39/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.39/0.62       ( ![B:$i]:
% 0.39/0.62         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.39/0.62           ( ![C:$i]:
% 0.39/0.62             ( ( r2_hidden @ C @ B ) <=>
% 0.39/0.62               ( ?[D:$i]:
% 0.39/0.62                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.39/0.62                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.39/0.62  thf('5', plain,
% 0.39/0.62      (![X12 : $i, X14 : $i, X15 : $i]:
% 0.39/0.62         (((X14) != (k2_relat_1 @ X12))
% 0.39/0.62          | (r2_hidden @ (sk_D_1 @ X15 @ X12) @ (k1_relat_1 @ X12))
% 0.39/0.62          | ~ (r2_hidden @ X15 @ X14)
% 0.39/0.62          | ~ (v1_funct_1 @ X12)
% 0.39/0.62          | ~ (v1_relat_1 @ X12))),
% 0.39/0.62      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.39/0.62  thf('6', plain,
% 0.39/0.62      (![X12 : $i, X15 : $i]:
% 0.39/0.62         (~ (v1_relat_1 @ X12)
% 0.39/0.62          | ~ (v1_funct_1 @ X12)
% 0.39/0.62          | ~ (r2_hidden @ X15 @ (k2_relat_1 @ X12))
% 0.39/0.62          | (r2_hidden @ (sk_D_1 @ X15 @ X12) @ (k1_relat_1 @ X12)))),
% 0.39/0.62      inference('simplify', [status(thm)], ['5'])).
% 0.39/0.62  thf('7', plain,
% 0.39/0.62      (((r2_hidden @ (sk_D_1 @ sk_A @ sk_D_2) @ (k1_relat_1 @ sk_D_2))
% 0.39/0.62        | ~ (v1_funct_1 @ sk_D_2)
% 0.39/0.62        | ~ (v1_relat_1 @ sk_D_2))),
% 0.39/0.62      inference('sup-', [status(thm)], ['4', '6'])).
% 0.39/0.62  thf('8', plain, ((v1_funct_2 @ sk_D_2 @ sk_B_1 @ sk_C_2)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(d1_funct_2, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.62       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.39/0.62           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.39/0.62             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.39/0.62         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.39/0.62           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.39/0.62             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.39/0.62  thf(zf_stmt_1, axiom,
% 0.39/0.62    (![C:$i,B:$i,A:$i]:
% 0.39/0.62     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.39/0.62       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.39/0.62  thf('9', plain,
% 0.39/0.62      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.39/0.62         (~ (v1_funct_2 @ X34 @ X32 @ X33)
% 0.39/0.62          | ((X32) = (k1_relset_1 @ X32 @ X33 @ X34))
% 0.39/0.62          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.62  thf('10', plain,
% 0.39/0.62      ((~ (zip_tseitin_1 @ sk_D_2 @ sk_C_2 @ sk_B_1)
% 0.39/0.62        | ((sk_B_1) = (k1_relset_1 @ sk_B_1 @ sk_C_2 @ sk_D_2)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['8', '9'])).
% 0.39/0.62  thf(zf_stmt_2, axiom,
% 0.39/0.62    (![B:$i,A:$i]:
% 0.39/0.62     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.39/0.62       ( zip_tseitin_0 @ B @ A ) ))).
% 0.39/0.62  thf('11', plain,
% 0.39/0.62      (![X30 : $i, X31 : $i]:
% 0.39/0.62         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.39/0.62  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.39/0.62  thf('12', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.62      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.39/0.62  thf('13', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.39/0.62      inference('sup+', [status(thm)], ['11', '12'])).
% 0.39/0.62  thf('14', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_2)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.39/0.62  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.39/0.62  thf(zf_stmt_5, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.62       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.39/0.62         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.39/0.62           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.39/0.62             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.39/0.62  thf('15', plain,
% 0.39/0.62      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.39/0.62         (~ (zip_tseitin_0 @ X35 @ X36)
% 0.39/0.62          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 0.39/0.62          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.39/0.62  thf('16', plain,
% 0.39/0.62      (((zip_tseitin_1 @ sk_D_2 @ sk_C_2 @ sk_B_1)
% 0.39/0.62        | ~ (zip_tseitin_0 @ sk_C_2 @ sk_B_1))),
% 0.39/0.62      inference('sup-', [status(thm)], ['14', '15'])).
% 0.39/0.62  thf('17', plain,
% 0.39/0.62      (((v1_xboole_0 @ sk_C_2) | (zip_tseitin_1 @ sk_D_2 @ sk_C_2 @ sk_B_1))),
% 0.39/0.62      inference('sup-', [status(thm)], ['13', '16'])).
% 0.39/0.62  thf('18', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_2))),
% 0.39/0.62      inference('demod', [status(thm)], ['0', '3'])).
% 0.39/0.62  thf('19', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_2)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(cc2_relset_1, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.62       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.39/0.62  thf('20', plain,
% 0.39/0.62      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.39/0.62         ((v5_relat_1 @ X21 @ X23)
% 0.39/0.62          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.39/0.62      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.39/0.62  thf('21', plain, ((v5_relat_1 @ sk_D_2 @ sk_C_2)),
% 0.39/0.62      inference('sup-', [status(thm)], ['19', '20'])).
% 0.39/0.62  thf(d19_relat_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( v1_relat_1 @ B ) =>
% 0.39/0.62       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.39/0.62  thf('22', plain,
% 0.39/0.62      (![X9 : $i, X10 : $i]:
% 0.39/0.62         (~ (v5_relat_1 @ X9 @ X10)
% 0.39/0.62          | (r1_tarski @ (k2_relat_1 @ X9) @ X10)
% 0.39/0.62          | ~ (v1_relat_1 @ X9))),
% 0.39/0.62      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.39/0.62  thf('23', plain,
% 0.39/0.62      ((~ (v1_relat_1 @ sk_D_2) | (r1_tarski @ (k2_relat_1 @ sk_D_2) @ sk_C_2))),
% 0.39/0.62      inference('sup-', [status(thm)], ['21', '22'])).
% 0.39/0.62  thf('24', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_2)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(cc1_relset_1, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.62       ( v1_relat_1 @ C ) ))).
% 0.39/0.62  thf('25', plain,
% 0.39/0.62      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.39/0.62         ((v1_relat_1 @ X18)
% 0.39/0.62          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.39/0.62      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.39/0.62  thf('26', plain, ((v1_relat_1 @ sk_D_2)),
% 0.39/0.62      inference('sup-', [status(thm)], ['24', '25'])).
% 0.39/0.62  thf('27', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_2) @ sk_C_2)),
% 0.39/0.62      inference('demod', [status(thm)], ['23', '26'])).
% 0.39/0.62  thf(d3_tarski, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( r1_tarski @ A @ B ) <=>
% 0.39/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.39/0.62  thf('28', plain,
% 0.39/0.62      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.39/0.62         (~ (r2_hidden @ X3 @ X4)
% 0.39/0.62          | (r2_hidden @ X3 @ X5)
% 0.39/0.62          | ~ (r1_tarski @ X4 @ X5))),
% 0.39/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.62  thf('29', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         ((r2_hidden @ X0 @ sk_C_2)
% 0.39/0.62          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_2)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['27', '28'])).
% 0.39/0.62  thf('30', plain, ((r2_hidden @ sk_A @ sk_C_2)),
% 0.39/0.62      inference('sup-', [status(thm)], ['18', '29'])).
% 0.39/0.62  thf(d1_xboole_0, axiom,
% 0.39/0.62    (![A:$i]:
% 0.39/0.62     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.39/0.62  thf('31', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.39/0.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.62  thf('32', plain, (~ (v1_xboole_0 @ sk_C_2)),
% 0.39/0.62      inference('sup-', [status(thm)], ['30', '31'])).
% 0.39/0.62  thf('33', plain, ((zip_tseitin_1 @ sk_D_2 @ sk_C_2 @ sk_B_1)),
% 0.39/0.62      inference('clc', [status(thm)], ['17', '32'])).
% 0.39/0.62  thf('34', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_2)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(redefinition_k1_relset_1, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.62       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.39/0.62  thf('35', plain,
% 0.39/0.62      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.39/0.62         (((k1_relset_1 @ X25 @ X26 @ X24) = (k1_relat_1 @ X24))
% 0.39/0.62          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.39/0.62      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.39/0.62  thf('36', plain,
% 0.39/0.62      (((k1_relset_1 @ sk_B_1 @ sk_C_2 @ sk_D_2) = (k1_relat_1 @ sk_D_2))),
% 0.39/0.62      inference('sup-', [status(thm)], ['34', '35'])).
% 0.39/0.62  thf('37', plain, (((sk_B_1) = (k1_relat_1 @ sk_D_2))),
% 0.39/0.62      inference('demod', [status(thm)], ['10', '33', '36'])).
% 0.39/0.62  thf('38', plain, ((v1_funct_1 @ sk_D_2)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('39', plain, ((v1_relat_1 @ sk_D_2)),
% 0.39/0.62      inference('sup-', [status(thm)], ['24', '25'])).
% 0.39/0.62  thf('40', plain, ((r2_hidden @ (sk_D_1 @ sk_A @ sk_D_2) @ sk_B_1)),
% 0.39/0.62      inference('demod', [status(thm)], ['7', '37', '38', '39'])).
% 0.39/0.62  thf(t1_subset, axiom,
% 0.39/0.62    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.39/0.62  thf('41', plain,
% 0.39/0.62      (![X7 : $i, X8 : $i]: ((m1_subset_1 @ X7 @ X8) | ~ (r2_hidden @ X7 @ X8))),
% 0.39/0.62      inference('cnf', [status(esa)], [t1_subset])).
% 0.39/0.62  thf('42', plain, ((m1_subset_1 @ (sk_D_1 @ sk_A @ sk_D_2) @ sk_B_1)),
% 0.39/0.62      inference('sup-', [status(thm)], ['40', '41'])).
% 0.39/0.62  thf('43', plain,
% 0.39/0.62      (![X38 : $i]:
% 0.39/0.62         (((sk_A) != (k1_funct_1 @ sk_D_2 @ X38))
% 0.39/0.62          | ~ (m1_subset_1 @ X38 @ sk_B_1))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('44', plain,
% 0.39/0.62      (((sk_A) != (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_A @ sk_D_2)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['42', '43'])).
% 0.39/0.62  thf('45', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_2))),
% 0.39/0.62      inference('demod', [status(thm)], ['0', '3'])).
% 0.39/0.62  thf('46', plain,
% 0.39/0.62      (![X12 : $i, X14 : $i, X15 : $i]:
% 0.39/0.62         (((X14) != (k2_relat_1 @ X12))
% 0.39/0.62          | ((X15) = (k1_funct_1 @ X12 @ (sk_D_1 @ X15 @ X12)))
% 0.39/0.62          | ~ (r2_hidden @ X15 @ X14)
% 0.39/0.62          | ~ (v1_funct_1 @ X12)
% 0.39/0.62          | ~ (v1_relat_1 @ X12))),
% 0.39/0.62      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.39/0.62  thf('47', plain,
% 0.39/0.62      (![X12 : $i, X15 : $i]:
% 0.39/0.62         (~ (v1_relat_1 @ X12)
% 0.39/0.62          | ~ (v1_funct_1 @ X12)
% 0.39/0.62          | ~ (r2_hidden @ X15 @ (k2_relat_1 @ X12))
% 0.39/0.62          | ((X15) = (k1_funct_1 @ X12 @ (sk_D_1 @ X15 @ X12))))),
% 0.39/0.62      inference('simplify', [status(thm)], ['46'])).
% 0.39/0.62  thf('48', plain,
% 0.39/0.62      ((((sk_A) = (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_A @ sk_D_2)))
% 0.39/0.62        | ~ (v1_funct_1 @ sk_D_2)
% 0.39/0.62        | ~ (v1_relat_1 @ sk_D_2))),
% 0.39/0.62      inference('sup-', [status(thm)], ['45', '47'])).
% 0.39/0.62  thf('49', plain, ((v1_funct_1 @ sk_D_2)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('50', plain, ((v1_relat_1 @ sk_D_2)),
% 0.39/0.62      inference('sup-', [status(thm)], ['24', '25'])).
% 0.39/0.62  thf('51', plain,
% 0.39/0.62      (((sk_A) = (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_A @ sk_D_2)))),
% 0.39/0.62      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.39/0.62  thf('52', plain, (((sk_A) != (sk_A))),
% 0.39/0.62      inference('demod', [status(thm)], ['44', '51'])).
% 0.39/0.62  thf('53', plain, ($false), inference('simplify', [status(thm)], ['52'])).
% 0.39/0.62  
% 0.39/0.62  % SZS output end Refutation
% 0.39/0.62  
% 0.46/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
