%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eFdqW8wHiP

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:55 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  124 (1016 expanded)
%              Number of leaves         :   34 ( 301 expanded)
%              Depth                    :   24
%              Number of atoms          : 1068 (15249 expanded)
%              Number of equality atoms :   96 (1106 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t77_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( v2_funct_1 @ B )
      <=> ! [C: $i,D: $i] :
            ( ( ( r2_hidden @ C @ A )
              & ( r2_hidden @ D @ A )
              & ( ( k1_funct_1 @ B @ C )
                = ( k1_funct_1 @ B @ D ) ) )
           => ( C = D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ( ( v2_funct_1 @ B )
        <=> ! [C: $i,D: $i] :
              ( ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ D @ A )
                & ( ( k1_funct_1 @ B @ C )
                  = ( k1_funct_1 @ B @ D ) ) )
             => ( C = D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t77_funct_2])).

thf('0',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_A )
   <= ( r2_hidden @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X20: $i,X21: $i] :
      ( ( X21 = X20 )
      | ( ( k1_funct_1 @ sk_B_1 @ X21 )
       != ( k1_funct_1 @ sk_B_1 @ X20 ) )
      | ~ ( r2_hidden @ X20 @ sk_A )
      | ~ ( r2_hidden @ X21 @ sk_A )
      | ( v2_funct_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ! [X20: $i,X21: $i] :
        ( ( X21 = X20 )
        | ( ( k1_funct_1 @ sk_B_1 @ X21 )
         != ( k1_funct_1 @ sk_B_1 @ X20 ) )
        | ~ ( r2_hidden @ X20 @ sk_A )
        | ~ ( r2_hidden @ X21 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_funct_2 @ X16 @ X14 @ X15 )
      | ( X14
        = ( k1_relset_1 @ X14 @ X15 @ X16 ) )
      | ~ ( zip_tseitin_1 @ X16 @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,
    ( ~ ( zip_tseitin_1 @ sk_B_1 @ sk_A @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_0 @ X17 @ X18 )
      | ( zip_tseitin_1 @ X19 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('9',plain,
    ( ( zip_tseitin_1 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 )
      | ( X12 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('11',plain,(
    ! [X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 )
      | ( X13 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('12',plain,(
    ! [X12: $i] :
      ( zip_tseitin_0 @ X12 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['13'])).

thf('15',plain,(
    zip_tseitin_1 @ sk_B_1 @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['9','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('17',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('18',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B_1 )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['6','15','18'])).

thf(d8_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
      <=> ! [B: $i,C: $i] :
            ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
              & ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
              & ( ( k1_funct_1 @ A @ B )
                = ( k1_funct_1 @ A @ C ) ) )
           => ( B = C ) ) ) ) )).

thf('20',plain,(
    ! [X4: $i] :
      ( ( r2_hidden @ ( sk_C @ X4 ) @ ( k1_relat_1 @ X4 ) )
      | ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('21',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B_1 ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('26',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B_1 ) @ sk_A )
    | ( v2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['21','26','27'])).

thf('29',plain,(
    ! [X4: $i] :
      ( ( ( k1_funct_1 @ X4 @ ( sk_B @ X4 ) )
        = ( k1_funct_1 @ X4 @ ( sk_C @ X4 ) ) )
      | ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('30',plain,
    ( ! [X20: $i,X21: $i] :
        ( ( X21 = X20 )
        | ( ( k1_funct_1 @ sk_B_1 @ X21 )
         != ( k1_funct_1 @ sk_B_1 @ X20 ) )
        | ~ ( r2_hidden @ X20 @ sk_A )
        | ~ ( r2_hidden @ X21 @ sk_A ) )
   <= ! [X20: $i,X21: $i] :
        ( ( X21 = X20 )
        | ( ( k1_funct_1 @ sk_B_1 @ X21 )
         != ( k1_funct_1 @ sk_B_1 @ X20 ) )
        | ~ ( r2_hidden @ X20 @ sk_A )
        | ~ ( r2_hidden @ X21 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B_1 @ X0 )
         != ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
        | ~ ( v1_relat_1 @ sk_B_1 )
        | ~ ( v1_funct_1 @ sk_B_1 )
        | ( v2_funct_1 @ sk_B_1 )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ ( sk_C @ sk_B_1 ) @ sk_A )
        | ( X0
          = ( sk_C @ sk_B_1 ) ) )
   <= ! [X20: $i,X21: $i] :
        ( ( X21 = X20 )
        | ( ( k1_funct_1 @ sk_B_1 @ X21 )
         != ( k1_funct_1 @ sk_B_1 @ X20 ) )
        | ~ ( r2_hidden @ X20 @ sk_A )
        | ~ ( r2_hidden @ X21 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['24','25'])).

thf('33',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B_1 @ X0 )
         != ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
        | ( v2_funct_1 @ sk_B_1 )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ ( sk_C @ sk_B_1 ) @ sk_A )
        | ( X0
          = ( sk_C @ sk_B_1 ) ) )
   <= ! [X20: $i,X21: $i] :
        ( ( X21 = X20 )
        | ( ( k1_funct_1 @ sk_B_1 @ X21 )
         != ( k1_funct_1 @ sk_B_1 @ X20 ) )
        | ~ ( r2_hidden @ X20 @ sk_A )
        | ~ ( r2_hidden @ X21 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,
    ( ! [X0: $i] :
        ( ( v2_funct_1 @ sk_B_1 )
        | ( X0
          = ( sk_C @ sk_B_1 ) )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ( v2_funct_1 @ sk_B_1 )
        | ( ( k1_funct_1 @ sk_B_1 @ X0 )
         != ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) )
   <= ! [X20: $i,X21: $i] :
        ( ( X21 = X20 )
        | ( ( k1_funct_1 @ sk_B_1 @ X21 )
         != ( k1_funct_1 @ sk_B_1 @ X20 ) )
        | ~ ( r2_hidden @ X20 @ sk_A )
        | ~ ( r2_hidden @ X21 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','34'])).

thf('36',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B_1 @ X0 )
         != ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ( X0
          = ( sk_C @ sk_B_1 ) )
        | ( v2_funct_1 @ sk_B_1 ) )
   <= ! [X20: $i,X21: $i] :
        ( ( X21 = X20 )
        | ( ( k1_funct_1 @ sk_B_1 @ X21 )
         != ( k1_funct_1 @ sk_B_1 @ X20 ) )
        | ~ ( r2_hidden @ X20 @ sk_A )
        | ~ ( r2_hidden @ X21 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( ( v2_funct_1 @ sk_B_1 )
      | ( ( sk_B @ sk_B_1 )
        = ( sk_C @ sk_B_1 ) )
      | ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ) )
   <= ! [X20: $i,X21: $i] :
        ( ( X21 = X20 )
        | ( ( k1_funct_1 @ sk_B_1 @ X21 )
         != ( k1_funct_1 @ sk_B_1 @ X20 ) )
        | ~ ( r2_hidden @ X20 @ sk_A )
        | ~ ( r2_hidden @ X21 @ sk_A ) ) ),
    inference(eq_res,[status(thm)],['36'])).

thf('38',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['6','15','18'])).

thf('39',plain,(
    ! [X4: $i] :
      ( ( r2_hidden @ ( sk_B @ X4 ) @ ( k1_relat_1 @ X4 ) )
      | ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('40',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['24','25'])).

thf('42',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A )
    | ( v2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,
    ( ( ( ( sk_B @ sk_B_1 )
        = ( sk_C @ sk_B_1 ) )
      | ( v2_funct_1 @ sk_B_1 ) )
   <= ! [X20: $i,X21: $i] :
        ( ( X21 = X20 )
        | ( ( k1_funct_1 @ sk_B_1 @ X21 )
         != ( k1_funct_1 @ sk_B_1 @ X20 ) )
        | ~ ( r2_hidden @ X20 @ sk_A )
        | ~ ( r2_hidden @ X21 @ sk_A ) ) ),
    inference(clc,[status(thm)],['37','43'])).

thf('45',plain,
    ( ~ ( v2_funct_1 @ sk_B_1 )
   <= ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('46',plain,
    ( ( ( sk_B @ sk_B_1 )
      = ( sk_C @ sk_B_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X20: $i,X21: $i] :
          ( ( X21 = X20 )
          | ( ( k1_funct_1 @ sk_B_1 @ X21 )
           != ( k1_funct_1 @ sk_B_1 @ X20 ) )
          | ~ ( r2_hidden @ X20 @ sk_A )
          | ~ ( r2_hidden @ X21 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X4: $i] :
      ( ( ( sk_B @ X4 )
       != ( sk_C @ X4 ) )
      | ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('48',plain,
    ( ( ( ( sk_B @ sk_B_1 )
       != ( sk_B @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( v2_funct_1 @ sk_B_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X20: $i,X21: $i] :
          ( ( X21 = X20 )
          | ( ( k1_funct_1 @ sk_B_1 @ X21 )
           != ( k1_funct_1 @ sk_B_1 @ X20 ) )
          | ~ ( r2_hidden @ X20 @ sk_A )
          | ~ ( r2_hidden @ X21 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['24','25'])).

thf('50',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( ( ( sk_B @ sk_B_1 )
       != ( sk_B @ sk_B_1 ) )
      | ( v2_funct_1 @ sk_B_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X20: $i,X21: $i] :
          ( ( X21 = X20 )
          | ( ( k1_funct_1 @ sk_B_1 @ X21 )
           != ( k1_funct_1 @ sk_B_1 @ X20 ) )
          | ~ ( r2_hidden @ X20 @ sk_A )
          | ~ ( r2_hidden @ X21 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,
    ( ( v2_funct_1 @ sk_B_1 )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X20: $i,X21: $i] :
          ( ( X21 = X20 )
          | ( ( k1_funct_1 @ sk_B_1 @ X21 )
           != ( k1_funct_1 @ sk_B_1 @ X20 ) )
          | ~ ( r2_hidden @ X20 @ sk_A )
          | ~ ( r2_hidden @ X21 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ~ ( v2_funct_1 @ sk_B_1 )
   <= ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('54',plain,
    ( ~ ! [X20: $i,X21: $i] :
          ( ( X21 = X20 )
          | ( ( k1_funct_1 @ sk_B_1 @ X21 )
           != ( k1_funct_1 @ sk_B_1 @ X20 ) )
          | ~ ( r2_hidden @ X20 @ sk_A )
          | ~ ( r2_hidden @ X21 @ sk_A ) )
    | ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('56',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['3','54','55'])).

thf('57',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['1','56'])).

thf('58',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['6','15','18'])).

thf(t56_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( v2_funct_1 @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) )
       => ( ( A
            = ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) )
          & ( A
            = ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ) )).

thf('59',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ X7 ) )
      | ( X8
        = ( k1_funct_1 @ ( k2_funct_1 @ X7 ) @ ( k1_funct_1 @ X7 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t56_funct_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( X0
        = ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['24','25'])).

thf('62',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( X0
        = ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,
    ( ( v2_funct_1 @ sk_B_1 )
   <= ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('65',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['3','54'])).

thf('66',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(simpl_trail,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( X0
        = ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['63','66'])).

thf('68',plain,
    ( sk_C_1
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['57','67'])).

thf('69',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
   <= ( r2_hidden @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['69'])).

thf('71',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['69'])).

thf('72',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference('sat_resolution*',[status(thm)],['3','54','71'])).

thf('73',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(simpl_trail,[status(thm)],['70','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( X0
        = ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['63','66'])).

thf('75',plain,
    ( sk_D
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) )
   <= ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) ) ),
    inference(split,[status(esa)],['76'])).

thf('78',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['76'])).

thf('79',plain,
    ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
    = ( k1_funct_1 @ sk_B_1 @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['3','54','78'])).

thf('80',plain,
    ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
    = ( k1_funct_1 @ sk_B_1 @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['77','79'])).

thf('81',plain,
    ( sk_D
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['75','80'])).

thf('82',plain,(
    sk_D = sk_C_1 ),
    inference('sup+',[status(thm)],['68','81'])).

thf('83',plain,
    ( ( sk_C_1 != sk_D )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( sk_C_1 != sk_D )
   <= ( sk_C_1 != sk_D ) ),
    inference(split,[status(esa)],['83'])).

thf('85',plain,
    ( ( sk_C_1 != sk_D )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['83'])).

thf('86',plain,(
    sk_C_1 != sk_D ),
    inference('sat_resolution*',[status(thm)],['3','54','85'])).

thf('87',plain,(
    sk_C_1 != sk_D ),
    inference(simpl_trail,[status(thm)],['84','86'])).

thf('88',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['82','87'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eFdqW8wHiP
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:43:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.41/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.58  % Solved by: fo/fo7.sh
% 0.41/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.58  % done 97 iterations in 0.109s
% 0.41/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.58  % SZS output start Refutation
% 0.41/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.58  thf(sk_D_type, type, sk_D: $i).
% 0.41/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.41/0.58  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.41/0.58  thf(sk_B_type, type, sk_B: $i > $i).
% 0.41/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.41/0.58  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.41/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.41/0.58  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.41/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.58  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.41/0.58  thf(sk_C_type, type, sk_C: $i > $i).
% 0.41/0.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.41/0.58  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.41/0.58  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.41/0.58  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.41/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.41/0.58  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.41/0.58  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.41/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.58  thf(t77_funct_2, conjecture,
% 0.41/0.58    (![A:$i,B:$i]:
% 0.41/0.58     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.41/0.58         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.41/0.58       ( ( v2_funct_1 @ B ) <=>
% 0.41/0.58         ( ![C:$i,D:$i]:
% 0.41/0.58           ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.41/0.58               ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.41/0.58             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.41/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.58    (~( ![A:$i,B:$i]:
% 0.41/0.58        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.41/0.58            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.41/0.58          ( ( v2_funct_1 @ B ) <=>
% 0.41/0.58            ( ![C:$i,D:$i]:
% 0.41/0.58              ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.41/0.58                  ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.41/0.58                ( ( C ) = ( D ) ) ) ) ) ) )),
% 0.41/0.58    inference('cnf.neg', [status(esa)], [t77_funct_2])).
% 0.41/0.58  thf('0', plain, (((r2_hidden @ sk_C_1 @ sk_A) | ~ (v2_funct_1 @ sk_B_1))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('1', plain,
% 0.41/0.58      (((r2_hidden @ sk_C_1 @ sk_A)) <= (((r2_hidden @ sk_C_1 @ sk_A)))),
% 0.41/0.58      inference('split', [status(esa)], ['0'])).
% 0.41/0.58  thf('2', plain,
% 0.41/0.58      (![X20 : $i, X21 : $i]:
% 0.41/0.58         (((X21) = (X20))
% 0.41/0.58          | ((k1_funct_1 @ sk_B_1 @ X21) != (k1_funct_1 @ sk_B_1 @ X20))
% 0.41/0.58          | ~ (r2_hidden @ X20 @ sk_A)
% 0.41/0.58          | ~ (r2_hidden @ X21 @ sk_A)
% 0.41/0.58          | (v2_funct_1 @ sk_B_1))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('3', plain,
% 0.41/0.58      (((v2_funct_1 @ sk_B_1)) | 
% 0.41/0.58       (![X20 : $i, X21 : $i]:
% 0.41/0.58          (((X21) = (X20))
% 0.41/0.58           | ((k1_funct_1 @ sk_B_1 @ X21) != (k1_funct_1 @ sk_B_1 @ X20))
% 0.41/0.58           | ~ (r2_hidden @ X20 @ sk_A)
% 0.41/0.58           | ~ (r2_hidden @ X21 @ sk_A)))),
% 0.41/0.58      inference('split', [status(esa)], ['2'])).
% 0.41/0.58  thf('4', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf(d1_funct_2, axiom,
% 0.41/0.58    (![A:$i,B:$i,C:$i]:
% 0.41/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.58       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.41/0.58           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.41/0.58             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.41/0.58         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.41/0.58           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.41/0.58             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.41/0.58  thf(zf_stmt_1, axiom,
% 0.41/0.58    (![C:$i,B:$i,A:$i]:
% 0.41/0.58     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.41/0.58       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.41/0.58  thf('5', plain,
% 0.41/0.58      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.41/0.58         (~ (v1_funct_2 @ X16 @ X14 @ X15)
% 0.41/0.58          | ((X14) = (k1_relset_1 @ X14 @ X15 @ X16))
% 0.41/0.58          | ~ (zip_tseitin_1 @ X16 @ X15 @ X14))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.41/0.58  thf('6', plain,
% 0.41/0.58      ((~ (zip_tseitin_1 @ sk_B_1 @ sk_A @ sk_A)
% 0.41/0.58        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_A @ sk_B_1)))),
% 0.41/0.58      inference('sup-', [status(thm)], ['4', '5'])).
% 0.41/0.58  thf('7', plain,
% 0.41/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.41/0.58  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.41/0.58  thf(zf_stmt_4, axiom,
% 0.41/0.58    (![B:$i,A:$i]:
% 0.41/0.58     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.41/0.58       ( zip_tseitin_0 @ B @ A ) ))).
% 0.41/0.58  thf(zf_stmt_5, axiom,
% 0.41/0.58    (![A:$i,B:$i,C:$i]:
% 0.41/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.58       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.41/0.58         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.41/0.58           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.41/0.58             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.41/0.58  thf('8', plain,
% 0.41/0.58      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.41/0.58         (~ (zip_tseitin_0 @ X17 @ X18)
% 0.41/0.58          | (zip_tseitin_1 @ X19 @ X17 @ X18)
% 0.41/0.58          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X17))))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.41/0.58  thf('9', plain,
% 0.41/0.58      (((zip_tseitin_1 @ sk_B_1 @ sk_A @ sk_A)
% 0.41/0.58        | ~ (zip_tseitin_0 @ sk_A @ sk_A))),
% 0.41/0.58      inference('sup-', [status(thm)], ['7', '8'])).
% 0.41/0.58  thf('10', plain,
% 0.41/0.58      (![X12 : $i, X13 : $i]:
% 0.41/0.58         ((zip_tseitin_0 @ X12 @ X13) | ((X12) = (k1_xboole_0)))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.41/0.58  thf('11', plain,
% 0.41/0.58      (![X12 : $i, X13 : $i]:
% 0.41/0.58         ((zip_tseitin_0 @ X12 @ X13) | ((X13) != (k1_xboole_0)))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.41/0.58  thf('12', plain, (![X12 : $i]: (zip_tseitin_0 @ X12 @ k1_xboole_0)),
% 0.41/0.58      inference('simplify', [status(thm)], ['11'])).
% 0.41/0.58  thf('13', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.58         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 0.41/0.58      inference('sup+', [status(thm)], ['10', '12'])).
% 0.41/0.58  thf('14', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 0.41/0.58      inference('eq_fact', [status(thm)], ['13'])).
% 0.41/0.58  thf('15', plain, ((zip_tseitin_1 @ sk_B_1 @ sk_A @ sk_A)),
% 0.41/0.58      inference('demod', [status(thm)], ['9', '14'])).
% 0.41/0.58  thf('16', plain,
% 0.41/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf(redefinition_k1_relset_1, axiom,
% 0.41/0.58    (![A:$i,B:$i,C:$i]:
% 0.41/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.58       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.41/0.58  thf('17', plain,
% 0.41/0.58      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.41/0.58         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 0.41/0.58          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.41/0.58      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.41/0.58  thf('18', plain,
% 0.41/0.58      (((k1_relset_1 @ sk_A @ sk_A @ sk_B_1) = (k1_relat_1 @ sk_B_1))),
% 0.41/0.58      inference('sup-', [status(thm)], ['16', '17'])).
% 0.41/0.58  thf('19', plain, (((sk_A) = (k1_relat_1 @ sk_B_1))),
% 0.41/0.58      inference('demod', [status(thm)], ['6', '15', '18'])).
% 0.41/0.58  thf(d8_funct_1, axiom,
% 0.41/0.58    (![A:$i]:
% 0.41/0.58     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.41/0.58       ( ( v2_funct_1 @ A ) <=>
% 0.41/0.58         ( ![B:$i,C:$i]:
% 0.41/0.58           ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 0.41/0.58               ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.41/0.58               ( ( k1_funct_1 @ A @ B ) = ( k1_funct_1 @ A @ C ) ) ) =>
% 0.41/0.58             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.41/0.58  thf('20', plain,
% 0.41/0.58      (![X4 : $i]:
% 0.41/0.58         ((r2_hidden @ (sk_C @ X4) @ (k1_relat_1 @ X4))
% 0.41/0.58          | (v2_funct_1 @ X4)
% 0.41/0.58          | ~ (v1_funct_1 @ X4)
% 0.41/0.58          | ~ (v1_relat_1 @ X4))),
% 0.41/0.58      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.41/0.58  thf('21', plain,
% 0.41/0.58      (((r2_hidden @ (sk_C @ sk_B_1) @ sk_A)
% 0.41/0.58        | ~ (v1_relat_1 @ sk_B_1)
% 0.41/0.58        | ~ (v1_funct_1 @ sk_B_1)
% 0.41/0.58        | (v2_funct_1 @ sk_B_1))),
% 0.41/0.58      inference('sup+', [status(thm)], ['19', '20'])).
% 0.41/0.58  thf('22', plain,
% 0.41/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf(cc2_relat_1, axiom,
% 0.41/0.58    (![A:$i]:
% 0.41/0.58     ( ( v1_relat_1 @ A ) =>
% 0.41/0.58       ( ![B:$i]:
% 0.41/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.41/0.58  thf('23', plain,
% 0.41/0.58      (![X0 : $i, X1 : $i]:
% 0.41/0.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.41/0.58          | (v1_relat_1 @ X0)
% 0.41/0.58          | ~ (v1_relat_1 @ X1))),
% 0.41/0.58      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.41/0.58  thf('24', plain,
% 0.41/0.58      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B_1))),
% 0.41/0.58      inference('sup-', [status(thm)], ['22', '23'])).
% 0.41/0.58  thf(fc6_relat_1, axiom,
% 0.41/0.58    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.41/0.58  thf('25', plain,
% 0.41/0.58      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.41/0.58      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.41/0.58  thf('26', plain, ((v1_relat_1 @ sk_B_1)),
% 0.41/0.58      inference('demod', [status(thm)], ['24', '25'])).
% 0.41/0.58  thf('27', plain, ((v1_funct_1 @ sk_B_1)),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('28', plain,
% 0.41/0.58      (((r2_hidden @ (sk_C @ sk_B_1) @ sk_A) | (v2_funct_1 @ sk_B_1))),
% 0.41/0.58      inference('demod', [status(thm)], ['21', '26', '27'])).
% 0.41/0.58  thf('29', plain,
% 0.41/0.58      (![X4 : $i]:
% 0.41/0.58         (((k1_funct_1 @ X4 @ (sk_B @ X4)) = (k1_funct_1 @ X4 @ (sk_C @ X4)))
% 0.41/0.58          | (v2_funct_1 @ X4)
% 0.41/0.58          | ~ (v1_funct_1 @ X4)
% 0.41/0.58          | ~ (v1_relat_1 @ X4))),
% 0.41/0.58      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.41/0.58  thf('30', plain,
% 0.41/0.58      ((![X20 : $i, X21 : $i]:
% 0.41/0.58          (((X21) = (X20))
% 0.41/0.58           | ((k1_funct_1 @ sk_B_1 @ X21) != (k1_funct_1 @ sk_B_1 @ X20))
% 0.41/0.58           | ~ (r2_hidden @ X20 @ sk_A)
% 0.41/0.58           | ~ (r2_hidden @ X21 @ sk_A)))
% 0.41/0.58         <= ((![X20 : $i, X21 : $i]:
% 0.41/0.58                (((X21) = (X20))
% 0.41/0.58                 | ((k1_funct_1 @ sk_B_1 @ X21) != (k1_funct_1 @ sk_B_1 @ X20))
% 0.41/0.58                 | ~ (r2_hidden @ X20 @ sk_A)
% 0.41/0.58                 | ~ (r2_hidden @ X21 @ sk_A))))),
% 0.41/0.58      inference('split', [status(esa)], ['2'])).
% 0.41/0.58  thf('31', plain,
% 0.41/0.58      ((![X0 : $i]:
% 0.41/0.58          (((k1_funct_1 @ sk_B_1 @ X0)
% 0.41/0.58             != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.41/0.58           | ~ (v1_relat_1 @ sk_B_1)
% 0.41/0.58           | ~ (v1_funct_1 @ sk_B_1)
% 0.41/0.58           | (v2_funct_1 @ sk_B_1)
% 0.41/0.58           | ~ (r2_hidden @ X0 @ sk_A)
% 0.41/0.58           | ~ (r2_hidden @ (sk_C @ sk_B_1) @ sk_A)
% 0.41/0.58           | ((X0) = (sk_C @ sk_B_1))))
% 0.41/0.58         <= ((![X20 : $i, X21 : $i]:
% 0.41/0.58                (((X21) = (X20))
% 0.41/0.58                 | ((k1_funct_1 @ sk_B_1 @ X21) != (k1_funct_1 @ sk_B_1 @ X20))
% 0.41/0.58                 | ~ (r2_hidden @ X20 @ sk_A)
% 0.41/0.58                 | ~ (r2_hidden @ X21 @ sk_A))))),
% 0.41/0.58      inference('sup-', [status(thm)], ['29', '30'])).
% 0.41/0.58  thf('32', plain, ((v1_relat_1 @ sk_B_1)),
% 0.41/0.58      inference('demod', [status(thm)], ['24', '25'])).
% 0.41/0.58  thf('33', plain, ((v1_funct_1 @ sk_B_1)),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('34', plain,
% 0.41/0.58      ((![X0 : $i]:
% 0.41/0.58          (((k1_funct_1 @ sk_B_1 @ X0)
% 0.41/0.58             != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.41/0.58           | (v2_funct_1 @ sk_B_1)
% 0.41/0.58           | ~ (r2_hidden @ X0 @ sk_A)
% 0.41/0.58           | ~ (r2_hidden @ (sk_C @ sk_B_1) @ sk_A)
% 0.41/0.58           | ((X0) = (sk_C @ sk_B_1))))
% 0.41/0.58         <= ((![X20 : $i, X21 : $i]:
% 0.41/0.58                (((X21) = (X20))
% 0.41/0.58                 | ((k1_funct_1 @ sk_B_1 @ X21) != (k1_funct_1 @ sk_B_1 @ X20))
% 0.41/0.58                 | ~ (r2_hidden @ X20 @ sk_A)
% 0.41/0.58                 | ~ (r2_hidden @ X21 @ sk_A))))),
% 0.41/0.58      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.41/0.58  thf('35', plain,
% 0.41/0.58      ((![X0 : $i]:
% 0.41/0.58          ((v2_funct_1 @ sk_B_1)
% 0.41/0.58           | ((X0) = (sk_C @ sk_B_1))
% 0.41/0.58           | ~ (r2_hidden @ X0 @ sk_A)
% 0.41/0.58           | (v2_funct_1 @ sk_B_1)
% 0.41/0.58           | ((k1_funct_1 @ sk_B_1 @ X0)
% 0.41/0.58               != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))))
% 0.41/0.58         <= ((![X20 : $i, X21 : $i]:
% 0.41/0.58                (((X21) = (X20))
% 0.41/0.58                 | ((k1_funct_1 @ sk_B_1 @ X21) != (k1_funct_1 @ sk_B_1 @ X20))
% 0.41/0.58                 | ~ (r2_hidden @ X20 @ sk_A)
% 0.41/0.58                 | ~ (r2_hidden @ X21 @ sk_A))))),
% 0.41/0.58      inference('sup-', [status(thm)], ['28', '34'])).
% 0.41/0.58  thf('36', plain,
% 0.41/0.58      ((![X0 : $i]:
% 0.41/0.58          (((k1_funct_1 @ sk_B_1 @ X0)
% 0.41/0.58             != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.41/0.58           | ~ (r2_hidden @ X0 @ sk_A)
% 0.41/0.58           | ((X0) = (sk_C @ sk_B_1))
% 0.41/0.58           | (v2_funct_1 @ sk_B_1)))
% 0.41/0.58         <= ((![X20 : $i, X21 : $i]:
% 0.41/0.58                (((X21) = (X20))
% 0.41/0.58                 | ((k1_funct_1 @ sk_B_1 @ X21) != (k1_funct_1 @ sk_B_1 @ X20))
% 0.41/0.58                 | ~ (r2_hidden @ X20 @ sk_A)
% 0.41/0.58                 | ~ (r2_hidden @ X21 @ sk_A))))),
% 0.41/0.58      inference('simplify', [status(thm)], ['35'])).
% 0.41/0.58  thf('37', plain,
% 0.41/0.58      ((((v2_funct_1 @ sk_B_1)
% 0.41/0.58         | ((sk_B @ sk_B_1) = (sk_C @ sk_B_1))
% 0.41/0.58         | ~ (r2_hidden @ (sk_B @ sk_B_1) @ sk_A)))
% 0.41/0.58         <= ((![X20 : $i, X21 : $i]:
% 0.41/0.58                (((X21) = (X20))
% 0.41/0.58                 | ((k1_funct_1 @ sk_B_1 @ X21) != (k1_funct_1 @ sk_B_1 @ X20))
% 0.41/0.58                 | ~ (r2_hidden @ X20 @ sk_A)
% 0.41/0.58                 | ~ (r2_hidden @ X21 @ sk_A))))),
% 0.41/0.58      inference('eq_res', [status(thm)], ['36'])).
% 0.41/0.58  thf('38', plain, (((sk_A) = (k1_relat_1 @ sk_B_1))),
% 0.41/0.58      inference('demod', [status(thm)], ['6', '15', '18'])).
% 0.41/0.58  thf('39', plain,
% 0.41/0.58      (![X4 : $i]:
% 0.41/0.58         ((r2_hidden @ (sk_B @ X4) @ (k1_relat_1 @ X4))
% 0.41/0.58          | (v2_funct_1 @ X4)
% 0.41/0.58          | ~ (v1_funct_1 @ X4)
% 0.41/0.58          | ~ (v1_relat_1 @ X4))),
% 0.41/0.58      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.41/0.58  thf('40', plain,
% 0.41/0.58      (((r2_hidden @ (sk_B @ sk_B_1) @ sk_A)
% 0.41/0.58        | ~ (v1_relat_1 @ sk_B_1)
% 0.41/0.58        | ~ (v1_funct_1 @ sk_B_1)
% 0.41/0.58        | (v2_funct_1 @ sk_B_1))),
% 0.41/0.58      inference('sup+', [status(thm)], ['38', '39'])).
% 0.41/0.58  thf('41', plain, ((v1_relat_1 @ sk_B_1)),
% 0.41/0.58      inference('demod', [status(thm)], ['24', '25'])).
% 0.41/0.58  thf('42', plain, ((v1_funct_1 @ sk_B_1)),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('43', plain,
% 0.41/0.58      (((r2_hidden @ (sk_B @ sk_B_1) @ sk_A) | (v2_funct_1 @ sk_B_1))),
% 0.41/0.58      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.41/0.58  thf('44', plain,
% 0.41/0.58      (((((sk_B @ sk_B_1) = (sk_C @ sk_B_1)) | (v2_funct_1 @ sk_B_1)))
% 0.41/0.58         <= ((![X20 : $i, X21 : $i]:
% 0.41/0.58                (((X21) = (X20))
% 0.41/0.58                 | ((k1_funct_1 @ sk_B_1 @ X21) != (k1_funct_1 @ sk_B_1 @ X20))
% 0.41/0.58                 | ~ (r2_hidden @ X20 @ sk_A)
% 0.41/0.58                 | ~ (r2_hidden @ X21 @ sk_A))))),
% 0.41/0.58      inference('clc', [status(thm)], ['37', '43'])).
% 0.41/0.58  thf('45', plain, ((~ (v2_funct_1 @ sk_B_1)) <= (~ ((v2_funct_1 @ sk_B_1)))),
% 0.41/0.58      inference('split', [status(esa)], ['0'])).
% 0.41/0.58  thf('46', plain,
% 0.41/0.58      ((((sk_B @ sk_B_1) = (sk_C @ sk_B_1)))
% 0.41/0.58         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.41/0.58             (![X20 : $i, X21 : $i]:
% 0.41/0.58                (((X21) = (X20))
% 0.41/0.58                 | ((k1_funct_1 @ sk_B_1 @ X21) != (k1_funct_1 @ sk_B_1 @ X20))
% 0.41/0.58                 | ~ (r2_hidden @ X20 @ sk_A)
% 0.41/0.58                 | ~ (r2_hidden @ X21 @ sk_A))))),
% 0.41/0.58      inference('sup-', [status(thm)], ['44', '45'])).
% 0.41/0.58  thf('47', plain,
% 0.41/0.58      (![X4 : $i]:
% 0.41/0.58         (((sk_B @ X4) != (sk_C @ X4))
% 0.41/0.58          | (v2_funct_1 @ X4)
% 0.41/0.58          | ~ (v1_funct_1 @ X4)
% 0.41/0.58          | ~ (v1_relat_1 @ X4))),
% 0.41/0.58      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.41/0.58  thf('48', plain,
% 0.41/0.58      (((((sk_B @ sk_B_1) != (sk_B @ sk_B_1))
% 0.41/0.58         | ~ (v1_relat_1 @ sk_B_1)
% 0.41/0.58         | ~ (v1_funct_1 @ sk_B_1)
% 0.41/0.58         | (v2_funct_1 @ sk_B_1)))
% 0.41/0.58         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.41/0.58             (![X20 : $i, X21 : $i]:
% 0.41/0.58                (((X21) = (X20))
% 0.41/0.58                 | ((k1_funct_1 @ sk_B_1 @ X21) != (k1_funct_1 @ sk_B_1 @ X20))
% 0.41/0.58                 | ~ (r2_hidden @ X20 @ sk_A)
% 0.41/0.58                 | ~ (r2_hidden @ X21 @ sk_A))))),
% 0.41/0.58      inference('sup-', [status(thm)], ['46', '47'])).
% 0.41/0.58  thf('49', plain, ((v1_relat_1 @ sk_B_1)),
% 0.41/0.58      inference('demod', [status(thm)], ['24', '25'])).
% 0.41/0.58  thf('50', plain, ((v1_funct_1 @ sk_B_1)),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('51', plain,
% 0.41/0.58      (((((sk_B @ sk_B_1) != (sk_B @ sk_B_1)) | (v2_funct_1 @ sk_B_1)))
% 0.41/0.58         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.41/0.58             (![X20 : $i, X21 : $i]:
% 0.41/0.58                (((X21) = (X20))
% 0.41/0.58                 | ((k1_funct_1 @ sk_B_1 @ X21) != (k1_funct_1 @ sk_B_1 @ X20))
% 0.41/0.58                 | ~ (r2_hidden @ X20 @ sk_A)
% 0.41/0.58                 | ~ (r2_hidden @ X21 @ sk_A))))),
% 0.41/0.58      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.41/0.58  thf('52', plain,
% 0.41/0.58      (((v2_funct_1 @ sk_B_1))
% 0.41/0.58         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.41/0.58             (![X20 : $i, X21 : $i]:
% 0.41/0.58                (((X21) = (X20))
% 0.41/0.58                 | ((k1_funct_1 @ sk_B_1 @ X21) != (k1_funct_1 @ sk_B_1 @ X20))
% 0.41/0.58                 | ~ (r2_hidden @ X20 @ sk_A)
% 0.41/0.58                 | ~ (r2_hidden @ X21 @ sk_A))))),
% 0.41/0.58      inference('simplify', [status(thm)], ['51'])).
% 0.41/0.58  thf('53', plain, ((~ (v2_funct_1 @ sk_B_1)) <= (~ ((v2_funct_1 @ sk_B_1)))),
% 0.41/0.58      inference('split', [status(esa)], ['0'])).
% 0.41/0.58  thf('54', plain,
% 0.41/0.58      (~
% 0.41/0.58       (![X20 : $i, X21 : $i]:
% 0.41/0.58          (((X21) = (X20))
% 0.41/0.58           | ((k1_funct_1 @ sk_B_1 @ X21) != (k1_funct_1 @ sk_B_1 @ X20))
% 0.41/0.58           | ~ (r2_hidden @ X20 @ sk_A)
% 0.41/0.58           | ~ (r2_hidden @ X21 @ sk_A))) | 
% 0.41/0.58       ((v2_funct_1 @ sk_B_1))),
% 0.41/0.58      inference('sup-', [status(thm)], ['52', '53'])).
% 0.41/0.58  thf('55', plain, (((r2_hidden @ sk_C_1 @ sk_A)) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.41/0.58      inference('split', [status(esa)], ['0'])).
% 0.41/0.58  thf('56', plain, (((r2_hidden @ sk_C_1 @ sk_A))),
% 0.41/0.58      inference('sat_resolution*', [status(thm)], ['3', '54', '55'])).
% 0.41/0.58  thf('57', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.41/0.58      inference('simpl_trail', [status(thm)], ['1', '56'])).
% 0.41/0.58  thf('58', plain, (((sk_A) = (k1_relat_1 @ sk_B_1))),
% 0.41/0.58      inference('demod', [status(thm)], ['6', '15', '18'])).
% 0.41/0.58  thf(t56_funct_1, axiom,
% 0.41/0.58    (![A:$i,B:$i]:
% 0.41/0.58     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.41/0.58       ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) ) =>
% 0.41/0.58         ( ( ( A ) =
% 0.41/0.58             ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) ) & 
% 0.41/0.58           ( ( A ) =
% 0.41/0.58             ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ))).
% 0.41/0.58  thf('59', plain,
% 0.41/0.58      (![X7 : $i, X8 : $i]:
% 0.41/0.58         (~ (v2_funct_1 @ X7)
% 0.41/0.58          | ~ (r2_hidden @ X8 @ (k1_relat_1 @ X7))
% 0.41/0.58          | ((X8) = (k1_funct_1 @ (k2_funct_1 @ X7) @ (k1_funct_1 @ X7 @ X8)))
% 0.41/0.58          | ~ (v1_funct_1 @ X7)
% 0.41/0.58          | ~ (v1_relat_1 @ X7))),
% 0.41/0.58      inference('cnf', [status(esa)], [t56_funct_1])).
% 0.41/0.58  thf('60', plain,
% 0.41/0.58      (![X0 : $i]:
% 0.41/0.58         (~ (r2_hidden @ X0 @ sk_A)
% 0.41/0.58          | ~ (v1_relat_1 @ sk_B_1)
% 0.41/0.58          | ~ (v1_funct_1 @ sk_B_1)
% 0.41/0.58          | ((X0)
% 0.41/0.58              = (k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ 
% 0.41/0.58                 (k1_funct_1 @ sk_B_1 @ X0)))
% 0.41/0.58          | ~ (v2_funct_1 @ sk_B_1))),
% 0.41/0.58      inference('sup-', [status(thm)], ['58', '59'])).
% 0.41/0.58  thf('61', plain, ((v1_relat_1 @ sk_B_1)),
% 0.41/0.58      inference('demod', [status(thm)], ['24', '25'])).
% 0.41/0.58  thf('62', plain, ((v1_funct_1 @ sk_B_1)),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('63', plain,
% 0.41/0.58      (![X0 : $i]:
% 0.41/0.58         (~ (r2_hidden @ X0 @ sk_A)
% 0.41/0.58          | ((X0)
% 0.41/0.58              = (k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ 
% 0.41/0.58                 (k1_funct_1 @ sk_B_1 @ X0)))
% 0.41/0.58          | ~ (v2_funct_1 @ sk_B_1))),
% 0.41/0.58      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.41/0.58  thf('64', plain, (((v2_funct_1 @ sk_B_1)) <= (((v2_funct_1 @ sk_B_1)))),
% 0.41/0.58      inference('split', [status(esa)], ['2'])).
% 0.41/0.58  thf('65', plain, (((v2_funct_1 @ sk_B_1))),
% 0.41/0.58      inference('sat_resolution*', [status(thm)], ['3', '54'])).
% 0.41/0.58  thf('66', plain, ((v2_funct_1 @ sk_B_1)),
% 0.41/0.58      inference('simpl_trail', [status(thm)], ['64', '65'])).
% 0.41/0.58  thf('67', plain,
% 0.41/0.58      (![X0 : $i]:
% 0.41/0.58         (~ (r2_hidden @ X0 @ sk_A)
% 0.41/0.58          | ((X0)
% 0.41/0.58              = (k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ 
% 0.41/0.58                 (k1_funct_1 @ sk_B_1 @ X0))))),
% 0.41/0.58      inference('demod', [status(thm)], ['63', '66'])).
% 0.41/0.58  thf('68', plain,
% 0.41/0.58      (((sk_C_1)
% 0.41/0.58         = (k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ sk_C_1)))),
% 0.41/0.58      inference('sup-', [status(thm)], ['57', '67'])).
% 0.41/0.58  thf('69', plain, (((r2_hidden @ sk_D @ sk_A) | ~ (v2_funct_1 @ sk_B_1))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('70', plain,
% 0.41/0.58      (((r2_hidden @ sk_D @ sk_A)) <= (((r2_hidden @ sk_D @ sk_A)))),
% 0.41/0.58      inference('split', [status(esa)], ['69'])).
% 0.41/0.58  thf('71', plain, (((r2_hidden @ sk_D @ sk_A)) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.41/0.58      inference('split', [status(esa)], ['69'])).
% 0.41/0.58  thf('72', plain, (((r2_hidden @ sk_D @ sk_A))),
% 0.41/0.58      inference('sat_resolution*', [status(thm)], ['3', '54', '71'])).
% 0.41/0.58  thf('73', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.41/0.58      inference('simpl_trail', [status(thm)], ['70', '72'])).
% 0.41/0.58  thf('74', plain,
% 0.41/0.58      (![X0 : $i]:
% 0.41/0.58         (~ (r2_hidden @ X0 @ sk_A)
% 0.41/0.58          | ((X0)
% 0.41/0.58              = (k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ 
% 0.41/0.58                 (k1_funct_1 @ sk_B_1 @ X0))))),
% 0.41/0.58      inference('demod', [status(thm)], ['63', '66'])).
% 0.41/0.58  thf('75', plain,
% 0.41/0.58      (((sk_D)
% 0.41/0.58         = (k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ sk_D)))),
% 0.41/0.58      inference('sup-', [status(thm)], ['73', '74'])).
% 0.41/0.58  thf('76', plain,
% 0.41/0.58      ((((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D))
% 0.41/0.58        | ~ (v2_funct_1 @ sk_B_1))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('77', plain,
% 0.41/0.58      ((((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D)))
% 0.41/0.58         <= ((((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D))))),
% 0.41/0.58      inference('split', [status(esa)], ['76'])).
% 0.41/0.58  thf('78', plain,
% 0.41/0.58      ((((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D))) | 
% 0.41/0.58       ~ ((v2_funct_1 @ sk_B_1))),
% 0.41/0.58      inference('split', [status(esa)], ['76'])).
% 0.41/0.58  thf('79', plain,
% 0.41/0.58      ((((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D)))),
% 0.41/0.58      inference('sat_resolution*', [status(thm)], ['3', '54', '78'])).
% 0.41/0.58  thf('80', plain,
% 0.41/0.58      (((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D))),
% 0.41/0.58      inference('simpl_trail', [status(thm)], ['77', '79'])).
% 0.41/0.58  thf('81', plain,
% 0.41/0.58      (((sk_D)
% 0.41/0.58         = (k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ sk_C_1)))),
% 0.41/0.58      inference('demod', [status(thm)], ['75', '80'])).
% 0.41/0.58  thf('82', plain, (((sk_D) = (sk_C_1))),
% 0.41/0.58      inference('sup+', [status(thm)], ['68', '81'])).
% 0.41/0.58  thf('83', plain, ((((sk_C_1) != (sk_D)) | ~ (v2_funct_1 @ sk_B_1))),
% 0.41/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.58  thf('84', plain, ((((sk_C_1) != (sk_D))) <= (~ (((sk_C_1) = (sk_D))))),
% 0.41/0.58      inference('split', [status(esa)], ['83'])).
% 0.41/0.58  thf('85', plain, (~ (((sk_C_1) = (sk_D))) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.41/0.58      inference('split', [status(esa)], ['83'])).
% 0.41/0.58  thf('86', plain, (~ (((sk_C_1) = (sk_D)))),
% 0.41/0.58      inference('sat_resolution*', [status(thm)], ['3', '54', '85'])).
% 0.41/0.58  thf('87', plain, (((sk_C_1) != (sk_D))),
% 0.41/0.58      inference('simpl_trail', [status(thm)], ['84', '86'])).
% 0.41/0.58  thf('88', plain, ($false),
% 0.41/0.58      inference('simplify_reflect-', [status(thm)], ['82', '87'])).
% 0.41/0.58  
% 0.41/0.58  % SZS output end Refutation
% 0.41/0.58  
% 0.41/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
