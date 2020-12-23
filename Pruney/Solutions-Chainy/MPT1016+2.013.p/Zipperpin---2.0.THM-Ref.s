%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZDoUo9mUCi

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:52 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 792 expanded)
%              Number of leaves         :   30 ( 232 expanded)
%              Depth                    :   25
%              Number of atoms          : 1093 (12653 expanded)
%              Number of equality atoms :  104 ( 953 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) )
   <= ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X18 = X17 )
      | ( ( k1_funct_1 @ sk_B_1 @ X18 )
       != ( k1_funct_1 @ sk_B_1 @ X17 ) )
      | ~ ( r2_hidden @ X17 @ sk_A )
      | ~ ( r2_hidden @ X18 @ sk_A )
      | ( v2_funct_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ! [X17: $i,X18: $i] :
        ( ( X18 = X17 )
        | ( ( k1_funct_1 @ sk_B_1 @ X18 )
         != ( k1_funct_1 @ sk_B_1 @ X17 ) )
        | ~ ( r2_hidden @ X17 @ sk_A )
        | ~ ( r2_hidden @ X18 @ sk_A ) ) ),
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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_funct_2 @ X13 @ X11 @ X12 )
      | ( X11
        = ( k1_relset_1 @ X11 @ X12 @ X13 ) )
      | ~ ( zip_tseitin_1 @ X13 @ X12 @ X11 ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( zip_tseitin_0 @ X14 @ X15 )
      | ( zip_tseitin_1 @ X16 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('9',plain,
    ( ( zip_tseitin_1 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X9: $i,X10: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('11',plain,(
    ! [X9: $i,X10: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('12',plain,(
    ! [X9: $i] :
      ( zip_tseitin_0 @ X9 @ k1_xboole_0 ) ),
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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k1_relset_1 @ X7 @ X8 @ X6 )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
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
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
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

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('23',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('24',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B_1 ) @ sk_A )
    | ( v2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['21','24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( sk_C @ X0 ) ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('28',plain,
    ( ! [X17: $i,X18: $i] :
        ( ( X18 = X17 )
        | ( ( k1_funct_1 @ sk_B_1 @ X18 )
         != ( k1_funct_1 @ sk_B_1 @ X17 ) )
        | ~ ( r2_hidden @ X17 @ sk_A )
        | ~ ( r2_hidden @ X18 @ sk_A ) )
   <= ! [X17: $i,X18: $i] :
        ( ( X18 = X17 )
        | ( ( k1_funct_1 @ sk_B_1 @ X18 )
         != ( k1_funct_1 @ sk_B_1 @ X17 ) )
        | ~ ( r2_hidden @ X17 @ sk_A )
        | ~ ( r2_hidden @ X18 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) )
         != ( k1_funct_1 @ sk_B_1 @ X0 ) )
        | ~ ( v1_relat_1 @ sk_B_1 )
        | ~ ( v1_funct_1 @ sk_B_1 )
        | ( v2_funct_1 @ sk_B_1 )
        | ~ ( r2_hidden @ ( sk_C @ sk_B_1 ) @ sk_A )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ( ( sk_C @ sk_B_1 )
          = X0 ) )
   <= ! [X17: $i,X18: $i] :
        ( ( X18 = X17 )
        | ( ( k1_funct_1 @ sk_B_1 @ X18 )
         != ( k1_funct_1 @ sk_B_1 @ X17 ) )
        | ~ ( r2_hidden @ X17 @ sk_A )
        | ~ ( r2_hidden @ X18 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) )
         != ( k1_funct_1 @ sk_B_1 @ X0 ) )
        | ~ ( v1_relat_1 @ sk_B_1 )
        | ( v2_funct_1 @ sk_B_1 )
        | ~ ( r2_hidden @ ( sk_C @ sk_B_1 ) @ sk_A )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ( ( sk_C @ sk_B_1 )
          = X0 ) )
   <= ! [X17: $i,X18: $i] :
        ( ( X18 = X17 )
        | ( ( k1_funct_1 @ sk_B_1 @ X18 )
         != ( k1_funct_1 @ sk_B_1 @ X17 ) )
        | ~ ( r2_hidden @ X17 @ sk_A )
        | ~ ( r2_hidden @ X18 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['22','23'])).

thf('33',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) )
         != ( k1_funct_1 @ sk_B_1 @ X0 ) )
        | ( v2_funct_1 @ sk_B_1 )
        | ~ ( r2_hidden @ ( sk_C @ sk_B_1 ) @ sk_A )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ( ( sk_C @ sk_B_1 )
          = X0 ) )
   <= ! [X17: $i,X18: $i] :
        ( ( X18 = X17 )
        | ( ( k1_funct_1 @ sk_B_1 @ X18 )
         != ( k1_funct_1 @ sk_B_1 @ X17 ) )
        | ~ ( r2_hidden @ X17 @ sk_A )
        | ~ ( r2_hidden @ X18 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ! [X0: $i] :
        ( ( v2_funct_1 @ sk_B_1 )
        | ( ( sk_C @ sk_B_1 )
          = X0 )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ( v2_funct_1 @ sk_B_1 )
        | ( ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) )
         != ( k1_funct_1 @ sk_B_1 @ X0 ) ) )
   <= ! [X17: $i,X18: $i] :
        ( ( X18 = X17 )
        | ( ( k1_funct_1 @ sk_B_1 @ X18 )
         != ( k1_funct_1 @ sk_B_1 @ X17 ) )
        | ~ ( r2_hidden @ X17 @ sk_A )
        | ~ ( r2_hidden @ X18 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','33'])).

thf('35',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) )
         != ( k1_funct_1 @ sk_B_1 @ X0 ) )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ( ( sk_C @ sk_B_1 )
          = X0 )
        | ( v2_funct_1 @ sk_B_1 ) )
   <= ! [X17: $i,X18: $i] :
        ( ( X18 = X17 )
        | ( ( k1_funct_1 @ sk_B_1 @ X18 )
         != ( k1_funct_1 @ sk_B_1 @ X17 ) )
        | ~ ( r2_hidden @ X17 @ sk_A )
        | ~ ( r2_hidden @ X18 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ( ( v2_funct_1 @ sk_B_1 )
      | ( ( sk_C @ sk_B_1 )
        = ( sk_B @ sk_B_1 ) )
      | ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ) )
   <= ! [X17: $i,X18: $i] :
        ( ( X18 = X17 )
        | ( ( k1_funct_1 @ sk_B_1 @ X18 )
         != ( k1_funct_1 @ sk_B_1 @ X17 ) )
        | ~ ( r2_hidden @ X17 @ sk_A )
        | ~ ( r2_hidden @ X18 @ sk_A ) ) ),
    inference(eq_res,[status(thm)],['35'])).

thf('37',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['6','15','18'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('39',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['22','23'])).

thf('41',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A )
    | ( v2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( ( ( ( sk_C @ sk_B_1 )
        = ( sk_B @ sk_B_1 ) )
      | ( v2_funct_1 @ sk_B_1 ) )
   <= ! [X17: $i,X18: $i] :
        ( ( X18 = X17 )
        | ( ( k1_funct_1 @ sk_B_1 @ X18 )
         != ( k1_funct_1 @ sk_B_1 @ X17 ) )
        | ~ ( r2_hidden @ X17 @ sk_A )
        | ~ ( r2_hidden @ X18 @ sk_A ) ) ),
    inference(clc,[status(thm)],['36','42'])).

thf('44',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ~ ( v2_funct_1 @ sk_B_1 )
   <= ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['44'])).

thf('46',plain,
    ( ( ( sk_C @ sk_B_1 )
      = ( sk_B @ sk_B_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X17: $i,X18: $i] :
          ( ( X18 = X17 )
          | ( ( k1_funct_1 @ sk_B_1 @ X18 )
           != ( k1_funct_1 @ sk_B_1 @ X17 ) )
          | ~ ( r2_hidden @ X17 @ sk_A )
          | ~ ( r2_hidden @ X18 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
       != ( sk_C @ X0 ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('48',plain,
    ( ( ( ( sk_B @ sk_B_1 )
       != ( sk_B @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( v2_funct_1 @ sk_B_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X17: $i,X18: $i] :
          ( ( X18 = X17 )
          | ( ( k1_funct_1 @ sk_B_1 @ X18 )
           != ( k1_funct_1 @ sk_B_1 @ X17 ) )
          | ~ ( r2_hidden @ X17 @ sk_A )
          | ~ ( r2_hidden @ X18 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['22','23'])).

thf('50',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( ( ( sk_B @ sk_B_1 )
       != ( sk_B @ sk_B_1 ) )
      | ( v2_funct_1 @ sk_B_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X17: $i,X18: $i] :
          ( ( X18 = X17 )
          | ( ( k1_funct_1 @ sk_B_1 @ X18 )
           != ( k1_funct_1 @ sk_B_1 @ X17 ) )
          | ~ ( r2_hidden @ X17 @ sk_A )
          | ~ ( r2_hidden @ X18 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,
    ( ( v2_funct_1 @ sk_B_1 )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X17: $i,X18: $i] :
          ( ( X18 = X17 )
          | ( ( k1_funct_1 @ sk_B_1 @ X18 )
           != ( k1_funct_1 @ sk_B_1 @ X17 ) )
          | ~ ( r2_hidden @ X17 @ sk_A )
          | ~ ( r2_hidden @ X18 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ~ ( v2_funct_1 @ sk_B_1 )
   <= ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['44'])).

thf('54',plain,
    ( ~ ! [X17: $i,X18: $i] :
          ( ( X18 = X17 )
          | ( ( k1_funct_1 @ sk_B_1 @ X18 )
           != ( k1_funct_1 @ sk_B_1 @ X17 ) )
          | ~ ( r2_hidden @ X17 @ sk_A )
          | ~ ( r2_hidden @ X18 @ sk_A ) )
    | ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('56',plain,
    ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
    = ( k1_funct_1 @ sk_B_1 @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['3','54','55'])).

thf('57',plain,
    ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
    = ( k1_funct_1 @ sk_B_1 @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['1','56'])).

thf('58',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['6','15','18'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ X0 @ X1 )
       != ( k1_funct_1 @ X0 @ X2 ) )
      | ( X1 = X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ sk_B_1 @ X0 )
       != ( k1_funct_1 @ sk_B_1 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_B_1 ) )
      | ~ ( v2_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['22','23'])).

thf('62',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['6','15','18'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ sk_B_1 @ X0 )
       != ( k1_funct_1 @ sk_B_1 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['60','61','62','63'])).

thf('65',plain,
    ( ( v2_funct_1 @ sk_B_1 )
   <= ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('66',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['3','54'])).

thf('67',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(simpl_trail,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ sk_B_1 @ X0 )
       != ( k1_funct_1 @ sk_B_1 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
       != ( k1_funct_1 @ sk_B_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( sk_D = X0 )
      | ~ ( r2_hidden @ sk_D @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','68'])).

thf('70',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
   <= ( r2_hidden @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['70'])).

thf('72',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['70'])).

thf('73',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference('sat_resolution*',[status(thm)],['3','54','72'])).

thf('74',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(simpl_trail,[status(thm)],['71','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
       != ( k1_funct_1 @ sk_B_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( sk_D = X0 ) ) ),
    inference(demod,[status(thm)],['69','74'])).

thf('76',plain,
    ( ( sk_D = sk_C_1 )
    | ~ ( r2_hidden @ sk_C_1 @ sk_A ) ),
    inference(eq_res,[status(thm)],['75'])).

thf('77',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_A )
   <= ( r2_hidden @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['44'])).

thf('78',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['44'])).

thf('79',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['3','54','78'])).

thf('80',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['77','79'])).

thf('81',plain,(
    sk_D = sk_C_1 ),
    inference(demod,[status(thm)],['76','80'])).

thf('82',plain,
    ( ( sk_C_1 != sk_D )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( sk_C_1 != sk_D )
   <= ( sk_C_1 != sk_D ) ),
    inference(split,[status(esa)],['82'])).

thf('84',plain,
    ( ( sk_C_1 != sk_D )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['82'])).

thf('85',plain,(
    sk_C_1 != sk_D ),
    inference('sat_resolution*',[status(thm)],['3','54','84'])).

thf('86',plain,(
    sk_C_1 != sk_D ),
    inference(simpl_trail,[status(thm)],['83','85'])).

thf('87',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['81','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZDoUo9mUCi
% 0.13/0.36  % Computer   : n024.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 18:27:36 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.41/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.62  % Solved by: fo/fo7.sh
% 0.41/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.62  % done 105 iterations in 0.148s
% 0.41/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.62  % SZS output start Refutation
% 0.41/0.62  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.41/0.62  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.41/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.62  thf(sk_D_type, type, sk_D: $i).
% 0.41/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.62  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.41/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.41/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.41/0.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.41/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.62  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.41/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.62  thf(sk_C_type, type, sk_C: $i > $i).
% 0.41/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.41/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.41/0.62  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.41/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.62  thf(sk_B_type, type, sk_B: $i > $i).
% 0.41/0.62  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.41/0.62  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.41/0.62  thf(t77_funct_2, conjecture,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.41/0.62         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.41/0.62       ( ( v2_funct_1 @ B ) <=>
% 0.41/0.62         ( ![C:$i,D:$i]:
% 0.41/0.62           ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.41/0.62               ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.41/0.62             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.41/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.62    (~( ![A:$i,B:$i]:
% 0.41/0.62        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.41/0.62            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.41/0.62          ( ( v2_funct_1 @ B ) <=>
% 0.41/0.62            ( ![C:$i,D:$i]:
% 0.41/0.62              ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.41/0.62                  ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.41/0.62                ( ( C ) = ( D ) ) ) ) ) ) )),
% 0.41/0.62    inference('cnf.neg', [status(esa)], [t77_funct_2])).
% 0.41/0.62  thf('0', plain,
% 0.41/0.62      ((((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D))
% 0.41/0.62        | ~ (v2_funct_1 @ sk_B_1))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('1', plain,
% 0.41/0.62      ((((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D)))
% 0.41/0.62         <= ((((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D))))),
% 0.41/0.62      inference('split', [status(esa)], ['0'])).
% 0.41/0.62  thf('2', plain,
% 0.41/0.62      (![X17 : $i, X18 : $i]:
% 0.41/0.62         (((X18) = (X17))
% 0.41/0.62          | ((k1_funct_1 @ sk_B_1 @ X18) != (k1_funct_1 @ sk_B_1 @ X17))
% 0.41/0.62          | ~ (r2_hidden @ X17 @ sk_A)
% 0.41/0.62          | ~ (r2_hidden @ X18 @ sk_A)
% 0.41/0.62          | (v2_funct_1 @ sk_B_1))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('3', plain,
% 0.41/0.62      (((v2_funct_1 @ sk_B_1)) | 
% 0.41/0.62       (![X17 : $i, X18 : $i]:
% 0.41/0.62          (((X18) = (X17))
% 0.41/0.62           | ((k1_funct_1 @ sk_B_1 @ X18) != (k1_funct_1 @ sk_B_1 @ X17))
% 0.41/0.62           | ~ (r2_hidden @ X17 @ sk_A)
% 0.41/0.62           | ~ (r2_hidden @ X18 @ sk_A)))),
% 0.41/0.62      inference('split', [status(esa)], ['2'])).
% 0.41/0.62  thf('4', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(d1_funct_2, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i]:
% 0.41/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.62       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.41/0.62           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.41/0.62             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.41/0.62         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.41/0.62           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.41/0.62             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.41/0.62  thf(zf_stmt_1, axiom,
% 0.41/0.62    (![C:$i,B:$i,A:$i]:
% 0.41/0.62     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.41/0.62       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.41/0.62  thf('5', plain,
% 0.41/0.62      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.41/0.62         (~ (v1_funct_2 @ X13 @ X11 @ X12)
% 0.41/0.62          | ((X11) = (k1_relset_1 @ X11 @ X12 @ X13))
% 0.41/0.62          | ~ (zip_tseitin_1 @ X13 @ X12 @ X11))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.41/0.62  thf('6', plain,
% 0.41/0.62      ((~ (zip_tseitin_1 @ sk_B_1 @ sk_A @ sk_A)
% 0.41/0.62        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_A @ sk_B_1)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['4', '5'])).
% 0.41/0.62  thf('7', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.41/0.62  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.41/0.62  thf(zf_stmt_4, axiom,
% 0.41/0.62    (![B:$i,A:$i]:
% 0.41/0.62     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.41/0.62       ( zip_tseitin_0 @ B @ A ) ))).
% 0.41/0.62  thf(zf_stmt_5, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i]:
% 0.41/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.62       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.41/0.62         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.41/0.62           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.41/0.62             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.41/0.62  thf('8', plain,
% 0.41/0.62      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.41/0.62         (~ (zip_tseitin_0 @ X14 @ X15)
% 0.41/0.62          | (zip_tseitin_1 @ X16 @ X14 @ X15)
% 0.41/0.62          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X14))))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.41/0.62  thf('9', plain,
% 0.41/0.62      (((zip_tseitin_1 @ sk_B_1 @ sk_A @ sk_A)
% 0.41/0.62        | ~ (zip_tseitin_0 @ sk_A @ sk_A))),
% 0.41/0.62      inference('sup-', [status(thm)], ['7', '8'])).
% 0.41/0.62  thf('10', plain,
% 0.41/0.62      (![X9 : $i, X10 : $i]:
% 0.41/0.62         ((zip_tseitin_0 @ X9 @ X10) | ((X9) = (k1_xboole_0)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.41/0.62  thf('11', plain,
% 0.41/0.62      (![X9 : $i, X10 : $i]:
% 0.41/0.62         ((zip_tseitin_0 @ X9 @ X10) | ((X10) != (k1_xboole_0)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.41/0.62  thf('12', plain, (![X9 : $i]: (zip_tseitin_0 @ X9 @ k1_xboole_0)),
% 0.41/0.62      inference('simplify', [status(thm)], ['11'])).
% 0.41/0.62  thf('13', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.62         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 0.41/0.62      inference('sup+', [status(thm)], ['10', '12'])).
% 0.41/0.62  thf('14', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 0.41/0.62      inference('eq_fact', [status(thm)], ['13'])).
% 0.41/0.62  thf('15', plain, ((zip_tseitin_1 @ sk_B_1 @ sk_A @ sk_A)),
% 0.41/0.62      inference('demod', [status(thm)], ['9', '14'])).
% 0.41/0.62  thf('16', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(redefinition_k1_relset_1, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i]:
% 0.41/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.62       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.41/0.62  thf('17', plain,
% 0.41/0.62      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.41/0.62         (((k1_relset_1 @ X7 @ X8 @ X6) = (k1_relat_1 @ X6))
% 0.41/0.62          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.41/0.62      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.41/0.62  thf('18', plain,
% 0.41/0.62      (((k1_relset_1 @ sk_A @ sk_A @ sk_B_1) = (k1_relat_1 @ sk_B_1))),
% 0.41/0.62      inference('sup-', [status(thm)], ['16', '17'])).
% 0.41/0.62  thf('19', plain, (((sk_A) = (k1_relat_1 @ sk_B_1))),
% 0.41/0.62      inference('demod', [status(thm)], ['6', '15', '18'])).
% 0.41/0.62  thf(d8_funct_1, axiom,
% 0.41/0.62    (![A:$i]:
% 0.41/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.41/0.62       ( ( v2_funct_1 @ A ) <=>
% 0.41/0.62         ( ![B:$i,C:$i]:
% 0.41/0.62           ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 0.41/0.62               ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.41/0.62               ( ( k1_funct_1 @ A @ B ) = ( k1_funct_1 @ A @ C ) ) ) =>
% 0.41/0.62             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.41/0.62  thf('20', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         ((r2_hidden @ (sk_C @ X0) @ (k1_relat_1 @ X0))
% 0.41/0.62          | (v2_funct_1 @ X0)
% 0.41/0.62          | ~ (v1_funct_1 @ X0)
% 0.41/0.62          | ~ (v1_relat_1 @ X0))),
% 0.41/0.62      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.41/0.62  thf('21', plain,
% 0.41/0.62      (((r2_hidden @ (sk_C @ sk_B_1) @ sk_A)
% 0.41/0.62        | ~ (v1_relat_1 @ sk_B_1)
% 0.41/0.62        | ~ (v1_funct_1 @ sk_B_1)
% 0.41/0.62        | (v2_funct_1 @ sk_B_1))),
% 0.41/0.62      inference('sup+', [status(thm)], ['19', '20'])).
% 0.41/0.62  thf('22', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(cc1_relset_1, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i]:
% 0.41/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.62       ( v1_relat_1 @ C ) ))).
% 0.41/0.62  thf('23', plain,
% 0.41/0.62      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.41/0.62         ((v1_relat_1 @ X3)
% 0.41/0.62          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 0.41/0.62      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.41/0.62  thf('24', plain, ((v1_relat_1 @ sk_B_1)),
% 0.41/0.62      inference('sup-', [status(thm)], ['22', '23'])).
% 0.41/0.62  thf('25', plain, ((v1_funct_1 @ sk_B_1)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('26', plain,
% 0.41/0.62      (((r2_hidden @ (sk_C @ sk_B_1) @ sk_A) | (v2_funct_1 @ sk_B_1))),
% 0.41/0.62      inference('demod', [status(thm)], ['21', '24', '25'])).
% 0.41/0.62  thf('27', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         (((k1_funct_1 @ X0 @ (sk_B @ X0)) = (k1_funct_1 @ X0 @ (sk_C @ X0)))
% 0.41/0.62          | (v2_funct_1 @ X0)
% 0.41/0.62          | ~ (v1_funct_1 @ X0)
% 0.41/0.62          | ~ (v1_relat_1 @ X0))),
% 0.41/0.62      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.41/0.62  thf('28', plain,
% 0.41/0.62      ((![X17 : $i, X18 : $i]:
% 0.41/0.62          (((X18) = (X17))
% 0.41/0.62           | ((k1_funct_1 @ sk_B_1 @ X18) != (k1_funct_1 @ sk_B_1 @ X17))
% 0.41/0.62           | ~ (r2_hidden @ X17 @ sk_A)
% 0.41/0.62           | ~ (r2_hidden @ X18 @ sk_A)))
% 0.41/0.62         <= ((![X17 : $i, X18 : $i]:
% 0.41/0.62                (((X18) = (X17))
% 0.41/0.62                 | ((k1_funct_1 @ sk_B_1 @ X18) != (k1_funct_1 @ sk_B_1 @ X17))
% 0.41/0.62                 | ~ (r2_hidden @ X17 @ sk_A)
% 0.41/0.62                 | ~ (r2_hidden @ X18 @ sk_A))))),
% 0.41/0.62      inference('split', [status(esa)], ['2'])).
% 0.41/0.62  thf('29', plain,
% 0.41/0.62      ((![X0 : $i]:
% 0.41/0.62          (((k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1))
% 0.41/0.62             != (k1_funct_1 @ sk_B_1 @ X0))
% 0.41/0.62           | ~ (v1_relat_1 @ sk_B_1)
% 0.41/0.62           | ~ (v1_funct_1 @ sk_B_1)
% 0.41/0.62           | (v2_funct_1 @ sk_B_1)
% 0.41/0.62           | ~ (r2_hidden @ (sk_C @ sk_B_1) @ sk_A)
% 0.41/0.62           | ~ (r2_hidden @ X0 @ sk_A)
% 0.41/0.62           | ((sk_C @ sk_B_1) = (X0))))
% 0.41/0.62         <= ((![X17 : $i, X18 : $i]:
% 0.41/0.62                (((X18) = (X17))
% 0.41/0.62                 | ((k1_funct_1 @ sk_B_1 @ X18) != (k1_funct_1 @ sk_B_1 @ X17))
% 0.41/0.62                 | ~ (r2_hidden @ X17 @ sk_A)
% 0.41/0.62                 | ~ (r2_hidden @ X18 @ sk_A))))),
% 0.41/0.62      inference('sup-', [status(thm)], ['27', '28'])).
% 0.41/0.62  thf('30', plain, ((v1_funct_1 @ sk_B_1)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('31', plain,
% 0.41/0.62      ((![X0 : $i]:
% 0.41/0.62          (((k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1))
% 0.41/0.62             != (k1_funct_1 @ sk_B_1 @ X0))
% 0.41/0.62           | ~ (v1_relat_1 @ sk_B_1)
% 0.41/0.62           | (v2_funct_1 @ sk_B_1)
% 0.41/0.62           | ~ (r2_hidden @ (sk_C @ sk_B_1) @ sk_A)
% 0.41/0.62           | ~ (r2_hidden @ X0 @ sk_A)
% 0.41/0.62           | ((sk_C @ sk_B_1) = (X0))))
% 0.41/0.62         <= ((![X17 : $i, X18 : $i]:
% 0.41/0.62                (((X18) = (X17))
% 0.41/0.62                 | ((k1_funct_1 @ sk_B_1 @ X18) != (k1_funct_1 @ sk_B_1 @ X17))
% 0.41/0.62                 | ~ (r2_hidden @ X17 @ sk_A)
% 0.41/0.62                 | ~ (r2_hidden @ X18 @ sk_A))))),
% 0.41/0.62      inference('demod', [status(thm)], ['29', '30'])).
% 0.41/0.62  thf('32', plain, ((v1_relat_1 @ sk_B_1)),
% 0.41/0.62      inference('sup-', [status(thm)], ['22', '23'])).
% 0.41/0.62  thf('33', plain,
% 0.41/0.62      ((![X0 : $i]:
% 0.41/0.62          (((k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1))
% 0.41/0.62             != (k1_funct_1 @ sk_B_1 @ X0))
% 0.41/0.62           | (v2_funct_1 @ sk_B_1)
% 0.41/0.62           | ~ (r2_hidden @ (sk_C @ sk_B_1) @ sk_A)
% 0.41/0.62           | ~ (r2_hidden @ X0 @ sk_A)
% 0.41/0.62           | ((sk_C @ sk_B_1) = (X0))))
% 0.41/0.62         <= ((![X17 : $i, X18 : $i]:
% 0.41/0.62                (((X18) = (X17))
% 0.41/0.62                 | ((k1_funct_1 @ sk_B_1 @ X18) != (k1_funct_1 @ sk_B_1 @ X17))
% 0.41/0.62                 | ~ (r2_hidden @ X17 @ sk_A)
% 0.41/0.62                 | ~ (r2_hidden @ X18 @ sk_A))))),
% 0.41/0.62      inference('demod', [status(thm)], ['31', '32'])).
% 0.41/0.62  thf('34', plain,
% 0.41/0.62      ((![X0 : $i]:
% 0.41/0.62          ((v2_funct_1 @ sk_B_1)
% 0.41/0.62           | ((sk_C @ sk_B_1) = (X0))
% 0.41/0.62           | ~ (r2_hidden @ X0 @ sk_A)
% 0.41/0.62           | (v2_funct_1 @ sk_B_1)
% 0.41/0.62           | ((k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1))
% 0.41/0.62               != (k1_funct_1 @ sk_B_1 @ X0))))
% 0.41/0.62         <= ((![X17 : $i, X18 : $i]:
% 0.41/0.62                (((X18) = (X17))
% 0.41/0.62                 | ((k1_funct_1 @ sk_B_1 @ X18) != (k1_funct_1 @ sk_B_1 @ X17))
% 0.41/0.62                 | ~ (r2_hidden @ X17 @ sk_A)
% 0.41/0.62                 | ~ (r2_hidden @ X18 @ sk_A))))),
% 0.41/0.62      inference('sup-', [status(thm)], ['26', '33'])).
% 0.41/0.62  thf('35', plain,
% 0.41/0.62      ((![X0 : $i]:
% 0.41/0.62          (((k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1))
% 0.41/0.62             != (k1_funct_1 @ sk_B_1 @ X0))
% 0.41/0.62           | ~ (r2_hidden @ X0 @ sk_A)
% 0.41/0.62           | ((sk_C @ sk_B_1) = (X0))
% 0.41/0.62           | (v2_funct_1 @ sk_B_1)))
% 0.41/0.62         <= ((![X17 : $i, X18 : $i]:
% 0.41/0.62                (((X18) = (X17))
% 0.41/0.62                 | ((k1_funct_1 @ sk_B_1 @ X18) != (k1_funct_1 @ sk_B_1 @ X17))
% 0.41/0.62                 | ~ (r2_hidden @ X17 @ sk_A)
% 0.41/0.62                 | ~ (r2_hidden @ X18 @ sk_A))))),
% 0.41/0.62      inference('simplify', [status(thm)], ['34'])).
% 0.41/0.62  thf('36', plain,
% 0.41/0.62      ((((v2_funct_1 @ sk_B_1)
% 0.41/0.62         | ((sk_C @ sk_B_1) = (sk_B @ sk_B_1))
% 0.41/0.62         | ~ (r2_hidden @ (sk_B @ sk_B_1) @ sk_A)))
% 0.41/0.62         <= ((![X17 : $i, X18 : $i]:
% 0.41/0.62                (((X18) = (X17))
% 0.41/0.62                 | ((k1_funct_1 @ sk_B_1 @ X18) != (k1_funct_1 @ sk_B_1 @ X17))
% 0.41/0.62                 | ~ (r2_hidden @ X17 @ sk_A)
% 0.41/0.62                 | ~ (r2_hidden @ X18 @ sk_A))))),
% 0.41/0.62      inference('eq_res', [status(thm)], ['35'])).
% 0.41/0.62  thf('37', plain, (((sk_A) = (k1_relat_1 @ sk_B_1))),
% 0.41/0.62      inference('demod', [status(thm)], ['6', '15', '18'])).
% 0.41/0.62  thf('38', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         ((r2_hidden @ (sk_B @ X0) @ (k1_relat_1 @ X0))
% 0.41/0.62          | (v2_funct_1 @ X0)
% 0.41/0.62          | ~ (v1_funct_1 @ X0)
% 0.41/0.62          | ~ (v1_relat_1 @ X0))),
% 0.41/0.62      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.41/0.62  thf('39', plain,
% 0.41/0.62      (((r2_hidden @ (sk_B @ sk_B_1) @ sk_A)
% 0.41/0.62        | ~ (v1_relat_1 @ sk_B_1)
% 0.41/0.62        | ~ (v1_funct_1 @ sk_B_1)
% 0.41/0.62        | (v2_funct_1 @ sk_B_1))),
% 0.41/0.62      inference('sup+', [status(thm)], ['37', '38'])).
% 0.41/0.62  thf('40', plain, ((v1_relat_1 @ sk_B_1)),
% 0.41/0.62      inference('sup-', [status(thm)], ['22', '23'])).
% 0.41/0.62  thf('41', plain, ((v1_funct_1 @ sk_B_1)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('42', plain,
% 0.41/0.62      (((r2_hidden @ (sk_B @ sk_B_1) @ sk_A) | (v2_funct_1 @ sk_B_1))),
% 0.41/0.62      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.41/0.62  thf('43', plain,
% 0.41/0.62      (((((sk_C @ sk_B_1) = (sk_B @ sk_B_1)) | (v2_funct_1 @ sk_B_1)))
% 0.41/0.62         <= ((![X17 : $i, X18 : $i]:
% 0.41/0.62                (((X18) = (X17))
% 0.41/0.62                 | ((k1_funct_1 @ sk_B_1 @ X18) != (k1_funct_1 @ sk_B_1 @ X17))
% 0.41/0.62                 | ~ (r2_hidden @ X17 @ sk_A)
% 0.41/0.62                 | ~ (r2_hidden @ X18 @ sk_A))))),
% 0.41/0.62      inference('clc', [status(thm)], ['36', '42'])).
% 0.41/0.62  thf('44', plain, (((r2_hidden @ sk_C_1 @ sk_A) | ~ (v2_funct_1 @ sk_B_1))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('45', plain, ((~ (v2_funct_1 @ sk_B_1)) <= (~ ((v2_funct_1 @ sk_B_1)))),
% 0.41/0.62      inference('split', [status(esa)], ['44'])).
% 0.41/0.62  thf('46', plain,
% 0.41/0.62      ((((sk_C @ sk_B_1) = (sk_B @ sk_B_1)))
% 0.41/0.62         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.41/0.62             (![X17 : $i, X18 : $i]:
% 0.41/0.62                (((X18) = (X17))
% 0.41/0.62                 | ((k1_funct_1 @ sk_B_1 @ X18) != (k1_funct_1 @ sk_B_1 @ X17))
% 0.41/0.62                 | ~ (r2_hidden @ X17 @ sk_A)
% 0.41/0.62                 | ~ (r2_hidden @ X18 @ sk_A))))),
% 0.41/0.62      inference('sup-', [status(thm)], ['43', '45'])).
% 0.41/0.62  thf('47', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         (((sk_B @ X0) != (sk_C @ X0))
% 0.41/0.62          | (v2_funct_1 @ X0)
% 0.41/0.62          | ~ (v1_funct_1 @ X0)
% 0.41/0.62          | ~ (v1_relat_1 @ X0))),
% 0.41/0.62      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.41/0.62  thf('48', plain,
% 0.41/0.62      (((((sk_B @ sk_B_1) != (sk_B @ sk_B_1))
% 0.41/0.62         | ~ (v1_relat_1 @ sk_B_1)
% 0.41/0.62         | ~ (v1_funct_1 @ sk_B_1)
% 0.41/0.62         | (v2_funct_1 @ sk_B_1)))
% 0.41/0.62         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.41/0.62             (![X17 : $i, X18 : $i]:
% 0.41/0.62                (((X18) = (X17))
% 0.41/0.62                 | ((k1_funct_1 @ sk_B_1 @ X18) != (k1_funct_1 @ sk_B_1 @ X17))
% 0.41/0.62                 | ~ (r2_hidden @ X17 @ sk_A)
% 0.41/0.62                 | ~ (r2_hidden @ X18 @ sk_A))))),
% 0.41/0.62      inference('sup-', [status(thm)], ['46', '47'])).
% 0.41/0.62  thf('49', plain, ((v1_relat_1 @ sk_B_1)),
% 0.41/0.62      inference('sup-', [status(thm)], ['22', '23'])).
% 0.41/0.62  thf('50', plain, ((v1_funct_1 @ sk_B_1)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('51', plain,
% 0.41/0.62      (((((sk_B @ sk_B_1) != (sk_B @ sk_B_1)) | (v2_funct_1 @ sk_B_1)))
% 0.41/0.62         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.41/0.62             (![X17 : $i, X18 : $i]:
% 0.41/0.62                (((X18) = (X17))
% 0.41/0.62                 | ((k1_funct_1 @ sk_B_1 @ X18) != (k1_funct_1 @ sk_B_1 @ X17))
% 0.41/0.62                 | ~ (r2_hidden @ X17 @ sk_A)
% 0.41/0.62                 | ~ (r2_hidden @ X18 @ sk_A))))),
% 0.41/0.62      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.41/0.62  thf('52', plain,
% 0.41/0.62      (((v2_funct_1 @ sk_B_1))
% 0.41/0.62         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.41/0.63             (![X17 : $i, X18 : $i]:
% 0.41/0.63                (((X18) = (X17))
% 0.41/0.63                 | ((k1_funct_1 @ sk_B_1 @ X18) != (k1_funct_1 @ sk_B_1 @ X17))
% 0.41/0.63                 | ~ (r2_hidden @ X17 @ sk_A)
% 0.41/0.63                 | ~ (r2_hidden @ X18 @ sk_A))))),
% 0.41/0.63      inference('simplify', [status(thm)], ['51'])).
% 0.41/0.63  thf('53', plain, ((~ (v2_funct_1 @ sk_B_1)) <= (~ ((v2_funct_1 @ sk_B_1)))),
% 0.41/0.63      inference('split', [status(esa)], ['44'])).
% 0.41/0.63  thf('54', plain,
% 0.41/0.63      (~
% 0.41/0.63       (![X17 : $i, X18 : $i]:
% 0.41/0.63          (((X18) = (X17))
% 0.41/0.63           | ((k1_funct_1 @ sk_B_1 @ X18) != (k1_funct_1 @ sk_B_1 @ X17))
% 0.41/0.63           | ~ (r2_hidden @ X17 @ sk_A)
% 0.41/0.63           | ~ (r2_hidden @ X18 @ sk_A))) | 
% 0.41/0.63       ((v2_funct_1 @ sk_B_1))),
% 0.41/0.63      inference('sup-', [status(thm)], ['52', '53'])).
% 0.41/0.63  thf('55', plain,
% 0.41/0.63      ((((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D))) | 
% 0.41/0.63       ~ ((v2_funct_1 @ sk_B_1))),
% 0.41/0.63      inference('split', [status(esa)], ['0'])).
% 0.41/0.63  thf('56', plain,
% 0.41/0.63      ((((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D)))),
% 0.41/0.63      inference('sat_resolution*', [status(thm)], ['3', '54', '55'])).
% 0.41/0.63  thf('57', plain,
% 0.41/0.63      (((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D))),
% 0.41/0.63      inference('simpl_trail', [status(thm)], ['1', '56'])).
% 0.41/0.63  thf('58', plain, (((sk_A) = (k1_relat_1 @ sk_B_1))),
% 0.41/0.63      inference('demod', [status(thm)], ['6', '15', '18'])).
% 0.41/0.63  thf('59', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.63         (~ (v2_funct_1 @ X0)
% 0.41/0.63          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.41/0.63          | ~ (r2_hidden @ X2 @ (k1_relat_1 @ X0))
% 0.41/0.63          | ((k1_funct_1 @ X0 @ X1) != (k1_funct_1 @ X0 @ X2))
% 0.41/0.63          | ((X1) = (X2))
% 0.41/0.63          | ~ (v1_funct_1 @ X0)
% 0.41/0.63          | ~ (v1_relat_1 @ X0))),
% 0.41/0.63      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.41/0.63  thf('60', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i]:
% 0.41/0.63         (~ (r2_hidden @ X0 @ sk_A)
% 0.41/0.63          | ~ (v1_relat_1 @ sk_B_1)
% 0.41/0.63          | ~ (v1_funct_1 @ sk_B_1)
% 0.41/0.63          | ((X0) = (X1))
% 0.41/0.63          | ((k1_funct_1 @ sk_B_1 @ X0) != (k1_funct_1 @ sk_B_1 @ X1))
% 0.41/0.63          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1))
% 0.41/0.63          | ~ (v2_funct_1 @ sk_B_1))),
% 0.41/0.63      inference('sup-', [status(thm)], ['58', '59'])).
% 0.41/0.63  thf('61', plain, ((v1_relat_1 @ sk_B_1)),
% 0.41/0.63      inference('sup-', [status(thm)], ['22', '23'])).
% 0.41/0.63  thf('62', plain, ((v1_funct_1 @ sk_B_1)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('63', plain, (((sk_A) = (k1_relat_1 @ sk_B_1))),
% 0.41/0.63      inference('demod', [status(thm)], ['6', '15', '18'])).
% 0.41/0.63  thf('64', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i]:
% 0.41/0.63         (~ (r2_hidden @ X0 @ sk_A)
% 0.41/0.63          | ((X0) = (X1))
% 0.41/0.63          | ((k1_funct_1 @ sk_B_1 @ X0) != (k1_funct_1 @ sk_B_1 @ X1))
% 0.41/0.63          | ~ (r2_hidden @ X1 @ sk_A)
% 0.41/0.63          | ~ (v2_funct_1 @ sk_B_1))),
% 0.41/0.63      inference('demod', [status(thm)], ['60', '61', '62', '63'])).
% 0.41/0.63  thf('65', plain, (((v2_funct_1 @ sk_B_1)) <= (((v2_funct_1 @ sk_B_1)))),
% 0.41/0.63      inference('split', [status(esa)], ['2'])).
% 0.41/0.63  thf('66', plain, (((v2_funct_1 @ sk_B_1))),
% 0.41/0.63      inference('sat_resolution*', [status(thm)], ['3', '54'])).
% 0.41/0.63  thf('67', plain, ((v2_funct_1 @ sk_B_1)),
% 0.41/0.63      inference('simpl_trail', [status(thm)], ['65', '66'])).
% 0.41/0.63  thf('68', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i]:
% 0.41/0.63         (~ (r2_hidden @ X0 @ sk_A)
% 0.41/0.63          | ((X0) = (X1))
% 0.41/0.63          | ((k1_funct_1 @ sk_B_1 @ X0) != (k1_funct_1 @ sk_B_1 @ X1))
% 0.41/0.63          | ~ (r2_hidden @ X1 @ sk_A))),
% 0.41/0.63      inference('demod', [status(thm)], ['64', '67'])).
% 0.41/0.63  thf('69', plain,
% 0.41/0.63      (![X0 : $i]:
% 0.41/0.63         (((k1_funct_1 @ sk_B_1 @ sk_C_1) != (k1_funct_1 @ sk_B_1 @ X0))
% 0.41/0.63          | ~ (r2_hidden @ X0 @ sk_A)
% 0.41/0.63          | ((sk_D) = (X0))
% 0.41/0.63          | ~ (r2_hidden @ sk_D @ sk_A))),
% 0.41/0.63      inference('sup-', [status(thm)], ['57', '68'])).
% 0.41/0.63  thf('70', plain, (((r2_hidden @ sk_D @ sk_A) | ~ (v2_funct_1 @ sk_B_1))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('71', plain,
% 0.41/0.63      (((r2_hidden @ sk_D @ sk_A)) <= (((r2_hidden @ sk_D @ sk_A)))),
% 0.41/0.63      inference('split', [status(esa)], ['70'])).
% 0.41/0.63  thf('72', plain, (((r2_hidden @ sk_D @ sk_A)) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.41/0.63      inference('split', [status(esa)], ['70'])).
% 0.41/0.63  thf('73', plain, (((r2_hidden @ sk_D @ sk_A))),
% 0.41/0.63      inference('sat_resolution*', [status(thm)], ['3', '54', '72'])).
% 0.41/0.63  thf('74', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.41/0.63      inference('simpl_trail', [status(thm)], ['71', '73'])).
% 0.41/0.63  thf('75', plain,
% 0.41/0.63      (![X0 : $i]:
% 0.41/0.63         (((k1_funct_1 @ sk_B_1 @ sk_C_1) != (k1_funct_1 @ sk_B_1 @ X0))
% 0.41/0.63          | ~ (r2_hidden @ X0 @ sk_A)
% 0.41/0.63          | ((sk_D) = (X0)))),
% 0.41/0.63      inference('demod', [status(thm)], ['69', '74'])).
% 0.41/0.63  thf('76', plain, ((((sk_D) = (sk_C_1)) | ~ (r2_hidden @ sk_C_1 @ sk_A))),
% 0.41/0.63      inference('eq_res', [status(thm)], ['75'])).
% 0.41/0.63  thf('77', plain,
% 0.41/0.63      (((r2_hidden @ sk_C_1 @ sk_A)) <= (((r2_hidden @ sk_C_1 @ sk_A)))),
% 0.41/0.63      inference('split', [status(esa)], ['44'])).
% 0.41/0.63  thf('78', plain, (((r2_hidden @ sk_C_1 @ sk_A)) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.41/0.63      inference('split', [status(esa)], ['44'])).
% 0.41/0.63  thf('79', plain, (((r2_hidden @ sk_C_1 @ sk_A))),
% 0.41/0.63      inference('sat_resolution*', [status(thm)], ['3', '54', '78'])).
% 0.41/0.63  thf('80', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.41/0.63      inference('simpl_trail', [status(thm)], ['77', '79'])).
% 0.41/0.63  thf('81', plain, (((sk_D) = (sk_C_1))),
% 0.41/0.63      inference('demod', [status(thm)], ['76', '80'])).
% 0.41/0.63  thf('82', plain, ((((sk_C_1) != (sk_D)) | ~ (v2_funct_1 @ sk_B_1))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('83', plain, ((((sk_C_1) != (sk_D))) <= (~ (((sk_C_1) = (sk_D))))),
% 0.41/0.63      inference('split', [status(esa)], ['82'])).
% 0.41/0.63  thf('84', plain, (~ (((sk_C_1) = (sk_D))) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.41/0.63      inference('split', [status(esa)], ['82'])).
% 0.41/0.63  thf('85', plain, (~ (((sk_C_1) = (sk_D)))),
% 0.41/0.63      inference('sat_resolution*', [status(thm)], ['3', '54', '84'])).
% 0.41/0.63  thf('86', plain, (((sk_C_1) != (sk_D))),
% 0.41/0.63      inference('simpl_trail', [status(thm)], ['83', '85'])).
% 0.41/0.63  thf('87', plain, ($false),
% 0.41/0.63      inference('simplify_reflect-', [status(thm)], ['81', '86'])).
% 0.41/0.63  
% 0.41/0.63  % SZS output end Refutation
% 0.41/0.63  
% 0.46/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
