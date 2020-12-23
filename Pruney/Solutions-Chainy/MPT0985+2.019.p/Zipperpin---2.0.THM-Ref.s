%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BRiHxZPTZ8

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:29 EST 2020

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :  195 (1022 expanded)
%              Number of leaves         :   50 ( 318 expanded)
%              Depth                    :   20
%              Number of atoms          : 1298 (15567 expanded)
%              Number of equality atoms :   71 ( 577 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t31_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ C )
          & ( ( k2_relset_1 @ A @ B @ C )
            = B ) )
       => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
          & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
          & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( v2_funct_1 @ C )
            & ( ( k2_relset_1 @ A @ B @ C )
              = B ) )
         => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
            & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
            & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_2 ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_2 ) @ sk_B_1 @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k2_funct_1 @ X19 )
        = ( k4_relat_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ( ( k2_funct_1 @ sk_C_2 )
      = ( k4_relat_1 @ sk_C_2 ) )
    | ~ ( v2_funct_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v2_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ( ( k2_funct_1 @ sk_C_2 )
      = ( k4_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('8',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('9',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k2_funct_1 @ sk_C_2 )
    = ( k4_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,
    ( ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['7','8'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('13',plain,(
    ! [X20: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('14',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_2 ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('15',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,
    ( ( k2_funct_1 @ sk_C_2 )
    = ( k4_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('20',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_2 ) @ sk_B_1 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_2 ) @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('21',plain,
    ( ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C_2 ) @ sk_B_1 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_2 ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

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

thf('22',plain,(
    ! [X34: $i,X35: $i] :
      ( ( zip_tseitin_0 @ X34 @ X35 )
      | ( X34 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('23',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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

thf('26',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( zip_tseitin_0 @ X39 @ X40 )
      | ( zip_tseitin_1 @ X41 @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('27',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_funct_2 @ X38 @ X36 @ X37 )
      | ( X36
        = ( k1_relset_1 @ X36 @ X37 @ X38 ) )
      | ~ ( zip_tseitin_1 @ X38 @ X37 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('31',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('33',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('34',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['31','34'])).

thf('36',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['28','35'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('37',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('38',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('39',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('40',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf(rc1_funct_2,axiom,(
    ! [A: $i,B: $i] :
    ? [C: $i] :
      ( ( v1_funct_2 @ C @ A @ B )
      & ( v1_funct_1 @ C )
      & ( v5_relat_1 @ C @ B )
      & ( v4_relat_1 @ C @ A )
      & ( v1_relat_1 @ C )
      & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) )).

thf('41',plain,(
    ! [X42: $i,X43: $i] :
      ( m1_subset_1 @ ( sk_C_1 @ X42 @ X43 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('42',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_xboole_0 @ X11 )
      | ~ ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( v1_xboole_0 @ ( sk_C_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( sk_C_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( sk_C_1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( sk_C_1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X42: $i,X43: $i] :
      ( v1_funct_2 @ ( sk_C_1 @ X42 @ X43 ) @ X43 @ X42 ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('50',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ X0 @ k1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ X2 @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['37','51'])).

thf('53',plain,
    ( ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C_2 ) @ sk_B_1 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_2 ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('54',plain,
    ( ( ~ ( v1_xboole_0 @ ( k4_relat_1 @ sk_C_2 ) )
      | ~ ( v1_xboole_0 @ sk_B_1 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_2 ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k2_funct_1 @ sk_C_2 )
    = ( k4_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['6','9'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('56',plain,(
    ! [X21: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relat_1 @ X21 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('57',plain,
    ( ( ( k2_relat_1 @ sk_C_2 )
      = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_2 ) ) )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ~ ( v2_funct_1 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('59',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v2_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( k2_relat_1 @ sk_C_2 )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['57','58','59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('63',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k2_relset_1 @ X32 @ X33 @ X31 )
        = ( k2_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('64',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 )
    = sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( k2_relat_1 @ sk_C_2 )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,
    ( sk_B_1
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['61','66'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('68',plain,(
    ! [X44: $i] :
      ( ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X44 ) @ ( k2_relat_1 @ X44 ) ) ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('69',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_xboole_0 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X27 ) ) )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( k4_relat_1 @ sk_C_2 ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C_2 ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf('72',plain,
    ( ( k2_funct_1 @ sk_C_2 )
    = ( k4_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('73',plain,(
    ! [X20: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('74',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ sk_C_2 ) )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('76',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,
    ( ( k2_funct_1 @ sk_C_2 )
    = ( k4_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('79',plain,(
    ! [X20: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('80',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_C_2 ) )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('82',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( k4_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['71','77','83'])).

thf('85',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_2 ) @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['54','84'])).

thf('86',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_2 ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','85'])).

thf('87',plain,
    ( sk_B_1
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['61','66'])).

thf('88',plain,(
    ! [X44: $i] :
      ( ( v1_funct_2 @ X44 @ ( k1_relat_1 @ X44 ) @ ( k2_relat_1 @ X44 ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('89',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C_2 ) @ sk_B_1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C_2 ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C_2 ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( k2_funct_1 @ sk_C_2 )
    = ( k4_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('91',plain,(
    ! [X21: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k1_relat_1 @ X21 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('92',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_2 ) ) )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ~ ( v2_funct_1 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('94',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v2_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['92','93','94','95'])).

thf('97',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('98',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('99',plain,(
    v1_funct_2 @ ( k4_relat_1 @ sk_C_2 ) @ sk_B_1 @ ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['89','96','97','98'])).

thf('100',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C_2 ) @ sk_B_1 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_2 ) @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['86','99'])).

thf('101',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C_2 ) @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['21','100'])).

thf('102',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_2 ) @ sk_B_1 @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('103',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['18','101','102'])).

thf('104',plain,(
    ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['11','103'])).

thf('105',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['92','93','94','95'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('107',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('108',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('109',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['107','109'])).

thf('111',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_xboole_0 @ X11 )
      | ~ ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('113',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['110','113'])).

thf('115',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('116',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['106','116'])).

thf(fc14_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( ( v1_xboole_0 @ ( k4_relat_1 @ A ) )
        & ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) ) )).

thf('118',plain,(
    ! [X17: $i] :
      ( ( v1_xboole_0 @ ( k4_relat_1 @ X17 ) )
      | ~ ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc14_relat_1])).

thf('119',plain,
    ( ( k2_funct_1 @ sk_C_2 )
    = ( k4_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['6','9'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('120',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('123',plain,(
    ! [X13: $i,X15: $i] :
      ( ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('126',plain,
    ( ~ ( v1_xboole_0 @ ( k2_funct_1 @ sk_C_2 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,
    ( ~ ( v1_xboole_0 @ ( k4_relat_1 @ sk_C_2 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['119','126'])).

thf('128',plain,
    ( ~ ( v1_xboole_0 @ sk_C_2 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['118','127'])).

thf('129',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ sk_B_1 @ X0 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['117','128'])).

thf('130',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('131',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['31','34'])).

thf('133',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['18','101','102'])).

thf('135',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['133','134'])).

thf('136',plain,
    ( sk_A
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['105','135'])).

thf('137',plain,(
    ! [X44: $i] :
      ( ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X44 ) @ ( k2_relat_1 @ X44 ) ) ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('138',plain,
    ( ( m1_subset_1 @ ( k4_relat_1 @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k4_relat_1 @ sk_C_2 ) ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C_2 ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['136','137'])).

thf('139',plain,
    ( sk_B_1
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['61','66'])).

thf('140',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('141',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('142',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['138','139','140','141'])).

thf('143',plain,(
    $false ),
    inference(demod,[status(thm)],['104','142'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BRiHxZPTZ8
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 11:20:00 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.77/0.96  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.77/0.96  % Solved by: fo/fo7.sh
% 0.77/0.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.77/0.96  % done 669 iterations in 0.491s
% 0.77/0.96  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.77/0.96  % SZS output start Refutation
% 0.77/0.96  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.77/0.96  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.77/0.96  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.77/0.96  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.77/0.96  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.77/0.96  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.77/0.96  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.77/0.96  thf(sk_A_type, type, sk_A: $i).
% 0.77/0.96  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.77/0.96  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.77/0.96  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.77/0.96  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.77/0.96  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.77/0.96  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.77/0.96  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.77/0.96  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.77/0.96  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.77/0.96  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.77/0.96  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.77/0.96  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.77/0.96  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.77/0.96  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.77/0.96  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.77/0.96  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.77/0.96  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.77/0.96  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.77/0.96  thf(t31_funct_2, conjecture,
% 0.77/0.96    (![A:$i,B:$i,C:$i]:
% 0.77/0.96     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.77/0.96         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.77/0.96       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.77/0.96         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.77/0.96           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.77/0.96           ( m1_subset_1 @
% 0.77/0.96             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.77/0.96  thf(zf_stmt_0, negated_conjecture,
% 0.77/0.96    (~( ![A:$i,B:$i,C:$i]:
% 0.77/0.96        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.77/0.96            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.77/0.96          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.77/0.96            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.77/0.96              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.77/0.96              ( m1_subset_1 @
% 0.77/0.96                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 0.77/0.96    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 0.77/0.96  thf('0', plain,
% 0.77/0.96      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_2))
% 0.77/0.96        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C_2) @ sk_B_1 @ sk_A)
% 0.77/0.96        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C_2) @ 
% 0.77/0.96             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('1', plain,
% 0.77/0.96      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C_2) @ 
% 0.77/0.96           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))
% 0.77/0.96         <= (~
% 0.77/0.96             ((m1_subset_1 @ (k2_funct_1 @ sk_C_2) @ 
% 0.77/0.96               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 0.77/0.96      inference('split', [status(esa)], ['0'])).
% 0.77/0.96  thf('2', plain, ((v1_funct_1 @ sk_C_2)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf(d9_funct_1, axiom,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.77/0.96       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.77/0.96  thf('3', plain,
% 0.77/0.96      (![X19 : $i]:
% 0.77/0.96         (~ (v2_funct_1 @ X19)
% 0.77/0.96          | ((k2_funct_1 @ X19) = (k4_relat_1 @ X19))
% 0.77/0.96          | ~ (v1_funct_1 @ X19)
% 0.77/0.96          | ~ (v1_relat_1 @ X19))),
% 0.77/0.96      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.77/0.96  thf('4', plain,
% 0.77/0.96      ((~ (v1_relat_1 @ sk_C_2)
% 0.77/0.96        | ((k2_funct_1 @ sk_C_2) = (k4_relat_1 @ sk_C_2))
% 0.77/0.96        | ~ (v2_funct_1 @ sk_C_2))),
% 0.77/0.96      inference('sup-', [status(thm)], ['2', '3'])).
% 0.77/0.96  thf('5', plain, ((v2_funct_1 @ sk_C_2)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('6', plain,
% 0.77/0.96      ((~ (v1_relat_1 @ sk_C_2)
% 0.77/0.96        | ((k2_funct_1 @ sk_C_2) = (k4_relat_1 @ sk_C_2)))),
% 0.77/0.96      inference('demod', [status(thm)], ['4', '5'])).
% 0.77/0.96  thf('7', plain,
% 0.77/0.96      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf(cc1_relset_1, axiom,
% 0.77/0.96    (![A:$i,B:$i,C:$i]:
% 0.77/0.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.77/0.96       ( v1_relat_1 @ C ) ))).
% 0.77/0.96  thf('8', plain,
% 0.77/0.96      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.77/0.96         ((v1_relat_1 @ X22)
% 0.77/0.96          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.77/0.96      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.77/0.96  thf('9', plain, ((v1_relat_1 @ sk_C_2)),
% 0.77/0.96      inference('sup-', [status(thm)], ['7', '8'])).
% 0.77/0.96  thf('10', plain, (((k2_funct_1 @ sk_C_2) = (k4_relat_1 @ sk_C_2))),
% 0.77/0.96      inference('demod', [status(thm)], ['6', '9'])).
% 0.77/0.96  thf('11', plain,
% 0.77/0.96      ((~ (m1_subset_1 @ (k4_relat_1 @ sk_C_2) @ 
% 0.77/0.96           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))
% 0.77/0.96         <= (~
% 0.77/0.96             ((m1_subset_1 @ (k2_funct_1 @ sk_C_2) @ 
% 0.77/0.96               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 0.77/0.96      inference('demod', [status(thm)], ['1', '10'])).
% 0.77/0.96  thf('12', plain, ((v1_relat_1 @ sk_C_2)),
% 0.77/0.96      inference('sup-', [status(thm)], ['7', '8'])).
% 0.77/0.96  thf(dt_k2_funct_1, axiom,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.77/0.96       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.77/0.96         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.77/0.96  thf('13', plain,
% 0.77/0.96      (![X20 : $i]:
% 0.77/0.96         ((v1_funct_1 @ (k2_funct_1 @ X20))
% 0.77/0.96          | ~ (v1_funct_1 @ X20)
% 0.77/0.96          | ~ (v1_relat_1 @ X20))),
% 0.77/0.96      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.77/0.96  thf('14', plain,
% 0.77/0.96      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_2)))
% 0.77/0.96         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_2))))),
% 0.77/0.96      inference('split', [status(esa)], ['0'])).
% 0.77/0.96  thf('15', plain,
% 0.77/0.96      (((~ (v1_relat_1 @ sk_C_2) | ~ (v1_funct_1 @ sk_C_2)))
% 0.77/0.96         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_2))))),
% 0.77/0.96      inference('sup-', [status(thm)], ['13', '14'])).
% 0.77/0.96  thf('16', plain, ((v1_funct_1 @ sk_C_2)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('17', plain,
% 0.77/0.96      ((~ (v1_relat_1 @ sk_C_2)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_2))))),
% 0.77/0.96      inference('demod', [status(thm)], ['15', '16'])).
% 0.77/0.96  thf('18', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C_2)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['12', '17'])).
% 0.77/0.96  thf('19', plain, (((k2_funct_1 @ sk_C_2) = (k4_relat_1 @ sk_C_2))),
% 0.77/0.96      inference('demod', [status(thm)], ['6', '9'])).
% 0.77/0.96  thf('20', plain,
% 0.77/0.96      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C_2) @ sk_B_1 @ sk_A))
% 0.77/0.96         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_2) @ sk_B_1 @ sk_A)))),
% 0.77/0.96      inference('split', [status(esa)], ['0'])).
% 0.77/0.96  thf('21', plain,
% 0.77/0.96      ((~ (v1_funct_2 @ (k4_relat_1 @ sk_C_2) @ sk_B_1 @ sk_A))
% 0.77/0.96         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_2) @ sk_B_1 @ sk_A)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['19', '20'])).
% 0.77/0.96  thf(d1_funct_2, axiom,
% 0.77/0.96    (![A:$i,B:$i,C:$i]:
% 0.77/0.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.77/0.96       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.77/0.96           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.77/0.96             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.77/0.96         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.77/0.96           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.77/0.96             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.77/0.96  thf(zf_stmt_1, axiom,
% 0.77/0.96    (![B:$i,A:$i]:
% 0.77/0.96     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.77/0.96       ( zip_tseitin_0 @ B @ A ) ))).
% 0.77/0.96  thf('22', plain,
% 0.77/0.96      (![X34 : $i, X35 : $i]:
% 0.77/0.96         ((zip_tseitin_0 @ X34 @ X35) | ((X34) = (k1_xboole_0)))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.77/0.96  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.77/0.96  thf('23', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.77/0.96      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.77/0.96  thf('24', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.77/0.96      inference('sup+', [status(thm)], ['22', '23'])).
% 0.77/0.96  thf('25', plain,
% 0.77/0.96      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.77/0.96  thf(zf_stmt_3, axiom,
% 0.77/0.96    (![C:$i,B:$i,A:$i]:
% 0.77/0.96     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.77/0.96       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.77/0.96  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.77/0.96  thf(zf_stmt_5, axiom,
% 0.77/0.96    (![A:$i,B:$i,C:$i]:
% 0.77/0.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.77/0.96       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.77/0.96         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.77/0.96           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.77/0.96             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.77/0.96  thf('26', plain,
% 0.77/0.96      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.77/0.96         (~ (zip_tseitin_0 @ X39 @ X40)
% 0.77/0.96          | (zip_tseitin_1 @ X41 @ X39 @ X40)
% 0.77/0.96          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39))))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.77/0.96  thf('27', plain,
% 0.77/0.96      (((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 0.77/0.96        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.77/0.96      inference('sup-', [status(thm)], ['25', '26'])).
% 0.77/0.96  thf('28', plain,
% 0.77/0.96      (((v1_xboole_0 @ sk_B_1) | (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A))),
% 0.77/0.96      inference('sup-', [status(thm)], ['24', '27'])).
% 0.77/0.96  thf('29', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('30', plain,
% 0.77/0.96      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.77/0.96         (~ (v1_funct_2 @ X38 @ X36 @ X37)
% 0.77/0.96          | ((X36) = (k1_relset_1 @ X36 @ X37 @ X38))
% 0.77/0.96          | ~ (zip_tseitin_1 @ X38 @ X37 @ X36))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.77/0.96  thf('31', plain,
% 0.77/0.96      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 0.77/0.96        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['29', '30'])).
% 0.77/0.96  thf('32', plain,
% 0.77/0.96      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf(redefinition_k1_relset_1, axiom,
% 0.77/0.96    (![A:$i,B:$i,C:$i]:
% 0.77/0.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.77/0.96       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.77/0.96  thf('33', plain,
% 0.77/0.96      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.77/0.96         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 0.77/0.96          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.77/0.96      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.77/0.96  thf('34', plain,
% 0.77/0.96      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 0.77/0.96      inference('sup-', [status(thm)], ['32', '33'])).
% 0.77/0.96  thf('35', plain,
% 0.77/0.96      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 0.77/0.96        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 0.77/0.96      inference('demod', [status(thm)], ['31', '34'])).
% 0.77/0.96  thf('36', plain,
% 0.77/0.96      (((v1_xboole_0 @ sk_B_1) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['28', '35'])).
% 0.77/0.96  thf(l13_xboole_0, axiom,
% 0.77/0.96    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.77/0.96  thf('37', plain,
% 0.77/0.96      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.77/0.96      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.77/0.96  thf('38', plain,
% 0.77/0.96      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.77/0.96      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.77/0.96  thf(t113_zfmisc_1, axiom,
% 0.77/0.96    (![A:$i,B:$i]:
% 0.77/0.96     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.77/0.96       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.77/0.96  thf('39', plain,
% 0.77/0.96      (![X9 : $i, X10 : $i]:
% 0.77/0.96         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 0.77/0.96      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.77/0.96  thf('40', plain,
% 0.77/0.96      (![X10 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 0.77/0.96      inference('simplify', [status(thm)], ['39'])).
% 0.77/0.96  thf(rc1_funct_2, axiom,
% 0.77/0.96    (![A:$i,B:$i]:
% 0.77/0.96     ( ?[C:$i]:
% 0.77/0.96       ( ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) & 
% 0.77/0.96         ( v5_relat_1 @ C @ B ) & ( v4_relat_1 @ C @ A ) & 
% 0.77/0.96         ( v1_relat_1 @ C ) & 
% 0.77/0.96         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.77/0.96  thf('41', plain,
% 0.77/0.96      (![X42 : $i, X43 : $i]:
% 0.77/0.96         (m1_subset_1 @ (sk_C_1 @ X42 @ X43) @ 
% 0.77/0.96          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42)))),
% 0.77/0.96      inference('cnf', [status(esa)], [rc1_funct_2])).
% 0.77/0.96  thf(cc1_subset_1, axiom,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( v1_xboole_0 @ A ) =>
% 0.77/0.96       ( ![B:$i]:
% 0.77/0.96         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.77/0.96  thf('42', plain,
% 0.77/0.96      (![X11 : $i, X12 : $i]:
% 0.77/0.96         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.77/0.96          | (v1_xboole_0 @ X11)
% 0.77/0.96          | ~ (v1_xboole_0 @ X12))),
% 0.77/0.96      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.77/0.96  thf('43', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.77/0.96          | (v1_xboole_0 @ (sk_C_1 @ X0 @ X1)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['41', '42'])).
% 0.77/0.96  thf('44', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.77/0.96          | (v1_xboole_0 @ (sk_C_1 @ X0 @ k1_xboole_0)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['40', '43'])).
% 0.77/0.96  thf('45', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.77/0.96      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.77/0.96  thf('46', plain, (![X0 : $i]: (v1_xboole_0 @ (sk_C_1 @ X0 @ k1_xboole_0))),
% 0.77/0.96      inference('demod', [status(thm)], ['44', '45'])).
% 0.77/0.96  thf('47', plain,
% 0.77/0.96      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.77/0.96      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.77/0.96  thf('48', plain, (![X0 : $i]: ((sk_C_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.77/0.96      inference('sup-', [status(thm)], ['46', '47'])).
% 0.77/0.96  thf('49', plain,
% 0.77/0.96      (![X42 : $i, X43 : $i]: (v1_funct_2 @ (sk_C_1 @ X42 @ X43) @ X43 @ X42)),
% 0.77/0.96      inference('cnf', [status(esa)], [rc1_funct_2])).
% 0.77/0.96  thf('50', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.77/0.96      inference('sup+', [status(thm)], ['48', '49'])).
% 0.77/0.96  thf('51', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         ((v1_funct_2 @ X0 @ k1_xboole_0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.77/0.96      inference('sup+', [status(thm)], ['38', '50'])).
% 0.77/0.96  thf('52', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.96         ((v1_funct_2 @ X2 @ X0 @ X1)
% 0.77/0.96          | ~ (v1_xboole_0 @ X0)
% 0.77/0.96          | ~ (v1_xboole_0 @ X2))),
% 0.77/0.96      inference('sup+', [status(thm)], ['37', '51'])).
% 0.77/0.96  thf('53', plain,
% 0.77/0.96      ((~ (v1_funct_2 @ (k4_relat_1 @ sk_C_2) @ sk_B_1 @ sk_A))
% 0.77/0.96         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_2) @ sk_B_1 @ sk_A)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['19', '20'])).
% 0.77/0.96  thf('54', plain,
% 0.77/0.96      (((~ (v1_xboole_0 @ (k4_relat_1 @ sk_C_2)) | ~ (v1_xboole_0 @ sk_B_1)))
% 0.77/0.96         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_2) @ sk_B_1 @ sk_A)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['52', '53'])).
% 0.77/0.96  thf('55', plain, (((k2_funct_1 @ sk_C_2) = (k4_relat_1 @ sk_C_2))),
% 0.77/0.96      inference('demod', [status(thm)], ['6', '9'])).
% 0.77/0.96  thf(t55_funct_1, axiom,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.77/0.96       ( ( v2_funct_1 @ A ) =>
% 0.77/0.96         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.77/0.96           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.77/0.96  thf('56', plain,
% 0.77/0.96      (![X21 : $i]:
% 0.77/0.96         (~ (v2_funct_1 @ X21)
% 0.77/0.96          | ((k2_relat_1 @ X21) = (k1_relat_1 @ (k2_funct_1 @ X21)))
% 0.77/0.96          | ~ (v1_funct_1 @ X21)
% 0.77/0.96          | ~ (v1_relat_1 @ X21))),
% 0.77/0.96      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.77/0.96  thf('57', plain,
% 0.77/0.96      ((((k2_relat_1 @ sk_C_2) = (k1_relat_1 @ (k4_relat_1 @ sk_C_2)))
% 0.77/0.96        | ~ (v1_relat_1 @ sk_C_2)
% 0.77/0.96        | ~ (v1_funct_1 @ sk_C_2)
% 0.77/0.96        | ~ (v2_funct_1 @ sk_C_2))),
% 0.77/0.96      inference('sup+', [status(thm)], ['55', '56'])).
% 0.77/0.96  thf('58', plain, ((v1_relat_1 @ sk_C_2)),
% 0.77/0.96      inference('sup-', [status(thm)], ['7', '8'])).
% 0.77/0.96  thf('59', plain, ((v1_funct_1 @ sk_C_2)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('60', plain, ((v2_funct_1 @ sk_C_2)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('61', plain,
% 0.77/0.96      (((k2_relat_1 @ sk_C_2) = (k1_relat_1 @ (k4_relat_1 @ sk_C_2)))),
% 0.77/0.96      inference('demod', [status(thm)], ['57', '58', '59', '60'])).
% 0.77/0.96  thf('62', plain,
% 0.77/0.96      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf(redefinition_k2_relset_1, axiom,
% 0.77/0.96    (![A:$i,B:$i,C:$i]:
% 0.77/0.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.77/0.96       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.77/0.96  thf('63', plain,
% 0.77/0.96      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.77/0.96         (((k2_relset_1 @ X32 @ X33 @ X31) = (k2_relat_1 @ X31))
% 0.77/0.96          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.77/0.96      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.77/0.96  thf('64', plain,
% 0.77/0.96      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 0.77/0.96      inference('sup-', [status(thm)], ['62', '63'])).
% 0.77/0.96  thf('65', plain, (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) = (sk_B_1))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('66', plain, (((k2_relat_1 @ sk_C_2) = (sk_B_1))),
% 0.77/0.96      inference('sup+', [status(thm)], ['64', '65'])).
% 0.77/0.96  thf('67', plain, (((sk_B_1) = (k1_relat_1 @ (k4_relat_1 @ sk_C_2)))),
% 0.77/0.96      inference('demod', [status(thm)], ['61', '66'])).
% 0.77/0.96  thf(t3_funct_2, axiom,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.77/0.96       ( ( v1_funct_1 @ A ) & 
% 0.77/0.96         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.77/0.96         ( m1_subset_1 @
% 0.77/0.96           A @ 
% 0.77/0.96           ( k1_zfmisc_1 @
% 0.77/0.96             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.77/0.96  thf('68', plain,
% 0.77/0.96      (![X44 : $i]:
% 0.77/0.96         ((m1_subset_1 @ X44 @ 
% 0.77/0.96           (k1_zfmisc_1 @ 
% 0.77/0.96            (k2_zfmisc_1 @ (k1_relat_1 @ X44) @ (k2_relat_1 @ X44))))
% 0.77/0.96          | ~ (v1_funct_1 @ X44)
% 0.77/0.96          | ~ (v1_relat_1 @ X44))),
% 0.77/0.96      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.77/0.96  thf(cc3_relset_1, axiom,
% 0.77/0.96    (![A:$i,B:$i]:
% 0.77/0.96     ( ( v1_xboole_0 @ A ) =>
% 0.77/0.96       ( ![C:$i]:
% 0.77/0.96         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.77/0.96           ( v1_xboole_0 @ C ) ) ) ))).
% 0.77/0.96  thf('69', plain,
% 0.77/0.96      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.77/0.96         (~ (v1_xboole_0 @ X25)
% 0.77/0.96          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X27)))
% 0.77/0.96          | (v1_xboole_0 @ X26))),
% 0.77/0.96      inference('cnf', [status(esa)], [cc3_relset_1])).
% 0.77/0.96  thf('70', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (~ (v1_relat_1 @ X0)
% 0.77/0.96          | ~ (v1_funct_1 @ X0)
% 0.77/0.96          | (v1_xboole_0 @ X0)
% 0.77/0.96          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['68', '69'])).
% 0.77/0.96  thf('71', plain,
% 0.77/0.96      ((~ (v1_xboole_0 @ sk_B_1)
% 0.77/0.96        | (v1_xboole_0 @ (k4_relat_1 @ sk_C_2))
% 0.77/0.96        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C_2))
% 0.77/0.96        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C_2)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['67', '70'])).
% 0.77/0.96  thf('72', plain, (((k2_funct_1 @ sk_C_2) = (k4_relat_1 @ sk_C_2))),
% 0.77/0.96      inference('demod', [status(thm)], ['6', '9'])).
% 0.77/0.96  thf('73', plain,
% 0.77/0.96      (![X20 : $i]:
% 0.77/0.96         ((v1_funct_1 @ (k2_funct_1 @ X20))
% 0.77/0.96          | ~ (v1_funct_1 @ X20)
% 0.77/0.96          | ~ (v1_relat_1 @ X20))),
% 0.77/0.96      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.77/0.96  thf('74', plain,
% 0.77/0.96      (((v1_funct_1 @ (k4_relat_1 @ sk_C_2))
% 0.77/0.96        | ~ (v1_relat_1 @ sk_C_2)
% 0.77/0.96        | ~ (v1_funct_1 @ sk_C_2))),
% 0.77/0.96      inference('sup+', [status(thm)], ['72', '73'])).
% 0.77/0.96  thf('75', plain, ((v1_relat_1 @ sk_C_2)),
% 0.77/0.96      inference('sup-', [status(thm)], ['7', '8'])).
% 0.77/0.96  thf('76', plain, ((v1_funct_1 @ sk_C_2)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('77', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C_2))),
% 0.77/0.96      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.77/0.96  thf('78', plain, (((k2_funct_1 @ sk_C_2) = (k4_relat_1 @ sk_C_2))),
% 0.77/0.96      inference('demod', [status(thm)], ['6', '9'])).
% 0.77/0.96  thf('79', plain,
% 0.77/0.96      (![X20 : $i]:
% 0.77/0.96         ((v1_relat_1 @ (k2_funct_1 @ X20))
% 0.77/0.96          | ~ (v1_funct_1 @ X20)
% 0.77/0.96          | ~ (v1_relat_1 @ X20))),
% 0.77/0.96      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.77/0.96  thf('80', plain,
% 0.77/0.96      (((v1_relat_1 @ (k4_relat_1 @ sk_C_2))
% 0.77/0.96        | ~ (v1_relat_1 @ sk_C_2)
% 0.77/0.96        | ~ (v1_funct_1 @ sk_C_2))),
% 0.77/0.96      inference('sup+', [status(thm)], ['78', '79'])).
% 0.77/0.96  thf('81', plain, ((v1_relat_1 @ sk_C_2)),
% 0.77/0.96      inference('sup-', [status(thm)], ['7', '8'])).
% 0.77/0.96  thf('82', plain, ((v1_funct_1 @ sk_C_2)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('83', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C_2))),
% 0.77/0.96      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.77/0.96  thf('84', plain,
% 0.77/0.96      ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ (k4_relat_1 @ sk_C_2)))),
% 0.77/0.96      inference('demod', [status(thm)], ['71', '77', '83'])).
% 0.77/0.96  thf('85', plain,
% 0.77/0.96      ((~ (v1_xboole_0 @ sk_B_1))
% 0.77/0.96         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_2) @ sk_B_1 @ sk_A)))),
% 0.77/0.96      inference('clc', [status(thm)], ['54', '84'])).
% 0.77/0.96  thf('86', plain,
% 0.77/0.96      ((((sk_A) = (k1_relat_1 @ sk_C_2)))
% 0.77/0.96         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_2) @ sk_B_1 @ sk_A)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['36', '85'])).
% 0.77/0.96  thf('87', plain, (((sk_B_1) = (k1_relat_1 @ (k4_relat_1 @ sk_C_2)))),
% 0.77/0.96      inference('demod', [status(thm)], ['61', '66'])).
% 0.77/0.96  thf('88', plain,
% 0.77/0.96      (![X44 : $i]:
% 0.77/0.96         ((v1_funct_2 @ X44 @ (k1_relat_1 @ X44) @ (k2_relat_1 @ X44))
% 0.77/0.96          | ~ (v1_funct_1 @ X44)
% 0.77/0.96          | ~ (v1_relat_1 @ X44))),
% 0.77/0.96      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.77/0.96  thf('89', plain,
% 0.77/0.96      (((v1_funct_2 @ (k4_relat_1 @ sk_C_2) @ sk_B_1 @ 
% 0.77/0.96         (k2_relat_1 @ (k4_relat_1 @ sk_C_2)))
% 0.77/0.96        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C_2))
% 0.77/0.96        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C_2)))),
% 0.77/0.96      inference('sup+', [status(thm)], ['87', '88'])).
% 0.77/0.96  thf('90', plain, (((k2_funct_1 @ sk_C_2) = (k4_relat_1 @ sk_C_2))),
% 0.77/0.96      inference('demod', [status(thm)], ['6', '9'])).
% 0.77/0.96  thf('91', plain,
% 0.77/0.96      (![X21 : $i]:
% 0.77/0.96         (~ (v2_funct_1 @ X21)
% 0.77/0.96          | ((k1_relat_1 @ X21) = (k2_relat_1 @ (k2_funct_1 @ X21)))
% 0.77/0.96          | ~ (v1_funct_1 @ X21)
% 0.77/0.96          | ~ (v1_relat_1 @ X21))),
% 0.77/0.96      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.77/0.96  thf('92', plain,
% 0.77/0.96      ((((k1_relat_1 @ sk_C_2) = (k2_relat_1 @ (k4_relat_1 @ sk_C_2)))
% 0.77/0.96        | ~ (v1_relat_1 @ sk_C_2)
% 0.77/0.96        | ~ (v1_funct_1 @ sk_C_2)
% 0.77/0.96        | ~ (v2_funct_1 @ sk_C_2))),
% 0.77/0.96      inference('sup+', [status(thm)], ['90', '91'])).
% 0.77/0.96  thf('93', plain, ((v1_relat_1 @ sk_C_2)),
% 0.77/0.96      inference('sup-', [status(thm)], ['7', '8'])).
% 0.77/0.96  thf('94', plain, ((v1_funct_1 @ sk_C_2)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('95', plain, ((v2_funct_1 @ sk_C_2)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('96', plain,
% 0.77/0.96      (((k1_relat_1 @ sk_C_2) = (k2_relat_1 @ (k4_relat_1 @ sk_C_2)))),
% 0.77/0.96      inference('demod', [status(thm)], ['92', '93', '94', '95'])).
% 0.77/0.96  thf('97', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C_2))),
% 0.77/0.96      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.77/0.96  thf('98', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C_2))),
% 0.77/0.96      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.77/0.96  thf('99', plain,
% 0.77/0.96      ((v1_funct_2 @ (k4_relat_1 @ sk_C_2) @ sk_B_1 @ (k1_relat_1 @ sk_C_2))),
% 0.77/0.96      inference('demod', [status(thm)], ['89', '96', '97', '98'])).
% 0.77/0.96  thf('100', plain,
% 0.77/0.96      (((v1_funct_2 @ (k4_relat_1 @ sk_C_2) @ sk_B_1 @ sk_A))
% 0.77/0.96         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_2) @ sk_B_1 @ sk_A)))),
% 0.77/0.96      inference('sup+', [status(thm)], ['86', '99'])).
% 0.77/0.96  thf('101', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C_2) @ sk_B_1 @ sk_A))),
% 0.77/0.96      inference('demod', [status(thm)], ['21', '100'])).
% 0.77/0.96  thf('102', plain,
% 0.77/0.96      (~
% 0.77/0.96       ((m1_subset_1 @ (k2_funct_1 @ sk_C_2) @ 
% 0.77/0.96         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))) | 
% 0.77/0.96       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_2) @ sk_B_1 @ sk_A)) | 
% 0.77/0.96       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_2)))),
% 0.77/0.96      inference('split', [status(esa)], ['0'])).
% 0.77/0.96  thf('103', plain,
% 0.77/0.96      (~
% 0.77/0.96       ((m1_subset_1 @ (k2_funct_1 @ sk_C_2) @ 
% 0.77/0.96         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))),
% 0.77/0.96      inference('sat_resolution*', [status(thm)], ['18', '101', '102'])).
% 0.77/0.96  thf('104', plain,
% 0.77/0.96      (~ (m1_subset_1 @ (k4_relat_1 @ sk_C_2) @ 
% 0.77/0.96          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.77/0.96      inference('simpl_trail', [status(thm)], ['11', '103'])).
% 0.77/0.96  thf('105', plain,
% 0.77/0.96      (((k1_relat_1 @ sk_C_2) = (k2_relat_1 @ (k4_relat_1 @ sk_C_2)))),
% 0.77/0.96      inference('demod', [status(thm)], ['92', '93', '94', '95'])).
% 0.77/0.96  thf('106', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.77/0.96      inference('sup+', [status(thm)], ['22', '23'])).
% 0.77/0.96  thf('107', plain,
% 0.77/0.96      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.77/0.96      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.77/0.96  thf('108', plain,
% 0.77/0.96      (![X9 : $i, X10 : $i]:
% 0.77/0.96         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X10) != (k1_xboole_0)))),
% 0.77/0.96      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.77/0.96  thf('109', plain,
% 0.77/0.96      (![X9 : $i]: ((k2_zfmisc_1 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 0.77/0.96      inference('simplify', [status(thm)], ['108'])).
% 0.77/0.96  thf('110', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.77/0.96      inference('sup+', [status(thm)], ['107', '109'])).
% 0.77/0.96  thf('111', plain,
% 0.77/0.96      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('112', plain,
% 0.77/0.96      (![X11 : $i, X12 : $i]:
% 0.77/0.96         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.77/0.96          | (v1_xboole_0 @ X11)
% 0.77/0.96          | ~ (v1_xboole_0 @ X12))),
% 0.77/0.96      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.77/0.96  thf('113', plain,
% 0.77/0.96      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.77/0.96        | (v1_xboole_0 @ sk_C_2))),
% 0.77/0.96      inference('sup-', [status(thm)], ['111', '112'])).
% 0.77/0.96  thf('114', plain,
% 0.77/0.96      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.77/0.96        | ~ (v1_xboole_0 @ sk_B_1)
% 0.77/0.96        | (v1_xboole_0 @ sk_C_2))),
% 0.77/0.96      inference('sup-', [status(thm)], ['110', '113'])).
% 0.77/0.96  thf('115', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.77/0.96      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.77/0.96  thf('116', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_C_2))),
% 0.77/0.96      inference('demod', [status(thm)], ['114', '115'])).
% 0.77/0.96  thf('117', plain,
% 0.77/0.96      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_C_2))),
% 0.77/0.96      inference('sup-', [status(thm)], ['106', '116'])).
% 0.77/0.96  thf(fc14_relat_1, axiom,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( v1_xboole_0 @ A ) =>
% 0.77/0.96       ( ( v1_xboole_0 @ ( k4_relat_1 @ A ) ) & 
% 0.77/0.96         ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) ))).
% 0.77/0.96  thf('118', plain,
% 0.77/0.96      (![X17 : $i]:
% 0.77/0.96         ((v1_xboole_0 @ (k4_relat_1 @ X17)) | ~ (v1_xboole_0 @ X17))),
% 0.77/0.96      inference('cnf', [status(esa)], [fc14_relat_1])).
% 0.77/0.96  thf('119', plain, (((k2_funct_1 @ sk_C_2) = (k4_relat_1 @ sk_C_2))),
% 0.77/0.96      inference('demod', [status(thm)], ['6', '9'])).
% 0.77/0.96  thf(d3_tarski, axiom,
% 0.77/0.96    (![A:$i,B:$i]:
% 0.77/0.96     ( ( r1_tarski @ A @ B ) <=>
% 0.77/0.96       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.77/0.96  thf('120', plain,
% 0.77/0.96      (![X4 : $i, X6 : $i]:
% 0.77/0.96         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.77/0.96      inference('cnf', [status(esa)], [d3_tarski])).
% 0.77/0.96  thf(d1_xboole_0, axiom,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.77/0.96  thf('121', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.77/0.96      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.77/0.96  thf('122', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.77/0.96      inference('sup-', [status(thm)], ['120', '121'])).
% 0.77/0.96  thf(t3_subset, axiom,
% 0.77/0.96    (![A:$i,B:$i]:
% 0.77/0.96     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.77/0.96  thf('123', plain,
% 0.77/0.96      (![X13 : $i, X15 : $i]:
% 0.77/0.96         ((m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X13 @ X15))),
% 0.77/0.96      inference('cnf', [status(esa)], [t3_subset])).
% 0.77/0.96  thf('124', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['122', '123'])).
% 0.77/0.96  thf('125', plain,
% 0.77/0.96      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C_2) @ 
% 0.77/0.96           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))
% 0.77/0.96         <= (~
% 0.77/0.96             ((m1_subset_1 @ (k2_funct_1 @ sk_C_2) @ 
% 0.77/0.96               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 0.77/0.96      inference('split', [status(esa)], ['0'])).
% 0.77/0.96  thf('126', plain,
% 0.77/0.96      ((~ (v1_xboole_0 @ (k2_funct_1 @ sk_C_2)))
% 0.77/0.96         <= (~
% 0.77/0.96             ((m1_subset_1 @ (k2_funct_1 @ sk_C_2) @ 
% 0.77/0.96               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 0.77/0.96      inference('sup-', [status(thm)], ['124', '125'])).
% 0.77/0.96  thf('127', plain,
% 0.77/0.96      ((~ (v1_xboole_0 @ (k4_relat_1 @ sk_C_2)))
% 0.77/0.96         <= (~
% 0.77/0.96             ((m1_subset_1 @ (k2_funct_1 @ sk_C_2) @ 
% 0.77/0.96               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 0.77/0.96      inference('sup-', [status(thm)], ['119', '126'])).
% 0.77/0.96  thf('128', plain,
% 0.77/0.96      ((~ (v1_xboole_0 @ sk_C_2))
% 0.77/0.96         <= (~
% 0.77/0.96             ((m1_subset_1 @ (k2_funct_1 @ sk_C_2) @ 
% 0.77/0.96               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 0.77/0.96      inference('sup-', [status(thm)], ['118', '127'])).
% 0.77/0.96  thf('129', plain,
% 0.77/0.96      ((![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0))
% 0.77/0.96         <= (~
% 0.77/0.96             ((m1_subset_1 @ (k2_funct_1 @ sk_C_2) @ 
% 0.77/0.96               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 0.77/0.96      inference('sup-', [status(thm)], ['117', '128'])).
% 0.77/0.96  thf('130', plain,
% 0.77/0.96      (((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 0.77/0.96        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.77/0.96      inference('sup-', [status(thm)], ['25', '26'])).
% 0.77/0.96  thf('131', plain,
% 0.77/0.96      (((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A))
% 0.77/0.96         <= (~
% 0.77/0.96             ((m1_subset_1 @ (k2_funct_1 @ sk_C_2) @ 
% 0.77/0.96               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 0.77/0.96      inference('sup-', [status(thm)], ['129', '130'])).
% 0.77/0.96  thf('132', plain,
% 0.77/0.96      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 0.77/0.96        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 0.77/0.96      inference('demod', [status(thm)], ['31', '34'])).
% 0.77/0.96  thf('133', plain,
% 0.77/0.96      ((((sk_A) = (k1_relat_1 @ sk_C_2)))
% 0.77/0.96         <= (~
% 0.77/0.96             ((m1_subset_1 @ (k2_funct_1 @ sk_C_2) @ 
% 0.77/0.96               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 0.77/0.96      inference('sup-', [status(thm)], ['131', '132'])).
% 0.77/0.96  thf('134', plain,
% 0.77/0.96      (~
% 0.77/0.96       ((m1_subset_1 @ (k2_funct_1 @ sk_C_2) @ 
% 0.77/0.96         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))),
% 0.77/0.96      inference('sat_resolution*', [status(thm)], ['18', '101', '102'])).
% 0.77/0.96  thf('135', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 0.77/0.96      inference('simpl_trail', [status(thm)], ['133', '134'])).
% 0.77/0.96  thf('136', plain, (((sk_A) = (k2_relat_1 @ (k4_relat_1 @ sk_C_2)))),
% 0.77/0.96      inference('demod', [status(thm)], ['105', '135'])).
% 0.77/0.96  thf('137', plain,
% 0.77/0.96      (![X44 : $i]:
% 0.77/0.96         ((m1_subset_1 @ X44 @ 
% 0.77/0.96           (k1_zfmisc_1 @ 
% 0.77/0.96            (k2_zfmisc_1 @ (k1_relat_1 @ X44) @ (k2_relat_1 @ X44))))
% 0.77/0.96          | ~ (v1_funct_1 @ X44)
% 0.77/0.96          | ~ (v1_relat_1 @ X44))),
% 0.77/0.96      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.77/0.96  thf('138', plain,
% 0.77/0.96      (((m1_subset_1 @ (k4_relat_1 @ sk_C_2) @ 
% 0.77/0.96         (k1_zfmisc_1 @ 
% 0.77/0.96          (k2_zfmisc_1 @ (k1_relat_1 @ (k4_relat_1 @ sk_C_2)) @ sk_A)))
% 0.77/0.96        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C_2))
% 0.77/0.96        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C_2)))),
% 0.77/0.96      inference('sup+', [status(thm)], ['136', '137'])).
% 0.77/0.96  thf('139', plain, (((sk_B_1) = (k1_relat_1 @ (k4_relat_1 @ sk_C_2)))),
% 0.77/0.96      inference('demod', [status(thm)], ['61', '66'])).
% 0.77/0.96  thf('140', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C_2))),
% 0.77/0.96      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.77/0.96  thf('141', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C_2))),
% 0.77/0.96      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.77/0.96  thf('142', plain,
% 0.77/0.96      ((m1_subset_1 @ (k4_relat_1 @ sk_C_2) @ 
% 0.77/0.96        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.77/0.96      inference('demod', [status(thm)], ['138', '139', '140', '141'])).
% 0.77/0.96  thf('143', plain, ($false), inference('demod', [status(thm)], ['104', '142'])).
% 0.77/0.96  
% 0.77/0.96  % SZS output end Refutation
% 0.77/0.96  
% 0.77/0.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
