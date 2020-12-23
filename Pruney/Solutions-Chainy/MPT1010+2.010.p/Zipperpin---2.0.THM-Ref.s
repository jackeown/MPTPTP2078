%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RahCgrLP1Z

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:14 EST 2020

% Result     : Theorem 0.57s
% Output     : Refutation 0.57s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 240 expanded)
%              Number of leaves         :   42 (  90 expanded)
%              Depth                    :   19
%              Number of atoms          :  768 (2329 expanded)
%              Number of equality atoms :   57 ( 141 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(t65_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( k1_funct_1 @ D @ C )
          = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
       => ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ D @ C )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
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

thf('2',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_2 @ X44 @ X42 @ X43 )
      | ( X42
        = ( k1_relset_1 @ X42 @ X43 @ X44 ) )
      | ~ ( zip_tseitin_1 @ X44 @ X43 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X40: $i,X41: $i] :
      ( ( zip_tseitin_0 @ X40 @ X41 )
      | ( X40 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('5',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
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

thf('8',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( zip_tseitin_0 @ X45 @ X46 )
      | ( zip_tseitin_1 @ X47 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('9',plain,
    ( ( zip_tseitin_1 @ sk_D_2 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ~ ( zip_tseitin_0 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( zip_tseitin_1 @ sk_D_2 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('11',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( X4 != X3 )
      | ( r2_hidden @ X4 @ X5 )
      | ( X5
       != ( k1_tarski @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('12',plain,(
    ! [X3: $i] :
      ( r2_hidden @ X3 @ ( k1_tarski @ X3 ) ) ),
    inference(simplify,[status(thm)],['11'])).

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
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    zip_tseitin_1 @ sk_D_2 @ ( k1_tarski @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['10','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('17',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k1_relset_1 @ X38 @ X39 @ X37 )
        = ( k1_relat_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('18',plain,
    ( ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_D_2 )
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['3','15','18'])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('20',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X29 @ ( k1_relat_1 @ X30 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X30 @ X29 ) @ ( k2_relat_1 @ X30 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D_2 )
      | ~ ( v1_funct_1 @ sk_D_2 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ X0 ) @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('23',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v1_relat_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('24',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ X0 ) @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference(demod,[status(thm)],['21','24','25'])).

thf('27',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_C_2 ) @ ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['0','26'])).

thf('28',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('29',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('30',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v5_relat_1 @ X34 @ X36 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('31',plain,(
    v5_relat_1 @ sk_D_2 @ ( k1_tarski @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('32',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v5_relat_1 @ X20 @ X21 )
      | ( r1_tarski @ ( k2_relat_1 @ X20 ) @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['22','23'])).

thf('35',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_tarski @ sk_B_1 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('36',plain,(
    ! [X17: $i,X19: $i] :
      ( ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('37',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('38',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ( r2_hidden @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_D_2 ) )
    | ( r2_hidden @ ( sk_B @ ( k2_relat_1 @ sk_D_2 ) ) @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['28','39'])).

thf('41',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( X6 = X3 )
      | ( X5
       != ( k1_tarski @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('42',plain,(
    ! [X3: $i,X6: $i] :
      ( ( X6 = X3 )
      | ~ ( r2_hidden @ X6 @ ( k1_tarski @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_D_2 ) )
    | ( ( sk_B @ ( k2_relat_1 @ sk_D_2 ) )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('45',plain,
    ( ( r2_hidden @ sk_B_1 @ ( k2_relat_1 @ sk_D_2 ) )
    | ( v1_xboole_0 @ ( k2_relat_1 @ sk_D_2 ) )
    | ( v1_xboole_0 @ ( k2_relat_1 @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_D_2 ) )
    | ( r2_hidden @ sk_B_1 @ ( k2_relat_1 @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X3: $i,X7: $i] :
      ( ( X7
        = ( k1_tarski @ X3 ) )
      | ( ( sk_C @ X7 @ X3 )
        = X3 )
      | ( r2_hidden @ ( sk_C @ X7 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ ( k2_relat_1 @ sk_D_2 ) @ X0 )
        = X0 )
      | ( ( k2_relat_1 @ sk_D_2 )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ sk_D_2 ) @ X0 ) @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X3: $i,X6: $i] :
      ( ( X6 = X3 )
      | ~ ( r2_hidden @ X6 @ ( k1_tarski @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_D_2 )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k2_relat_1 @ sk_D_2 ) @ X0 )
        = X0 )
      | ( ( sk_C @ ( k2_relat_1 @ sk_D_2 ) @ X0 )
        = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_B_1 )
      | ( ( sk_C @ ( k2_relat_1 @ sk_D_2 ) @ X0 )
        = sk_B_1 )
      | ( ( k2_relat_1 @ sk_D_2 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['51'])).

thf('53',plain,
    ( ( ( k2_relat_1 @ sk_D_2 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( ( sk_C @ ( k2_relat_1 @ sk_D_2 ) @ sk_B_1 )
      = sk_B_1 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X3: $i,X7: $i] :
      ( ( X7
        = ( k1_tarski @ X3 ) )
      | ( ( sk_C @ X7 @ X3 )
       != X3 )
      | ~ ( r2_hidden @ ( sk_C @ X7 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('55',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ ( k2_relat_1 @ sk_D_2 ) )
    | ( ( k2_relat_1 @ sk_D_2 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( ( sk_C @ ( k2_relat_1 @ sk_D_2 ) @ sk_B_1 )
     != sk_B_1 )
    | ( ( k2_relat_1 @ sk_D_2 )
      = ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( sk_C @ ( k2_relat_1 @ sk_D_2 ) @ sk_B_1 )
     != sk_B_1 )
    | ( ( k2_relat_1 @ sk_D_2 )
      = ( k1_tarski @ sk_B_1 ) )
    | ~ ( r2_hidden @ sk_B_1 @ ( k2_relat_1 @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ( ( k2_relat_1 @ sk_D_2 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( ( sk_C @ ( k2_relat_1 @ sk_D_2 ) @ sk_B_1 )
      = sk_B_1 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('58',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ ( k2_relat_1 @ sk_D_2 ) )
    | ( ( k2_relat_1 @ sk_D_2 )
      = ( k1_tarski @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_D_2 ) )
    | ( ( k2_relat_1 @ sk_D_2 )
      = ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['46','58'])).

thf('60',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_C_2 ) @ ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['0','26'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('62',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k2_relat_1 @ sk_D_2 )
    = ( k1_tarski @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_C_2 ) @ ( k1_tarski @ sk_B_1 ) ),
    inference(demod,[status(thm)],['27','63'])).

thf('65',plain,(
    ! [X3: $i,X6: $i] :
      ( ( X6 = X3 )
      | ~ ( r2_hidden @ X6 @ ( k1_tarski @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('66',plain,
    ( ( k1_funct_1 @ sk_D_2 @ sk_C_2 )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ( k1_funct_1 @ sk_D_2 @ sk_C_2 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['66','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RahCgrLP1Z
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:06:46 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.57/0.79  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.57/0.79  % Solved by: fo/fo7.sh
% 0.57/0.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.57/0.79  % done 210 iterations in 0.342s
% 0.57/0.79  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.57/0.79  % SZS output start Refutation
% 0.57/0.79  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.57/0.79  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.57/0.79  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.57/0.79  thf(sk_B_type, type, sk_B: $i > $i).
% 0.57/0.79  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.57/0.79  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.57/0.79  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.57/0.79  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.57/0.79  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.57/0.79  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.57/0.79  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.57/0.79  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.57/0.79  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.57/0.79  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.57/0.79  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.57/0.79  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.57/0.79  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.57/0.79  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.57/0.79  thf(sk_A_type, type, sk_A: $i).
% 0.57/0.79  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.57/0.79  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.57/0.79  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.57/0.79  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.57/0.79  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.57/0.79  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.57/0.79  thf(t65_funct_2, conjecture,
% 0.57/0.79    (![A:$i,B:$i,C:$i,D:$i]:
% 0.57/0.79     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.57/0.79         ( m1_subset_1 @
% 0.57/0.79           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.57/0.79       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.57/0.79  thf(zf_stmt_0, negated_conjecture,
% 0.57/0.79    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.57/0.79        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.57/0.79            ( m1_subset_1 @
% 0.57/0.79              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.57/0.79          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.57/0.79    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.57/0.79  thf('0', plain, ((r2_hidden @ sk_C_2 @ sk_A)),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('1', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ (k1_tarski @ sk_B_1))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf(d1_funct_2, axiom,
% 0.57/0.79    (![A:$i,B:$i,C:$i]:
% 0.57/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.57/0.79       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.57/0.79           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.57/0.79             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.57/0.79         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.57/0.79           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.57/0.79             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.57/0.79  thf(zf_stmt_1, axiom,
% 0.57/0.79    (![C:$i,B:$i,A:$i]:
% 0.57/0.79     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.57/0.79       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.57/0.79  thf('2', plain,
% 0.57/0.79      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.57/0.79         (~ (v1_funct_2 @ X44 @ X42 @ X43)
% 0.57/0.79          | ((X42) = (k1_relset_1 @ X42 @ X43 @ X44))
% 0.57/0.79          | ~ (zip_tseitin_1 @ X44 @ X43 @ X42))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.57/0.79  thf('3', plain,
% 0.57/0.79      ((~ (zip_tseitin_1 @ sk_D_2 @ (k1_tarski @ sk_B_1) @ sk_A)
% 0.57/0.79        | ((sk_A) = (k1_relset_1 @ sk_A @ (k1_tarski @ sk_B_1) @ sk_D_2)))),
% 0.57/0.79      inference('sup-', [status(thm)], ['1', '2'])).
% 0.57/0.79  thf(zf_stmt_2, axiom,
% 0.57/0.79    (![B:$i,A:$i]:
% 0.57/0.79     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.57/0.79       ( zip_tseitin_0 @ B @ A ) ))).
% 0.57/0.79  thf('4', plain,
% 0.57/0.79      (![X40 : $i, X41 : $i]:
% 0.57/0.79         ((zip_tseitin_0 @ X40 @ X41) | ((X40) = (k1_xboole_0)))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.57/0.79  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.57/0.79  thf('5', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.57/0.79      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.57/0.79  thf('6', plain,
% 0.57/0.79      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.57/0.79      inference('sup+', [status(thm)], ['4', '5'])).
% 0.57/0.79  thf('7', plain,
% 0.57/0.79      ((m1_subset_1 @ sk_D_2 @ 
% 0.57/0.79        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.57/0.79  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.57/0.79  thf(zf_stmt_5, axiom,
% 0.57/0.79    (![A:$i,B:$i,C:$i]:
% 0.57/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.57/0.79       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.57/0.79         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.57/0.79           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.57/0.79             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.57/0.79  thf('8', plain,
% 0.57/0.79      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.57/0.79         (~ (zip_tseitin_0 @ X45 @ X46)
% 0.57/0.79          | (zip_tseitin_1 @ X47 @ X45 @ X46)
% 0.57/0.79          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45))))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.57/0.79  thf('9', plain,
% 0.57/0.79      (((zip_tseitin_1 @ sk_D_2 @ (k1_tarski @ sk_B_1) @ sk_A)
% 0.57/0.79        | ~ (zip_tseitin_0 @ (k1_tarski @ sk_B_1) @ sk_A))),
% 0.57/0.79      inference('sup-', [status(thm)], ['7', '8'])).
% 0.57/0.79  thf('10', plain,
% 0.57/0.79      (((v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.57/0.79        | (zip_tseitin_1 @ sk_D_2 @ (k1_tarski @ sk_B_1) @ sk_A))),
% 0.57/0.79      inference('sup-', [status(thm)], ['6', '9'])).
% 0.57/0.79  thf(d1_tarski, axiom,
% 0.57/0.79    (![A:$i,B:$i]:
% 0.57/0.79     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.57/0.79       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.57/0.79  thf('11', plain,
% 0.57/0.79      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.57/0.79         (((X4) != (X3)) | (r2_hidden @ X4 @ X5) | ((X5) != (k1_tarski @ X3)))),
% 0.57/0.79      inference('cnf', [status(esa)], [d1_tarski])).
% 0.57/0.79  thf('12', plain, (![X3 : $i]: (r2_hidden @ X3 @ (k1_tarski @ X3))),
% 0.57/0.79      inference('simplify', [status(thm)], ['11'])).
% 0.57/0.79  thf(d1_xboole_0, axiom,
% 0.57/0.79    (![A:$i]:
% 0.57/0.79     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.57/0.79  thf('13', plain,
% 0.57/0.79      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.57/0.79      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.57/0.79  thf('14', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.57/0.79      inference('sup-', [status(thm)], ['12', '13'])).
% 0.57/0.79  thf('15', plain, ((zip_tseitin_1 @ sk_D_2 @ (k1_tarski @ sk_B_1) @ sk_A)),
% 0.57/0.79      inference('clc', [status(thm)], ['10', '14'])).
% 0.57/0.79  thf('16', plain,
% 0.57/0.79      ((m1_subset_1 @ sk_D_2 @ 
% 0.57/0.79        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf(redefinition_k1_relset_1, axiom,
% 0.57/0.79    (![A:$i,B:$i,C:$i]:
% 0.57/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.57/0.79       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.57/0.79  thf('17', plain,
% 0.57/0.79      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.57/0.79         (((k1_relset_1 @ X38 @ X39 @ X37) = (k1_relat_1 @ X37))
% 0.57/0.79          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 0.57/0.79      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.57/0.79  thf('18', plain,
% 0.57/0.79      (((k1_relset_1 @ sk_A @ (k1_tarski @ sk_B_1) @ sk_D_2)
% 0.57/0.79         = (k1_relat_1 @ sk_D_2))),
% 0.57/0.79      inference('sup-', [status(thm)], ['16', '17'])).
% 0.57/0.79  thf('19', plain, (((sk_A) = (k1_relat_1 @ sk_D_2))),
% 0.57/0.79      inference('demod', [status(thm)], ['3', '15', '18'])).
% 0.57/0.79  thf(t12_funct_1, axiom,
% 0.57/0.79    (![A:$i,B:$i]:
% 0.57/0.79     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.57/0.79       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.57/0.79         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 0.57/0.79  thf('20', plain,
% 0.57/0.79      (![X29 : $i, X30 : $i]:
% 0.57/0.79         (~ (r2_hidden @ X29 @ (k1_relat_1 @ X30))
% 0.57/0.79          | (r2_hidden @ (k1_funct_1 @ X30 @ X29) @ (k2_relat_1 @ X30))
% 0.57/0.79          | ~ (v1_funct_1 @ X30)
% 0.57/0.79          | ~ (v1_relat_1 @ X30))),
% 0.57/0.79      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.57/0.79  thf('21', plain,
% 0.57/0.79      (![X0 : $i]:
% 0.57/0.79         (~ (r2_hidden @ X0 @ sk_A)
% 0.57/0.79          | ~ (v1_relat_1 @ sk_D_2)
% 0.57/0.79          | ~ (v1_funct_1 @ sk_D_2)
% 0.57/0.79          | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k2_relat_1 @ sk_D_2)))),
% 0.57/0.79      inference('sup-', [status(thm)], ['19', '20'])).
% 0.57/0.79  thf('22', plain,
% 0.57/0.79      ((m1_subset_1 @ sk_D_2 @ 
% 0.57/0.79        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf(cc1_relset_1, axiom,
% 0.57/0.79    (![A:$i,B:$i,C:$i]:
% 0.57/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.57/0.79       ( v1_relat_1 @ C ) ))).
% 0.57/0.79  thf('23', plain,
% 0.57/0.79      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.57/0.79         ((v1_relat_1 @ X31)
% 0.57/0.79          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.57/0.79      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.57/0.79  thf('24', plain, ((v1_relat_1 @ sk_D_2)),
% 0.57/0.79      inference('sup-', [status(thm)], ['22', '23'])).
% 0.57/0.79  thf('25', plain, ((v1_funct_1 @ sk_D_2)),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('26', plain,
% 0.57/0.79      (![X0 : $i]:
% 0.57/0.79         (~ (r2_hidden @ X0 @ sk_A)
% 0.57/0.79          | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k2_relat_1 @ sk_D_2)))),
% 0.57/0.79      inference('demod', [status(thm)], ['21', '24', '25'])).
% 0.57/0.79  thf('27', plain,
% 0.57/0.79      ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_C_2) @ (k2_relat_1 @ sk_D_2))),
% 0.57/0.79      inference('sup-', [status(thm)], ['0', '26'])).
% 0.57/0.79  thf('28', plain,
% 0.57/0.79      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.57/0.79      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.57/0.79  thf('29', plain,
% 0.57/0.79      ((m1_subset_1 @ sk_D_2 @ 
% 0.57/0.79        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf(cc2_relset_1, axiom,
% 0.57/0.79    (![A:$i,B:$i,C:$i]:
% 0.57/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.57/0.79       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.57/0.79  thf('30', plain,
% 0.57/0.79      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.57/0.79         ((v5_relat_1 @ X34 @ X36)
% 0.57/0.79          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.57/0.79      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.57/0.79  thf('31', plain, ((v5_relat_1 @ sk_D_2 @ (k1_tarski @ sk_B_1))),
% 0.57/0.79      inference('sup-', [status(thm)], ['29', '30'])).
% 0.57/0.79  thf(d19_relat_1, axiom,
% 0.57/0.79    (![A:$i,B:$i]:
% 0.57/0.79     ( ( v1_relat_1 @ B ) =>
% 0.57/0.79       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.57/0.79  thf('32', plain,
% 0.57/0.79      (![X20 : $i, X21 : $i]:
% 0.57/0.79         (~ (v5_relat_1 @ X20 @ X21)
% 0.57/0.79          | (r1_tarski @ (k2_relat_1 @ X20) @ X21)
% 0.57/0.79          | ~ (v1_relat_1 @ X20))),
% 0.57/0.79      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.57/0.79  thf('33', plain,
% 0.57/0.79      ((~ (v1_relat_1 @ sk_D_2)
% 0.57/0.79        | (r1_tarski @ (k2_relat_1 @ sk_D_2) @ (k1_tarski @ sk_B_1)))),
% 0.57/0.79      inference('sup-', [status(thm)], ['31', '32'])).
% 0.57/0.79  thf('34', plain, ((v1_relat_1 @ sk_D_2)),
% 0.57/0.79      inference('sup-', [status(thm)], ['22', '23'])).
% 0.57/0.79  thf('35', plain,
% 0.57/0.79      ((r1_tarski @ (k2_relat_1 @ sk_D_2) @ (k1_tarski @ sk_B_1))),
% 0.57/0.79      inference('demod', [status(thm)], ['33', '34'])).
% 0.57/0.79  thf(t3_subset, axiom,
% 0.57/0.79    (![A:$i,B:$i]:
% 0.57/0.79     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.57/0.79  thf('36', plain,
% 0.57/0.79      (![X17 : $i, X19 : $i]:
% 0.57/0.79         ((m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X19)) | ~ (r1_tarski @ X17 @ X19))),
% 0.57/0.79      inference('cnf', [status(esa)], [t3_subset])).
% 0.57/0.79  thf('37', plain,
% 0.57/0.79      ((m1_subset_1 @ (k2_relat_1 @ sk_D_2) @ 
% 0.57/0.79        (k1_zfmisc_1 @ (k1_tarski @ sk_B_1)))),
% 0.57/0.79      inference('sup-', [status(thm)], ['35', '36'])).
% 0.57/0.79  thf(l3_subset_1, axiom,
% 0.57/0.79    (![A:$i,B:$i]:
% 0.57/0.79     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.57/0.79       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.57/0.79  thf('38', plain,
% 0.57/0.79      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.57/0.79         (~ (r2_hidden @ X14 @ X15)
% 0.57/0.79          | (r2_hidden @ X14 @ X16)
% 0.57/0.79          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.57/0.79      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.57/0.79  thf('39', plain,
% 0.57/0.79      (![X0 : $i]:
% 0.57/0.79         ((r2_hidden @ X0 @ (k1_tarski @ sk_B_1))
% 0.57/0.79          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_2)))),
% 0.57/0.79      inference('sup-', [status(thm)], ['37', '38'])).
% 0.57/0.79  thf('40', plain,
% 0.57/0.79      (((v1_xboole_0 @ (k2_relat_1 @ sk_D_2))
% 0.57/0.79        | (r2_hidden @ (sk_B @ (k2_relat_1 @ sk_D_2)) @ (k1_tarski @ sk_B_1)))),
% 0.57/0.79      inference('sup-', [status(thm)], ['28', '39'])).
% 0.57/0.79  thf('41', plain,
% 0.57/0.79      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.57/0.79         (~ (r2_hidden @ X6 @ X5) | ((X6) = (X3)) | ((X5) != (k1_tarski @ X3)))),
% 0.57/0.79      inference('cnf', [status(esa)], [d1_tarski])).
% 0.57/0.79  thf('42', plain,
% 0.57/0.79      (![X3 : $i, X6 : $i]:
% 0.57/0.79         (((X6) = (X3)) | ~ (r2_hidden @ X6 @ (k1_tarski @ X3)))),
% 0.57/0.79      inference('simplify', [status(thm)], ['41'])).
% 0.57/0.79  thf('43', plain,
% 0.57/0.79      (((v1_xboole_0 @ (k2_relat_1 @ sk_D_2))
% 0.57/0.79        | ((sk_B @ (k2_relat_1 @ sk_D_2)) = (sk_B_1)))),
% 0.57/0.79      inference('sup-', [status(thm)], ['40', '42'])).
% 0.57/0.79  thf('44', plain,
% 0.57/0.79      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.57/0.79      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.57/0.79  thf('45', plain,
% 0.57/0.79      (((r2_hidden @ sk_B_1 @ (k2_relat_1 @ sk_D_2))
% 0.57/0.79        | (v1_xboole_0 @ (k2_relat_1 @ sk_D_2))
% 0.57/0.79        | (v1_xboole_0 @ (k2_relat_1 @ sk_D_2)))),
% 0.57/0.79      inference('sup+', [status(thm)], ['43', '44'])).
% 0.57/0.79  thf('46', plain,
% 0.57/0.79      (((v1_xboole_0 @ (k2_relat_1 @ sk_D_2))
% 0.57/0.79        | (r2_hidden @ sk_B_1 @ (k2_relat_1 @ sk_D_2)))),
% 0.57/0.79      inference('simplify', [status(thm)], ['45'])).
% 0.57/0.79  thf('47', plain,
% 0.57/0.79      (![X3 : $i, X7 : $i]:
% 0.57/0.79         (((X7) = (k1_tarski @ X3))
% 0.57/0.79          | ((sk_C @ X7 @ X3) = (X3))
% 0.57/0.79          | (r2_hidden @ (sk_C @ X7 @ X3) @ X7))),
% 0.57/0.79      inference('cnf', [status(esa)], [d1_tarski])).
% 0.57/0.79  thf('48', plain,
% 0.57/0.79      (![X0 : $i]:
% 0.57/0.79         ((r2_hidden @ X0 @ (k1_tarski @ sk_B_1))
% 0.57/0.79          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_2)))),
% 0.57/0.79      inference('sup-', [status(thm)], ['37', '38'])).
% 0.57/0.79  thf('49', plain,
% 0.57/0.79      (![X0 : $i]:
% 0.57/0.79         (((sk_C @ (k2_relat_1 @ sk_D_2) @ X0) = (X0))
% 0.57/0.79          | ((k2_relat_1 @ sk_D_2) = (k1_tarski @ X0))
% 0.57/0.79          | (r2_hidden @ (sk_C @ (k2_relat_1 @ sk_D_2) @ X0) @ 
% 0.57/0.79             (k1_tarski @ sk_B_1)))),
% 0.57/0.79      inference('sup-', [status(thm)], ['47', '48'])).
% 0.57/0.79  thf('50', plain,
% 0.57/0.79      (![X3 : $i, X6 : $i]:
% 0.57/0.79         (((X6) = (X3)) | ~ (r2_hidden @ X6 @ (k1_tarski @ X3)))),
% 0.57/0.79      inference('simplify', [status(thm)], ['41'])).
% 0.57/0.79  thf('51', plain,
% 0.57/0.79      (![X0 : $i]:
% 0.57/0.79         (((k2_relat_1 @ sk_D_2) = (k1_tarski @ X0))
% 0.57/0.79          | ((sk_C @ (k2_relat_1 @ sk_D_2) @ X0) = (X0))
% 0.57/0.79          | ((sk_C @ (k2_relat_1 @ sk_D_2) @ X0) = (sk_B_1)))),
% 0.57/0.79      inference('sup-', [status(thm)], ['49', '50'])).
% 0.57/0.79  thf('52', plain,
% 0.57/0.79      (![X0 : $i]:
% 0.57/0.79         (((X0) != (sk_B_1))
% 0.57/0.79          | ((sk_C @ (k2_relat_1 @ sk_D_2) @ X0) = (sk_B_1))
% 0.57/0.79          | ((k2_relat_1 @ sk_D_2) = (k1_tarski @ X0)))),
% 0.57/0.79      inference('eq_fact', [status(thm)], ['51'])).
% 0.57/0.79  thf('53', plain,
% 0.57/0.79      ((((k2_relat_1 @ sk_D_2) = (k1_tarski @ sk_B_1))
% 0.57/0.79        | ((sk_C @ (k2_relat_1 @ sk_D_2) @ sk_B_1) = (sk_B_1)))),
% 0.57/0.79      inference('simplify', [status(thm)], ['52'])).
% 0.57/0.79  thf('54', plain,
% 0.57/0.79      (![X3 : $i, X7 : $i]:
% 0.57/0.79         (((X7) = (k1_tarski @ X3))
% 0.57/0.79          | ((sk_C @ X7 @ X3) != (X3))
% 0.57/0.79          | ~ (r2_hidden @ (sk_C @ X7 @ X3) @ X7))),
% 0.57/0.79      inference('cnf', [status(esa)], [d1_tarski])).
% 0.57/0.79  thf('55', plain,
% 0.57/0.79      ((~ (r2_hidden @ sk_B_1 @ (k2_relat_1 @ sk_D_2))
% 0.57/0.79        | ((k2_relat_1 @ sk_D_2) = (k1_tarski @ sk_B_1))
% 0.57/0.79        | ((sk_C @ (k2_relat_1 @ sk_D_2) @ sk_B_1) != (sk_B_1))
% 0.57/0.79        | ((k2_relat_1 @ sk_D_2) = (k1_tarski @ sk_B_1)))),
% 0.57/0.79      inference('sup-', [status(thm)], ['53', '54'])).
% 0.57/0.79  thf('56', plain,
% 0.57/0.79      ((((sk_C @ (k2_relat_1 @ sk_D_2) @ sk_B_1) != (sk_B_1))
% 0.57/0.79        | ((k2_relat_1 @ sk_D_2) = (k1_tarski @ sk_B_1))
% 0.57/0.79        | ~ (r2_hidden @ sk_B_1 @ (k2_relat_1 @ sk_D_2)))),
% 0.57/0.79      inference('simplify', [status(thm)], ['55'])).
% 0.57/0.79  thf('57', plain,
% 0.57/0.79      ((((k2_relat_1 @ sk_D_2) = (k1_tarski @ sk_B_1))
% 0.57/0.79        | ((sk_C @ (k2_relat_1 @ sk_D_2) @ sk_B_1) = (sk_B_1)))),
% 0.57/0.79      inference('simplify', [status(thm)], ['52'])).
% 0.57/0.79  thf('58', plain,
% 0.57/0.79      ((~ (r2_hidden @ sk_B_1 @ (k2_relat_1 @ sk_D_2))
% 0.57/0.79        | ((k2_relat_1 @ sk_D_2) = (k1_tarski @ sk_B_1)))),
% 0.57/0.79      inference('clc', [status(thm)], ['56', '57'])).
% 0.57/0.79  thf('59', plain,
% 0.57/0.79      (((v1_xboole_0 @ (k2_relat_1 @ sk_D_2))
% 0.57/0.79        | ((k2_relat_1 @ sk_D_2) = (k1_tarski @ sk_B_1)))),
% 0.57/0.79      inference('sup-', [status(thm)], ['46', '58'])).
% 0.57/0.79  thf('60', plain,
% 0.57/0.79      ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_C_2) @ (k2_relat_1 @ sk_D_2))),
% 0.57/0.79      inference('sup-', [status(thm)], ['0', '26'])).
% 0.57/0.79  thf('61', plain,
% 0.57/0.79      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.57/0.79      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.57/0.79  thf('62', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_D_2))),
% 0.57/0.79      inference('sup-', [status(thm)], ['60', '61'])).
% 0.57/0.79  thf('63', plain, (((k2_relat_1 @ sk_D_2) = (k1_tarski @ sk_B_1))),
% 0.57/0.79      inference('sup-', [status(thm)], ['59', '62'])).
% 0.57/0.79  thf('64', plain,
% 0.57/0.79      ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_C_2) @ (k1_tarski @ sk_B_1))),
% 0.57/0.79      inference('demod', [status(thm)], ['27', '63'])).
% 0.57/0.79  thf('65', plain,
% 0.57/0.79      (![X3 : $i, X6 : $i]:
% 0.57/0.79         (((X6) = (X3)) | ~ (r2_hidden @ X6 @ (k1_tarski @ X3)))),
% 0.57/0.79      inference('simplify', [status(thm)], ['41'])).
% 0.57/0.79  thf('66', plain, (((k1_funct_1 @ sk_D_2 @ sk_C_2) = (sk_B_1))),
% 0.57/0.79      inference('sup-', [status(thm)], ['64', '65'])).
% 0.57/0.79  thf('67', plain, (((k1_funct_1 @ sk_D_2 @ sk_C_2) != (sk_B_1))),
% 0.57/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.79  thf('68', plain, ($false),
% 0.57/0.79      inference('simplify_reflect-', [status(thm)], ['66', '67'])).
% 0.57/0.79  
% 0.57/0.79  % SZS output end Refutation
% 0.57/0.79  
% 0.57/0.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
