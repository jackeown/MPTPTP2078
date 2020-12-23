%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DrNmBY6XPg

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:21 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 120 expanded)
%              Number of leaves         :   40 (  53 expanded)
%              Depth                    :   15
%              Number of atoms          :  644 (1072 expanded)
%              Number of equality atoms :   46 (  73 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_funct_2 @ sk_D_3 @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
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
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_funct_2 @ X43 @ X41 @ X42 )
      | ( X41
        = ( k1_relset_1 @ X41 @ X42 @ X43 ) )
      | ~ ( zip_tseitin_1 @ X43 @ X42 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_3 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
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

thf('5',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( zip_tseitin_0 @ X44 @ X45 )
      | ( zip_tseitin_1 @ X46 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_1 @ sk_D_3 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ~ ( zip_tseitin_0 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X39: $i,X40: $i] :
      ( ( zip_tseitin_0 @ X39 @ X40 )
      | ( X39 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('8',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('10',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('11',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X4 != X3 )
      | ( r2_hidden @ X4 @ X5 )
      | ( X5
       != ( k2_tarski @ X6 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('12',plain,(
    ! [X3: $i,X6: $i] :
      ( r2_hidden @ X3 @ ( k2_tarski @ X6 @ X3 ) ) ),
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
    ! [X0: $i,X1: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( zip_tseitin_0 @ ( k1_tarski @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['9','15'])).

thf('17',plain,(
    zip_tseitin_1 @ sk_D_3 @ ( k1_tarski @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['6','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('19',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k1_relset_1 @ X34 @ X35 @ X33 )
        = ( k1_relat_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('20',plain,
    ( ( k1_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_D_3 )
    = ( k1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['3','17','20'])).

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

thf('22',plain,(
    ! [X21: $i,X23: $i,X25: $i,X26: $i] :
      ( ( X23
       != ( k2_relat_1 @ X21 ) )
      | ( r2_hidden @ X25 @ X23 )
      | ~ ( r2_hidden @ X26 @ ( k1_relat_1 @ X21 ) )
      | ( X25
       != ( k1_funct_1 @ X21 @ X26 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('23',plain,(
    ! [X21: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( r2_hidden @ X26 @ ( k1_relat_1 @ X21 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X21 @ X26 ) @ ( k2_relat_1 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_3 @ X0 ) @ ( k2_relat_1 @ sk_D_3 ) )
      | ~ ( v1_funct_1 @ sk_D_3 )
      | ~ ( v1_relat_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('27',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v1_relat_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('28',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_3 @ X0 ) @ ( k2_relat_1 @ sk_D_3 ) ) ) ),
    inference(demod,[status(thm)],['24','25','28'])).

thf('30',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_3 @ sk_C_1 ) @ ( k2_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['0','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('32',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X30 @ X31 @ X32 ) @ ( k1_zfmisc_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('33',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_D_3 ) @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('35',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k2_relset_1 @ X37 @ X38 @ X36 )
        = ( k2_relat_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('36',plain,
    ( ( k2_relset_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) @ sk_D_3 )
    = ( k2_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D_3 ) @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['33','36'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('38',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( m1_subset_1 @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_3 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ ( k1_funct_1 @ sk_D_3 @ sk_C_1 ) @ ( k1_tarski @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['30','39'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('41',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D_3 @ sk_C_1 ) @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf('44',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_3 @ sk_C_1 ) @ ( k1_tarski @ sk_B_1 ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X9: $i] :
      ( ( k2_tarski @ X9 @ X9 )
      = ( k1_tarski @ X9 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('46',plain,(
    ! [X3: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ( X7 = X6 )
      | ( X7 = X3 )
      | ( X5
       != ( k2_tarski @ X6 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('47',plain,(
    ! [X3: $i,X6: $i,X7: $i] :
      ( ( X7 = X3 )
      | ( X7 = X6 )
      | ~ ( r2_hidden @ X7 @ ( k2_tarski @ X6 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( k1_funct_1 @ sk_D_3 @ sk_C_1 )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['44','49'])).

thf('51',plain,(
    ( k1_funct_1 @ sk_D_3 @ sk_C_1 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['50','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DrNmBY6XPg
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:39:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.58  % Solved by: fo/fo7.sh
% 0.20/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.58  % done 133 iterations in 0.131s
% 0.20/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.58  % SZS output start Refutation
% 0.20/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.58  thf(sk_D_3_type, type, sk_D_3: $i).
% 0.20/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.58  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.58  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.58  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.58  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.58  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.58  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.20/0.58  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.58  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.20/0.58  thf(t65_funct_2, conjecture,
% 0.20/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.58     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.20/0.58         ( m1_subset_1 @
% 0.20/0.58           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.20/0.58       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.20/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.58    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.58        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.20/0.58            ( m1_subset_1 @
% 0.20/0.58              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.20/0.58          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.20/0.58    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.20/0.58  thf('0', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('1', plain, ((v1_funct_2 @ sk_D_3 @ sk_A @ (k1_tarski @ sk_B_1))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf(d1_funct_2, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.58       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.58           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.20/0.58             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.58         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.58           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.20/0.58             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.20/0.58  thf(zf_stmt_1, axiom,
% 0.20/0.58    (![C:$i,B:$i,A:$i]:
% 0.20/0.58     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.20/0.58       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.20/0.58  thf('2', plain,
% 0.20/0.58      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.20/0.58         (~ (v1_funct_2 @ X43 @ X41 @ X42)
% 0.20/0.58          | ((X41) = (k1_relset_1 @ X41 @ X42 @ X43))
% 0.20/0.58          | ~ (zip_tseitin_1 @ X43 @ X42 @ X41))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.58  thf('3', plain,
% 0.20/0.58      ((~ (zip_tseitin_1 @ sk_D_3 @ (k1_tarski @ sk_B_1) @ sk_A)
% 0.20/0.58        | ((sk_A) = (k1_relset_1 @ sk_A @ (k1_tarski @ sk_B_1) @ sk_D_3)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.58  thf('4', plain,
% 0.20/0.58      ((m1_subset_1 @ sk_D_3 @ 
% 0.20/0.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.20/0.58  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.20/0.58  thf(zf_stmt_4, axiom,
% 0.20/0.58    (![B:$i,A:$i]:
% 0.20/0.58     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.58       ( zip_tseitin_0 @ B @ A ) ))).
% 0.20/0.58  thf(zf_stmt_5, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.58       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.20/0.58         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.58           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.58             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.20/0.58  thf('5', plain,
% 0.20/0.58      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.20/0.58         (~ (zip_tseitin_0 @ X44 @ X45)
% 0.20/0.58          | (zip_tseitin_1 @ X46 @ X44 @ X45)
% 0.20/0.58          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44))))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.58  thf('6', plain,
% 0.20/0.58      (((zip_tseitin_1 @ sk_D_3 @ (k1_tarski @ sk_B_1) @ sk_A)
% 0.20/0.58        | ~ (zip_tseitin_0 @ (k1_tarski @ sk_B_1) @ sk_A))),
% 0.20/0.58      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.58  thf('7', plain,
% 0.20/0.58      (![X39 : $i, X40 : $i]:
% 0.20/0.58         ((zip_tseitin_0 @ X39 @ X40) | ((X39) = (k1_xboole_0)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.20/0.58  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.58  thf('8', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.58  thf('9', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.20/0.58      inference('sup+', [status(thm)], ['7', '8'])).
% 0.20/0.58  thf(t69_enumset1, axiom,
% 0.20/0.58    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.58  thf('10', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 0.20/0.58      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.58  thf(d2_tarski, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.20/0.58       ( ![D:$i]:
% 0.20/0.58         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.20/0.58  thf('11', plain,
% 0.20/0.58      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.58         (((X4) != (X3))
% 0.20/0.58          | (r2_hidden @ X4 @ X5)
% 0.20/0.58          | ((X5) != (k2_tarski @ X6 @ X3)))),
% 0.20/0.58      inference('cnf', [status(esa)], [d2_tarski])).
% 0.20/0.58  thf('12', plain,
% 0.20/0.58      (![X3 : $i, X6 : $i]: (r2_hidden @ X3 @ (k2_tarski @ X6 @ X3))),
% 0.20/0.58      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.58  thf(d1_xboole_0, axiom,
% 0.20/0.58    (![A:$i]:
% 0.20/0.58     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.58  thf('13', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.58  thf('14', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]: ~ (v1_xboole_0 @ (k2_tarski @ X1 @ X0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.58  thf('15', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.20/0.58      inference('sup-', [status(thm)], ['10', '14'])).
% 0.20/0.58  thf('16', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]: (zip_tseitin_0 @ (k1_tarski @ X0) @ X1)),
% 0.20/0.58      inference('sup-', [status(thm)], ['9', '15'])).
% 0.20/0.58  thf('17', plain, ((zip_tseitin_1 @ sk_D_3 @ (k1_tarski @ sk_B_1) @ sk_A)),
% 0.20/0.58      inference('demod', [status(thm)], ['6', '16'])).
% 0.20/0.58  thf('18', plain,
% 0.20/0.58      ((m1_subset_1 @ sk_D_3 @ 
% 0.20/0.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.58       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.58  thf('19', plain,
% 0.20/0.58      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.20/0.58         (((k1_relset_1 @ X34 @ X35 @ X33) = (k1_relat_1 @ X33))
% 0.20/0.58          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.20/0.59      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.59  thf('20', plain,
% 0.20/0.59      (((k1_relset_1 @ sk_A @ (k1_tarski @ sk_B_1) @ sk_D_3)
% 0.20/0.59         = (k1_relat_1 @ sk_D_3))),
% 0.20/0.59      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.59  thf('21', plain, (((sk_A) = (k1_relat_1 @ sk_D_3))),
% 0.20/0.59      inference('demod', [status(thm)], ['3', '17', '20'])).
% 0.20/0.59  thf(d5_funct_1, axiom,
% 0.20/0.59    (![A:$i]:
% 0.20/0.59     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.59       ( ![B:$i]:
% 0.20/0.59         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.20/0.59           ( ![C:$i]:
% 0.20/0.59             ( ( r2_hidden @ C @ B ) <=>
% 0.20/0.59               ( ?[D:$i]:
% 0.20/0.59                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.20/0.59                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.20/0.59  thf('22', plain,
% 0.20/0.59      (![X21 : $i, X23 : $i, X25 : $i, X26 : $i]:
% 0.20/0.59         (((X23) != (k2_relat_1 @ X21))
% 0.20/0.59          | (r2_hidden @ X25 @ X23)
% 0.20/0.59          | ~ (r2_hidden @ X26 @ (k1_relat_1 @ X21))
% 0.20/0.59          | ((X25) != (k1_funct_1 @ X21 @ X26))
% 0.20/0.59          | ~ (v1_funct_1 @ X21)
% 0.20/0.59          | ~ (v1_relat_1 @ X21))),
% 0.20/0.59      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.20/0.59  thf('23', plain,
% 0.20/0.59      (![X21 : $i, X26 : $i]:
% 0.20/0.59         (~ (v1_relat_1 @ X21)
% 0.20/0.59          | ~ (v1_funct_1 @ X21)
% 0.20/0.59          | ~ (r2_hidden @ X26 @ (k1_relat_1 @ X21))
% 0.20/0.59          | (r2_hidden @ (k1_funct_1 @ X21 @ X26) @ (k2_relat_1 @ X21)))),
% 0.20/0.59      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.59  thf('24', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.59          | (r2_hidden @ (k1_funct_1 @ sk_D_3 @ X0) @ (k2_relat_1 @ sk_D_3))
% 0.20/0.59          | ~ (v1_funct_1 @ sk_D_3)
% 0.20/0.59          | ~ (v1_relat_1 @ sk_D_3))),
% 0.20/0.59      inference('sup-', [status(thm)], ['21', '23'])).
% 0.20/0.59  thf('25', plain, ((v1_funct_1 @ sk_D_3)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('26', plain,
% 0.20/0.59      ((m1_subset_1 @ sk_D_3 @ 
% 0.20/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf(cc1_relset_1, axiom,
% 0.20/0.59    (![A:$i,B:$i,C:$i]:
% 0.20/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.59       ( v1_relat_1 @ C ) ))).
% 0.20/0.59  thf('27', plain,
% 0.20/0.59      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.20/0.59         ((v1_relat_1 @ X27)
% 0.20/0.59          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.20/0.59      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.59  thf('28', plain, ((v1_relat_1 @ sk_D_3)),
% 0.20/0.59      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.59  thf('29', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.59          | (r2_hidden @ (k1_funct_1 @ sk_D_3 @ X0) @ (k2_relat_1 @ sk_D_3)))),
% 0.20/0.59      inference('demod', [status(thm)], ['24', '25', '28'])).
% 0.20/0.59  thf('30', plain,
% 0.20/0.59      ((r2_hidden @ (k1_funct_1 @ sk_D_3 @ sk_C_1) @ (k2_relat_1 @ sk_D_3))),
% 0.20/0.59      inference('sup-', [status(thm)], ['0', '29'])).
% 0.20/0.59  thf('31', plain,
% 0.20/0.59      ((m1_subset_1 @ sk_D_3 @ 
% 0.20/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf(dt_k2_relset_1, axiom,
% 0.20/0.59    (![A:$i,B:$i,C:$i]:
% 0.20/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.59       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.20/0.59  thf('32', plain,
% 0.20/0.59      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.20/0.59         ((m1_subset_1 @ (k2_relset_1 @ X30 @ X31 @ X32) @ (k1_zfmisc_1 @ X31))
% 0.20/0.59          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.20/0.59      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.20/0.59  thf('33', plain,
% 0.20/0.59      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ (k1_tarski @ sk_B_1) @ sk_D_3) @ 
% 0.20/0.59        (k1_zfmisc_1 @ (k1_tarski @ sk_B_1)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.59  thf('34', plain,
% 0.20/0.59      ((m1_subset_1 @ sk_D_3 @ 
% 0.20/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.59    (![A:$i,B:$i,C:$i]:
% 0.20/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.59       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.59  thf('35', plain,
% 0.20/0.59      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.20/0.59         (((k2_relset_1 @ X37 @ X38 @ X36) = (k2_relat_1 @ X36))
% 0.20/0.59          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 0.20/0.59      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.59  thf('36', plain,
% 0.20/0.59      (((k2_relset_1 @ sk_A @ (k1_tarski @ sk_B_1) @ sk_D_3)
% 0.20/0.59         = (k2_relat_1 @ sk_D_3))),
% 0.20/0.59      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.59  thf('37', plain,
% 0.20/0.59      ((m1_subset_1 @ (k2_relat_1 @ sk_D_3) @ 
% 0.20/0.59        (k1_zfmisc_1 @ (k1_tarski @ sk_B_1)))),
% 0.20/0.59      inference('demod', [status(thm)], ['33', '36'])).
% 0.20/0.59  thf(t4_subset, axiom,
% 0.20/0.59    (![A:$i,B:$i,C:$i]:
% 0.20/0.59     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.20/0.59       ( m1_subset_1 @ A @ C ) ))).
% 0.20/0.59  thf('38', plain,
% 0.20/0.59      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.59         (~ (r2_hidden @ X17 @ X18)
% 0.20/0.59          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 0.20/0.59          | (m1_subset_1 @ X17 @ X19))),
% 0.20/0.59      inference('cnf', [status(esa)], [t4_subset])).
% 0.20/0.59  thf('39', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         ((m1_subset_1 @ X0 @ (k1_tarski @ sk_B_1))
% 0.20/0.59          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_3)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.59  thf('40', plain,
% 0.20/0.59      ((m1_subset_1 @ (k1_funct_1 @ sk_D_3 @ sk_C_1) @ (k1_tarski @ sk_B_1))),
% 0.20/0.59      inference('sup-', [status(thm)], ['30', '39'])).
% 0.20/0.59  thf(t2_subset, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( m1_subset_1 @ A @ B ) =>
% 0.20/0.59       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.59  thf('41', plain,
% 0.20/0.59      (![X15 : $i, X16 : $i]:
% 0.20/0.59         ((r2_hidden @ X15 @ X16)
% 0.20/0.59          | (v1_xboole_0 @ X16)
% 0.20/0.59          | ~ (m1_subset_1 @ X15 @ X16))),
% 0.20/0.59      inference('cnf', [status(esa)], [t2_subset])).
% 0.20/0.59  thf('42', plain,
% 0.20/0.59      (((v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.20/0.59        | (r2_hidden @ (k1_funct_1 @ sk_D_3 @ sk_C_1) @ (k1_tarski @ sk_B_1)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.59  thf('43', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.20/0.59      inference('sup-', [status(thm)], ['10', '14'])).
% 0.20/0.59  thf('44', plain,
% 0.20/0.59      ((r2_hidden @ (k1_funct_1 @ sk_D_3 @ sk_C_1) @ (k1_tarski @ sk_B_1))),
% 0.20/0.59      inference('clc', [status(thm)], ['42', '43'])).
% 0.20/0.59  thf('45', plain, (![X9 : $i]: ((k2_tarski @ X9 @ X9) = (k1_tarski @ X9))),
% 0.20/0.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.59  thf('46', plain,
% 0.20/0.59      (![X3 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.59         (~ (r2_hidden @ X7 @ X5)
% 0.20/0.59          | ((X7) = (X6))
% 0.20/0.59          | ((X7) = (X3))
% 0.20/0.59          | ((X5) != (k2_tarski @ X6 @ X3)))),
% 0.20/0.59      inference('cnf', [status(esa)], [d2_tarski])).
% 0.20/0.59  thf('47', plain,
% 0.20/0.59      (![X3 : $i, X6 : $i, X7 : $i]:
% 0.20/0.59         (((X7) = (X3))
% 0.20/0.59          | ((X7) = (X6))
% 0.20/0.59          | ~ (r2_hidden @ X7 @ (k2_tarski @ X6 @ X3)))),
% 0.20/0.59      inference('simplify', [status(thm)], ['46'])).
% 0.20/0.59  thf('48', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['45', '47'])).
% 0.20/0.59  thf('49', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]:
% 0.20/0.59         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.20/0.59      inference('simplify', [status(thm)], ['48'])).
% 0.20/0.59  thf('50', plain, (((k1_funct_1 @ sk_D_3 @ sk_C_1) = (sk_B_1))),
% 0.20/0.59      inference('sup-', [status(thm)], ['44', '49'])).
% 0.20/0.59  thf('51', plain, (((k1_funct_1 @ sk_D_3 @ sk_C_1) != (sk_B_1))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('52', plain, ($false),
% 0.20/0.59      inference('simplify_reflect-', [status(thm)], ['50', '51'])).
% 0.20/0.59  
% 0.20/0.59  % SZS output end Refutation
% 0.20/0.59  
% 0.20/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
