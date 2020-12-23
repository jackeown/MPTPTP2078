%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WC8zjjkyH8

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:34 EST 2020

% Result     : Theorem 5.96s
% Output     : Refutation 5.96s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 554 expanded)
%              Number of leaves         :   39 ( 188 expanded)
%              Depth                    :   23
%              Number of atoms          :  950 (6541 expanded)
%              Number of equality atoms :   67 ( 266 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(t18_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ! [E: $i] :
                ( ( r2_hidden @ E @ A )
               => ( ( k1_funct_1 @ C @ E )
                  = ( k1_funct_1 @ D @ E ) ) )
           => ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ B )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
           => ( ! [E: $i] :
                  ( ( r2_hidden @ E @ A )
                 => ( ( k1_funct_1 @ C @ E )
                    = ( k1_funct_1 @ D @ E ) ) )
             => ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t18_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
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
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_2 @ X36 @ X34 @ X35 )
      | ( X34
        = ( k1_relset_1 @ X34 @ X35 @ X36 ) )
      | ~ ( zip_tseitin_1 @ X36 @ X35 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('5',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('6',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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

thf('9',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( zip_tseitin_0 @ X37 @ X38 )
      | ( zip_tseitin_1 @ X39 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('10',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

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
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('15',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X22 ) ) )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('16',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('19',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('28',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('29',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( r2_relset_1 @ X29 @ X30 @ X28 @ X31 )
      | ( X28 != X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('30',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( r2_relset_1 @ X29 @ X30 @ X31 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_relset_1 @ X3 @ X2 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','32'])).

thf('34',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ~ ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ~ ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['17','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('38',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X22 ) ) )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('40',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B_1 @ X0 ) ),
    inference(clc,[status(thm)],['36','41'])).

thf('43',plain,(
    zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['10','42'])).

thf('44',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','43'])).

thf('45',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_2 @ X36 @ X34 @ X35 )
      | ( X34
        = ( k1_relset_1 @ X34 @ X35 @ X36 ) )
      | ~ ( zip_tseitin_1 @ X36 @ X35 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('47',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('50',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['47','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( zip_tseitin_0 @ X37 @ X38 )
      | ( zip_tseitin_1 @ X39 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('54',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B_1 @ X0 ) ),
    inference(clc,[status(thm)],['36','41'])).

thf('56',plain,(
    zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['51','56'])).

thf(t9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( ( k1_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ! [C: $i] :
                  ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
                 => ( ( k1_funct_1 @ A @ C )
                    = ( k1_funct_1 @ B @ C ) ) ) )
           => ( A = B ) ) ) ) )).

thf('58',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ( X18 = X17 )
      | ( r2_hidden @ ( sk_C_1 @ X17 @ X18 ) @ ( k1_relat_1 @ X18 ) )
      | ( ( k1_relat_1 @ X18 )
       != ( k1_relat_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('61',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_relat_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('62',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['51','56'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ sk_A )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['59','62','63','64'])).

thf('66',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['44','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_relat_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('69',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( sk_A != sk_A )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['66','69','70'])).

thf('72',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A )
    | ( sk_C_2 = sk_D ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X40: $i] :
      ( ( ( k1_funct_1 @ sk_C_2 @ X40 )
        = ( k1_funct_1 @ sk_D @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( sk_C_2 = sk_D )
    | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ),
    inference(condensation,[status(thm)],['74'])).

thf('76',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ( X18 = X17 )
      | ( ( k1_funct_1 @ X18 @ ( sk_C_1 @ X17 @ X18 ) )
       != ( k1_funct_1 @ X17 @ ( sk_C_1 @ X17 @ X18 ) ) )
      | ( ( k1_relat_1 @ X18 )
       != ( k1_relat_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('77',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_2 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['60','61'])).

thf('79',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['51','56'])).

thf('81',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','43'])).

thf('82',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['67','68'])).

thf('84',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ( sk_A != sk_A )
    | ( sk_C_2 = sk_D ) ),
    inference(demod,[status(thm)],['77','78','79','80','81','82','83'])).

thf('85',plain,(
    sk_C_2 = sk_D ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( r2_relset_1 @ X29 @ X30 @ X31 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('88',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2 ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    $false ),
    inference(demod,[status(thm)],['0','85','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WC8zjjkyH8
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:05:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 5.96/6.21  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 5.96/6.21  % Solved by: fo/fo7.sh
% 5.96/6.21  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.96/6.21  % done 3656 iterations in 5.764s
% 5.96/6.21  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 5.96/6.21  % SZS output start Refutation
% 5.96/6.21  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 5.96/6.21  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 5.96/6.21  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 5.96/6.21  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.96/6.21  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.96/6.21  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.96/6.21  thf(sk_D_type, type, sk_D: $i).
% 5.96/6.21  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 5.96/6.21  thf(sk_A_type, type, sk_A: $i).
% 5.96/6.21  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 5.96/6.21  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 5.96/6.21  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 5.96/6.21  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 5.96/6.21  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 5.96/6.21  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 5.96/6.21  thf(sk_B_1_type, type, sk_B_1: $i).
% 5.96/6.21  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.96/6.21  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.96/6.21  thf(sk_C_2_type, type, sk_C_2: $i).
% 5.96/6.21  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 5.96/6.21  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 5.96/6.21  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 5.96/6.21  thf(t18_funct_2, conjecture,
% 5.96/6.21    (![A:$i,B:$i,C:$i]:
% 5.96/6.21     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.96/6.21         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.96/6.21       ( ![D:$i]:
% 5.96/6.21         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 5.96/6.21             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.96/6.21           ( ( ![E:$i]:
% 5.96/6.21               ( ( r2_hidden @ E @ A ) =>
% 5.96/6.21                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 5.96/6.21             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 5.96/6.21  thf(zf_stmt_0, negated_conjecture,
% 5.96/6.21    (~( ![A:$i,B:$i,C:$i]:
% 5.96/6.21        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.96/6.21            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.96/6.21          ( ![D:$i]:
% 5.96/6.21            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 5.96/6.21                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.96/6.21              ( ( ![E:$i]:
% 5.96/6.21                  ( ( r2_hidden @ E @ A ) =>
% 5.96/6.21                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 5.96/6.21                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 5.96/6.21    inference('cnf.neg', [status(esa)], [t18_funct_2])).
% 5.96/6.21  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 5.96/6.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.96/6.21  thf('1', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 5.96/6.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.96/6.21  thf(d1_funct_2, axiom,
% 5.96/6.21    (![A:$i,B:$i,C:$i]:
% 5.96/6.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.96/6.21       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 5.96/6.21           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 5.96/6.21             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 5.96/6.21         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 5.96/6.21           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 5.96/6.21             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 5.96/6.21  thf(zf_stmt_1, axiom,
% 5.96/6.21    (![C:$i,B:$i,A:$i]:
% 5.96/6.21     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 5.96/6.21       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 5.96/6.21  thf('2', plain,
% 5.96/6.21      (![X34 : $i, X35 : $i, X36 : $i]:
% 5.96/6.21         (~ (v1_funct_2 @ X36 @ X34 @ X35)
% 5.96/6.21          | ((X34) = (k1_relset_1 @ X34 @ X35 @ X36))
% 5.96/6.21          | ~ (zip_tseitin_1 @ X36 @ X35 @ X34))),
% 5.96/6.21      inference('cnf', [status(esa)], [zf_stmt_1])).
% 5.96/6.21  thf('3', plain,
% 5.96/6.21      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 5.96/6.21        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 5.96/6.21      inference('sup-', [status(thm)], ['1', '2'])).
% 5.96/6.21  thf('4', plain,
% 5.96/6.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.96/6.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.96/6.21  thf(redefinition_k1_relset_1, axiom,
% 5.96/6.21    (![A:$i,B:$i,C:$i]:
% 5.96/6.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.96/6.21       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 5.96/6.21  thf('5', plain,
% 5.96/6.21      (![X25 : $i, X26 : $i, X27 : $i]:
% 5.96/6.21         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 5.96/6.21          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 5.96/6.21      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 5.96/6.21  thf('6', plain,
% 5.96/6.21      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 5.96/6.21      inference('sup-', [status(thm)], ['4', '5'])).
% 5.96/6.21  thf('7', plain,
% 5.96/6.21      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 5.96/6.21        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 5.96/6.21      inference('demod', [status(thm)], ['3', '6'])).
% 5.96/6.21  thf('8', plain,
% 5.96/6.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.96/6.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.96/6.21  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 5.96/6.21  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 5.96/6.21  thf(zf_stmt_4, axiom,
% 5.96/6.21    (![B:$i,A:$i]:
% 5.96/6.21     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 5.96/6.21       ( zip_tseitin_0 @ B @ A ) ))).
% 5.96/6.21  thf(zf_stmt_5, axiom,
% 5.96/6.21    (![A:$i,B:$i,C:$i]:
% 5.96/6.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.96/6.21       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 5.96/6.21         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 5.96/6.21           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 5.96/6.21             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 5.96/6.21  thf('9', plain,
% 5.96/6.21      (![X37 : $i, X38 : $i, X39 : $i]:
% 5.96/6.21         (~ (zip_tseitin_0 @ X37 @ X38)
% 5.96/6.21          | (zip_tseitin_1 @ X39 @ X37 @ X38)
% 5.96/6.21          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37))))),
% 5.96/6.21      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.96/6.21  thf('10', plain,
% 5.96/6.21      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 5.96/6.21        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 5.96/6.21      inference('sup-', [status(thm)], ['8', '9'])).
% 5.96/6.21  thf('11', plain,
% 5.96/6.21      (![X32 : $i, X33 : $i]:
% 5.96/6.21         ((zip_tseitin_0 @ X32 @ X33) | ((X32) = (k1_xboole_0)))),
% 5.96/6.21      inference('cnf', [status(esa)], [zf_stmt_4])).
% 5.96/6.21  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 5.96/6.21  thf('12', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 5.96/6.21      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 5.96/6.21  thf('13', plain,
% 5.96/6.21      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 5.96/6.21      inference('sup+', [status(thm)], ['11', '12'])).
% 5.96/6.21  thf('14', plain,
% 5.96/6.21      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.96/6.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.96/6.21  thf(cc4_relset_1, axiom,
% 5.96/6.21    (![A:$i,B:$i]:
% 5.96/6.21     ( ( v1_xboole_0 @ A ) =>
% 5.96/6.21       ( ![C:$i]:
% 5.96/6.21         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 5.96/6.21           ( v1_xboole_0 @ C ) ) ) ))).
% 5.96/6.21  thf('15', plain,
% 5.96/6.21      (![X22 : $i, X23 : $i, X24 : $i]:
% 5.96/6.21         (~ (v1_xboole_0 @ X22)
% 5.96/6.21          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X22)))
% 5.96/6.21          | (v1_xboole_0 @ X23))),
% 5.96/6.21      inference('cnf', [status(esa)], [cc4_relset_1])).
% 5.96/6.21  thf('16', plain, (((v1_xboole_0 @ sk_C_2) | ~ (v1_xboole_0 @ sk_B_1))),
% 5.96/6.21      inference('sup-', [status(thm)], ['14', '15'])).
% 5.96/6.21  thf('17', plain,
% 5.96/6.21      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_C_2))),
% 5.96/6.21      inference('sup-', [status(thm)], ['13', '16'])).
% 5.96/6.21  thf('18', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 5.96/6.21      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 5.96/6.21  thf(d3_tarski, axiom,
% 5.96/6.21    (![A:$i,B:$i]:
% 5.96/6.21     ( ( r1_tarski @ A @ B ) <=>
% 5.96/6.21       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 5.96/6.21  thf('19', plain,
% 5.96/6.21      (![X4 : $i, X6 : $i]:
% 5.96/6.21         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 5.96/6.21      inference('cnf', [status(esa)], [d3_tarski])).
% 5.96/6.21  thf(d1_xboole_0, axiom,
% 5.96/6.21    (![A:$i]:
% 5.96/6.21     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 5.96/6.21  thf('20', plain,
% 5.96/6.21      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 5.96/6.21      inference('cnf', [status(esa)], [d1_xboole_0])).
% 5.96/6.21  thf('21', plain,
% 5.96/6.21      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 5.96/6.21      inference('sup-', [status(thm)], ['19', '20'])).
% 5.96/6.21  thf('22', plain,
% 5.96/6.21      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 5.96/6.21      inference('sup-', [status(thm)], ['19', '20'])).
% 5.96/6.21  thf(d10_xboole_0, axiom,
% 5.96/6.21    (![A:$i,B:$i]:
% 5.96/6.21     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 5.96/6.21  thf('23', plain,
% 5.96/6.21      (![X7 : $i, X9 : $i]:
% 5.96/6.21         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 5.96/6.21      inference('cnf', [status(esa)], [d10_xboole_0])).
% 5.96/6.21  thf('24', plain,
% 5.96/6.21      (![X0 : $i, X1 : $i]:
% 5.96/6.21         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 5.96/6.21      inference('sup-', [status(thm)], ['22', '23'])).
% 5.96/6.21  thf('25', plain,
% 5.96/6.21      (![X0 : $i, X1 : $i]:
% 5.96/6.21         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 5.96/6.21      inference('sup-', [status(thm)], ['21', '24'])).
% 5.96/6.21  thf('26', plain,
% 5.96/6.21      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 5.96/6.21      inference('sup-', [status(thm)], ['18', '25'])).
% 5.96/6.21  thf('27', plain,
% 5.96/6.21      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 5.96/6.21      inference('sup-', [status(thm)], ['18', '25'])).
% 5.96/6.21  thf(t4_subset_1, axiom,
% 5.96/6.21    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 5.96/6.21  thf('28', plain,
% 5.96/6.21      (![X13 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 5.96/6.21      inference('cnf', [status(esa)], [t4_subset_1])).
% 5.96/6.21  thf(redefinition_r2_relset_1, axiom,
% 5.96/6.21    (![A:$i,B:$i,C:$i,D:$i]:
% 5.96/6.21     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 5.96/6.21         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.96/6.21       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 5.96/6.21  thf('29', plain,
% 5.96/6.21      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 5.96/6.21         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 5.96/6.21          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 5.96/6.21          | (r2_relset_1 @ X29 @ X30 @ X28 @ X31)
% 5.96/6.21          | ((X28) != (X31)))),
% 5.96/6.21      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 5.96/6.21  thf('30', plain,
% 5.96/6.21      (![X29 : $i, X30 : $i, X31 : $i]:
% 5.96/6.21         ((r2_relset_1 @ X29 @ X30 @ X31 @ X31)
% 5.96/6.21          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 5.96/6.21      inference('simplify', [status(thm)], ['29'])).
% 5.96/6.21  thf('31', plain,
% 5.96/6.21      (![X0 : $i, X1 : $i]: (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 5.96/6.21      inference('sup-', [status(thm)], ['28', '30'])).
% 5.96/6.21  thf('32', plain,
% 5.96/6.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.96/6.21         ((r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0))),
% 5.96/6.21      inference('sup+', [status(thm)], ['27', '31'])).
% 5.96/6.21  thf('33', plain,
% 5.96/6.21      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.96/6.21         ((r2_relset_1 @ X3 @ X2 @ X1 @ X0)
% 5.96/6.21          | ~ (v1_xboole_0 @ X0)
% 5.96/6.21          | ~ (v1_xboole_0 @ X1))),
% 5.96/6.21      inference('sup+', [status(thm)], ['26', '32'])).
% 5.96/6.21  thf('34', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 5.96/6.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.96/6.21  thf('35', plain, ((~ (v1_xboole_0 @ sk_C_2) | ~ (v1_xboole_0 @ sk_D))),
% 5.96/6.21      inference('sup-', [status(thm)], ['33', '34'])).
% 5.96/6.21  thf('36', plain,
% 5.96/6.21      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | ~ (v1_xboole_0 @ sk_D))),
% 5.96/6.21      inference('sup-', [status(thm)], ['17', '35'])).
% 5.96/6.21  thf('37', plain,
% 5.96/6.21      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 5.96/6.21      inference('sup+', [status(thm)], ['11', '12'])).
% 5.96/6.21  thf('38', plain,
% 5.96/6.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.96/6.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.96/6.21  thf('39', plain,
% 5.96/6.21      (![X22 : $i, X23 : $i, X24 : $i]:
% 5.96/6.21         (~ (v1_xboole_0 @ X22)
% 5.96/6.21          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X22)))
% 5.96/6.21          | (v1_xboole_0 @ X23))),
% 5.96/6.21      inference('cnf', [status(esa)], [cc4_relset_1])).
% 5.96/6.21  thf('40', plain, (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_B_1))),
% 5.96/6.21      inference('sup-', [status(thm)], ['38', '39'])).
% 5.96/6.21  thf('41', plain,
% 5.96/6.21      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_D))),
% 5.96/6.21      inference('sup-', [status(thm)], ['37', '40'])).
% 5.96/6.21  thf('42', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0)),
% 5.96/6.21      inference('clc', [status(thm)], ['36', '41'])).
% 5.96/6.21  thf('43', plain, ((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)),
% 5.96/6.21      inference('demod', [status(thm)], ['10', '42'])).
% 5.96/6.21  thf('44', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 5.96/6.21      inference('demod', [status(thm)], ['7', '43'])).
% 5.96/6.21  thf('45', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1)),
% 5.96/6.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.96/6.21  thf('46', plain,
% 5.96/6.21      (![X34 : $i, X35 : $i, X36 : $i]:
% 5.96/6.21         (~ (v1_funct_2 @ X36 @ X34 @ X35)
% 5.96/6.21          | ((X34) = (k1_relset_1 @ X34 @ X35 @ X36))
% 5.96/6.21          | ~ (zip_tseitin_1 @ X36 @ X35 @ X34))),
% 5.96/6.21      inference('cnf', [status(esa)], [zf_stmt_1])).
% 5.96/6.21  thf('47', plain,
% 5.96/6.21      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 5.96/6.21        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2)))),
% 5.96/6.21      inference('sup-', [status(thm)], ['45', '46'])).
% 5.96/6.21  thf('48', plain,
% 5.96/6.21      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.96/6.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.96/6.21  thf('49', plain,
% 5.96/6.21      (![X25 : $i, X26 : $i, X27 : $i]:
% 5.96/6.21         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 5.96/6.21          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 5.96/6.21      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 5.96/6.21  thf('50', plain,
% 5.96/6.21      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 5.96/6.21      inference('sup-', [status(thm)], ['48', '49'])).
% 5.96/6.21  thf('51', plain,
% 5.96/6.21      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 5.96/6.21        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 5.96/6.21      inference('demod', [status(thm)], ['47', '50'])).
% 5.96/6.21  thf('52', plain,
% 5.96/6.21      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.96/6.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.96/6.21  thf('53', plain,
% 5.96/6.21      (![X37 : $i, X38 : $i, X39 : $i]:
% 5.96/6.21         (~ (zip_tseitin_0 @ X37 @ X38)
% 5.96/6.21          | (zip_tseitin_1 @ X39 @ X37 @ X38)
% 5.96/6.21          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37))))),
% 5.96/6.21      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.96/6.21  thf('54', plain,
% 5.96/6.21      (((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 5.96/6.21        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 5.96/6.21      inference('sup-', [status(thm)], ['52', '53'])).
% 5.96/6.21  thf('55', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0)),
% 5.96/6.21      inference('clc', [status(thm)], ['36', '41'])).
% 5.96/6.21  thf('56', plain, ((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)),
% 5.96/6.21      inference('demod', [status(thm)], ['54', '55'])).
% 5.96/6.21  thf('57', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 5.96/6.21      inference('demod', [status(thm)], ['51', '56'])).
% 5.96/6.21  thf(t9_funct_1, axiom,
% 5.96/6.21    (![A:$i]:
% 5.96/6.21     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 5.96/6.21       ( ![B:$i]:
% 5.96/6.21         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 5.96/6.21           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 5.96/6.21               ( ![C:$i]:
% 5.96/6.21                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 5.96/6.21                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 5.96/6.21             ( ( A ) = ( B ) ) ) ) ) ))).
% 5.96/6.21  thf('58', plain,
% 5.96/6.21      (![X17 : $i, X18 : $i]:
% 5.96/6.21         (~ (v1_relat_1 @ X17)
% 5.96/6.21          | ~ (v1_funct_1 @ X17)
% 5.96/6.21          | ((X18) = (X17))
% 5.96/6.21          | (r2_hidden @ (sk_C_1 @ X17 @ X18) @ (k1_relat_1 @ X18))
% 5.96/6.21          | ((k1_relat_1 @ X18) != (k1_relat_1 @ X17))
% 5.96/6.21          | ~ (v1_funct_1 @ X18)
% 5.96/6.21          | ~ (v1_relat_1 @ X18))),
% 5.96/6.21      inference('cnf', [status(esa)], [t9_funct_1])).
% 5.96/6.21  thf('59', plain,
% 5.96/6.21      (![X0 : $i]:
% 5.96/6.21         (((sk_A) != (k1_relat_1 @ X0))
% 5.96/6.21          | ~ (v1_relat_1 @ sk_C_2)
% 5.96/6.21          | ~ (v1_funct_1 @ sk_C_2)
% 5.96/6.21          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 5.96/6.21          | ((sk_C_2) = (X0))
% 5.96/6.21          | ~ (v1_funct_1 @ X0)
% 5.96/6.21          | ~ (v1_relat_1 @ X0))),
% 5.96/6.21      inference('sup-', [status(thm)], ['57', '58'])).
% 5.96/6.21  thf('60', plain,
% 5.96/6.21      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.96/6.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.96/6.21  thf(cc1_relset_1, axiom,
% 5.96/6.21    (![A:$i,B:$i,C:$i]:
% 5.96/6.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.96/6.21       ( v1_relat_1 @ C ) ))).
% 5.96/6.21  thf('61', plain,
% 5.96/6.21      (![X19 : $i, X20 : $i, X21 : $i]:
% 5.96/6.21         ((v1_relat_1 @ X19)
% 5.96/6.21          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 5.96/6.21      inference('cnf', [status(esa)], [cc1_relset_1])).
% 5.96/6.21  thf('62', plain, ((v1_relat_1 @ sk_C_2)),
% 5.96/6.21      inference('sup-', [status(thm)], ['60', '61'])).
% 5.96/6.21  thf('63', plain, ((v1_funct_1 @ sk_C_2)),
% 5.96/6.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.96/6.21  thf('64', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 5.96/6.21      inference('demod', [status(thm)], ['51', '56'])).
% 5.96/6.21  thf('65', plain,
% 5.96/6.21      (![X0 : $i]:
% 5.96/6.21         (((sk_A) != (k1_relat_1 @ X0))
% 5.96/6.21          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ sk_A)
% 5.96/6.21          | ((sk_C_2) = (X0))
% 5.96/6.21          | ~ (v1_funct_1 @ X0)
% 5.96/6.21          | ~ (v1_relat_1 @ X0))),
% 5.96/6.21      inference('demod', [status(thm)], ['59', '62', '63', '64'])).
% 5.96/6.21  thf('66', plain,
% 5.96/6.21      ((((sk_A) != (sk_A))
% 5.96/6.21        | ~ (v1_relat_1 @ sk_D)
% 5.96/6.21        | ~ (v1_funct_1 @ sk_D)
% 5.96/6.21        | ((sk_C_2) = (sk_D))
% 5.96/6.21        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 5.96/6.21      inference('sup-', [status(thm)], ['44', '65'])).
% 5.96/6.21  thf('67', plain,
% 5.96/6.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.96/6.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.96/6.21  thf('68', plain,
% 5.96/6.21      (![X19 : $i, X20 : $i, X21 : $i]:
% 5.96/6.21         ((v1_relat_1 @ X19)
% 5.96/6.21          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 5.96/6.21      inference('cnf', [status(esa)], [cc1_relset_1])).
% 5.96/6.21  thf('69', plain, ((v1_relat_1 @ sk_D)),
% 5.96/6.21      inference('sup-', [status(thm)], ['67', '68'])).
% 5.96/6.21  thf('70', plain, ((v1_funct_1 @ sk_D)),
% 5.96/6.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.96/6.21  thf('71', plain,
% 5.96/6.21      ((((sk_A) != (sk_A))
% 5.96/6.21        | ((sk_C_2) = (sk_D))
% 5.96/6.21        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 5.96/6.21      inference('demod', [status(thm)], ['66', '69', '70'])).
% 5.96/6.21  thf('72', plain,
% 5.96/6.21      (((r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A) | ((sk_C_2) = (sk_D)))),
% 5.96/6.21      inference('simplify', [status(thm)], ['71'])).
% 5.96/6.21  thf('73', plain,
% 5.96/6.21      (![X40 : $i]:
% 5.96/6.21         (((k1_funct_1 @ sk_C_2 @ X40) = (k1_funct_1 @ sk_D @ X40))
% 5.96/6.21          | ~ (r2_hidden @ X40 @ sk_A))),
% 5.96/6.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.96/6.21  thf('74', plain,
% 5.96/6.21      ((((sk_C_2) = (sk_D))
% 5.96/6.21        | ((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 5.96/6.21            = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2))))),
% 5.96/6.21      inference('sup-', [status(thm)], ['72', '73'])).
% 5.96/6.21  thf('75', plain,
% 5.96/6.21      (((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 5.96/6.21         = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2)))),
% 5.96/6.21      inference('condensation', [status(thm)], ['74'])).
% 5.96/6.21  thf('76', plain,
% 5.96/6.21      (![X17 : $i, X18 : $i]:
% 5.96/6.21         (~ (v1_relat_1 @ X17)
% 5.96/6.21          | ~ (v1_funct_1 @ X17)
% 5.96/6.21          | ((X18) = (X17))
% 5.96/6.21          | ((k1_funct_1 @ X18 @ (sk_C_1 @ X17 @ X18))
% 5.96/6.21              != (k1_funct_1 @ X17 @ (sk_C_1 @ X17 @ X18)))
% 5.96/6.21          | ((k1_relat_1 @ X18) != (k1_relat_1 @ X17))
% 5.96/6.21          | ~ (v1_funct_1 @ X18)
% 5.96/6.21          | ~ (v1_relat_1 @ X18))),
% 5.96/6.21      inference('cnf', [status(esa)], [t9_funct_1])).
% 5.96/6.21  thf('77', plain,
% 5.96/6.21      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 5.96/6.21          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 5.96/6.21        | ~ (v1_relat_1 @ sk_C_2)
% 5.96/6.21        | ~ (v1_funct_1 @ sk_C_2)
% 5.96/6.21        | ((k1_relat_1 @ sk_C_2) != (k1_relat_1 @ sk_D))
% 5.96/6.21        | ((sk_C_2) = (sk_D))
% 5.96/6.21        | ~ (v1_funct_1 @ sk_D)
% 5.96/6.21        | ~ (v1_relat_1 @ sk_D))),
% 5.96/6.21      inference('sup-', [status(thm)], ['75', '76'])).
% 5.96/6.21  thf('78', plain, ((v1_relat_1 @ sk_C_2)),
% 5.96/6.21      inference('sup-', [status(thm)], ['60', '61'])).
% 5.96/6.21  thf('79', plain, ((v1_funct_1 @ sk_C_2)),
% 5.96/6.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.96/6.21  thf('80', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 5.96/6.21      inference('demod', [status(thm)], ['51', '56'])).
% 5.96/6.21  thf('81', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 5.96/6.21      inference('demod', [status(thm)], ['7', '43'])).
% 5.96/6.21  thf('82', plain, ((v1_funct_1 @ sk_D)),
% 5.96/6.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.96/6.21  thf('83', plain, ((v1_relat_1 @ sk_D)),
% 5.96/6.21      inference('sup-', [status(thm)], ['67', '68'])).
% 5.96/6.21  thf('84', plain,
% 5.96/6.21      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 5.96/6.21          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 5.96/6.21        | ((sk_A) != (sk_A))
% 5.96/6.21        | ((sk_C_2) = (sk_D)))),
% 5.96/6.21      inference('demod', [status(thm)],
% 5.96/6.21                ['77', '78', '79', '80', '81', '82', '83'])).
% 5.96/6.21  thf('85', plain, (((sk_C_2) = (sk_D))),
% 5.96/6.21      inference('simplify', [status(thm)], ['84'])).
% 5.96/6.21  thf('86', plain,
% 5.96/6.21      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.96/6.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.96/6.21  thf('87', plain,
% 5.96/6.21      (![X29 : $i, X30 : $i, X31 : $i]:
% 5.96/6.21         ((r2_relset_1 @ X29 @ X30 @ X31 @ X31)
% 5.96/6.21          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 5.96/6.21      inference('simplify', [status(thm)], ['29'])).
% 5.96/6.21  thf('88', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2)),
% 5.96/6.21      inference('sup-', [status(thm)], ['86', '87'])).
% 5.96/6.21  thf('89', plain, ($false),
% 5.96/6.21      inference('demod', [status(thm)], ['0', '85', '88'])).
% 5.96/6.21  
% 5.96/6.21  % SZS output end Refutation
% 5.96/6.21  
% 5.96/6.22  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
