%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CB4zfVAY3n

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:29 EST 2020

% Result     : Theorem 12.52s
% Output     : Refutation 12.52s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 557 expanded)
%              Number of leaves         :   40 ( 189 expanded)
%              Depth                    :   24
%              Number of atoms          :  970 (6561 expanded)
%              Number of equality atoms :   68 ( 267 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t113_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ! [E: $i] :
                ( ( m1_subset_1 @ E @ A )
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
                  ( ( m1_subset_1 @ E @ A )
                 => ( ( k1_funct_1 @ C @ E )
                    = ( k1_funct_1 @ D @ E ) ) )
             => ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t113_funct_2])).

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
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_funct_2 @ X38 @ X36 @ X37 )
      | ( X36
        = ( k1_relset_1 @ X36 @ X37 @ X38 ) )
      | ~ ( zip_tseitin_1 @ X38 @ X37 @ X36 ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
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
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( zip_tseitin_0 @ X39 @ X40 )
      | ( zip_tseitin_1 @ X41 @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('10',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X34: $i,X35: $i] :
      ( ( zip_tseitin_0 @ X34 @ X35 )
      | ( X34 = k1_xboole_0 ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X24 ) ) )
      | ( v1_xboole_0 @ X25 ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( r2_relset_1 @ X31 @ X32 @ X30 @ X33 )
      | ( X30 != X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('30',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( r2_relset_1 @ X31 @ X32 @ X33 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X24 ) ) )
      | ( v1_xboole_0 @ X25 ) ) ),
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
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_funct_2 @ X38 @ X36 @ X37 )
      | ( X36
        = ( k1_relset_1 @ X36 @ X37 @ X38 ) )
      | ~ ( zip_tseitin_1 @ X38 @ X37 @ X36 ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
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
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( zip_tseitin_0 @ X39 @ X40 )
      | ( zip_tseitin_1 @ X41 @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ( X20 = X19 )
      | ( r2_hidden @ ( sk_C_1 @ X19 @ X20 ) @ ( k1_relat_1 @ X20 ) )
      | ( ( k1_relat_1 @ X20 )
       != ( k1_relat_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
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

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('73',plain,(
    ! [X14: $i,X15: $i] :
      ( ( m1_subset_1 @ X14 @ X15 )
      | ~ ( r2_hidden @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('74',plain,
    ( ( sk_C_2 = sk_D )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X42: $i] :
      ( ( ( k1_funct_1 @ sk_C_2 @ X42 )
        = ( k1_funct_1 @ sk_D @ X42 ) )
      | ~ ( m1_subset_1 @ X42 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( sk_C_2 = sk_D )
    | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ),
    inference(condensation,[status(thm)],['76'])).

thf('78',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ( X20 = X19 )
      | ( ( k1_funct_1 @ X20 @ ( sk_C_1 @ X19 @ X20 ) )
       != ( k1_funct_1 @ X19 @ ( sk_C_1 @ X19 @ X20 ) ) )
      | ( ( k1_relat_1 @ X20 )
       != ( k1_relat_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('79',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_2 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['60','61'])).

thf('81',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['51','56'])).

thf('83',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','43'])).

thf('84',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['67','68'])).

thf('86',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ( sk_A != sk_A )
    | ( sk_C_2 = sk_D ) ),
    inference(demod,[status(thm)],['79','80','81','82','83','84','85'])).

thf('87',plain,(
    sk_C_2 = sk_D ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( r2_relset_1 @ X31 @ X32 @ X33 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('90',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2 ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    $false ),
    inference(demod,[status(thm)],['0','87','90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CB4zfVAY3n
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.19/0.34  % DateTime   : Tue Dec  1 17:19:22 EST 2020
% 0.19/0.35  % CPUTime    : 
% 0.19/0.35  % Running portfolio for 600 s
% 0.19/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.35  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 12.52/12.78  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 12.52/12.78  % Solved by: fo/fo7.sh
% 12.52/12.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 12.52/12.78  % done 5462 iterations in 12.316s
% 12.52/12.78  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 12.52/12.78  % SZS output start Refutation
% 12.52/12.78  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 12.52/12.78  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 12.52/12.78  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 12.52/12.78  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 12.52/12.78  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 12.52/12.78  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 12.52/12.78  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 12.52/12.78  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 12.52/12.78  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 12.52/12.78  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 12.52/12.78  thf(sk_D_type, type, sk_D: $i).
% 12.52/12.78  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 12.52/12.78  thf(sk_C_2_type, type, sk_C_2: $i).
% 12.52/12.78  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 12.52/12.78  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 12.52/12.78  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 12.52/12.78  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 12.52/12.78  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 12.52/12.78  thf(sk_B_1_type, type, sk_B_1: $i).
% 12.52/12.78  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 12.52/12.78  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 12.52/12.78  thf(sk_A_type, type, sk_A: $i).
% 12.52/12.78  thf(t113_funct_2, conjecture,
% 12.52/12.78    (![A:$i,B:$i,C:$i]:
% 12.52/12.78     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 12.52/12.78         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 12.52/12.78       ( ![D:$i]:
% 12.52/12.78         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 12.52/12.78             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 12.52/12.78           ( ( ![E:$i]:
% 12.52/12.78               ( ( m1_subset_1 @ E @ A ) =>
% 12.52/12.78                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 12.52/12.78             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 12.52/12.78  thf(zf_stmt_0, negated_conjecture,
% 12.52/12.78    (~( ![A:$i,B:$i,C:$i]:
% 12.52/12.78        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 12.52/12.78            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 12.52/12.78          ( ![D:$i]:
% 12.52/12.78            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 12.52/12.78                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 12.52/12.78              ( ( ![E:$i]:
% 12.52/12.78                  ( ( m1_subset_1 @ E @ A ) =>
% 12.52/12.78                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 12.52/12.78                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 12.52/12.78    inference('cnf.neg', [status(esa)], [t113_funct_2])).
% 12.52/12.78  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 12.52/12.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.52/12.78  thf('1', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 12.52/12.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.52/12.78  thf(d1_funct_2, axiom,
% 12.52/12.78    (![A:$i,B:$i,C:$i]:
% 12.52/12.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 12.52/12.78       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 12.52/12.78           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 12.52/12.78             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 12.52/12.78         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 12.52/12.78           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 12.52/12.78             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 12.52/12.78  thf(zf_stmt_1, axiom,
% 12.52/12.78    (![C:$i,B:$i,A:$i]:
% 12.52/12.78     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 12.52/12.78       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 12.52/12.78  thf('2', plain,
% 12.52/12.78      (![X36 : $i, X37 : $i, X38 : $i]:
% 12.52/12.78         (~ (v1_funct_2 @ X38 @ X36 @ X37)
% 12.52/12.78          | ((X36) = (k1_relset_1 @ X36 @ X37 @ X38))
% 12.52/12.78          | ~ (zip_tseitin_1 @ X38 @ X37 @ X36))),
% 12.52/12.78      inference('cnf', [status(esa)], [zf_stmt_1])).
% 12.52/12.78  thf('3', plain,
% 12.52/12.78      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 12.52/12.78        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 12.52/12.78      inference('sup-', [status(thm)], ['1', '2'])).
% 12.52/12.78  thf('4', plain,
% 12.52/12.78      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 12.52/12.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.52/12.78  thf(redefinition_k1_relset_1, axiom,
% 12.52/12.78    (![A:$i,B:$i,C:$i]:
% 12.52/12.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 12.52/12.78       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 12.52/12.78  thf('5', plain,
% 12.52/12.78      (![X27 : $i, X28 : $i, X29 : $i]:
% 12.52/12.78         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 12.52/12.78          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 12.52/12.78      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 12.52/12.78  thf('6', plain,
% 12.52/12.78      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 12.52/12.78      inference('sup-', [status(thm)], ['4', '5'])).
% 12.52/12.78  thf('7', plain,
% 12.52/12.78      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 12.52/12.78        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 12.52/12.78      inference('demod', [status(thm)], ['3', '6'])).
% 12.52/12.78  thf('8', plain,
% 12.52/12.78      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 12.52/12.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.52/12.78  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 12.52/12.78  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 12.52/12.78  thf(zf_stmt_4, axiom,
% 12.52/12.78    (![B:$i,A:$i]:
% 12.52/12.78     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 12.52/12.78       ( zip_tseitin_0 @ B @ A ) ))).
% 12.52/12.78  thf(zf_stmt_5, axiom,
% 12.52/12.78    (![A:$i,B:$i,C:$i]:
% 12.52/12.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 12.52/12.78       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 12.52/12.78         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 12.52/12.78           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 12.52/12.78             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 12.52/12.78  thf('9', plain,
% 12.52/12.78      (![X39 : $i, X40 : $i, X41 : $i]:
% 12.52/12.78         (~ (zip_tseitin_0 @ X39 @ X40)
% 12.52/12.78          | (zip_tseitin_1 @ X41 @ X39 @ X40)
% 12.52/12.78          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39))))),
% 12.52/12.78      inference('cnf', [status(esa)], [zf_stmt_5])).
% 12.52/12.78  thf('10', plain,
% 12.52/12.78      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 12.52/12.78        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 12.52/12.78      inference('sup-', [status(thm)], ['8', '9'])).
% 12.52/12.78  thf('11', plain,
% 12.52/12.78      (![X34 : $i, X35 : $i]:
% 12.52/12.78         ((zip_tseitin_0 @ X34 @ X35) | ((X34) = (k1_xboole_0)))),
% 12.52/12.78      inference('cnf', [status(esa)], [zf_stmt_4])).
% 12.52/12.78  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 12.52/12.78  thf('12', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 12.52/12.78      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 12.52/12.78  thf('13', plain,
% 12.52/12.78      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 12.52/12.78      inference('sup+', [status(thm)], ['11', '12'])).
% 12.52/12.78  thf('14', plain,
% 12.52/12.78      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 12.52/12.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.52/12.78  thf(cc4_relset_1, axiom,
% 12.52/12.78    (![A:$i,B:$i]:
% 12.52/12.78     ( ( v1_xboole_0 @ A ) =>
% 12.52/12.78       ( ![C:$i]:
% 12.52/12.78         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 12.52/12.78           ( v1_xboole_0 @ C ) ) ) ))).
% 12.52/12.78  thf('15', plain,
% 12.52/12.78      (![X24 : $i, X25 : $i, X26 : $i]:
% 12.52/12.78         (~ (v1_xboole_0 @ X24)
% 12.52/12.78          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X24)))
% 12.52/12.78          | (v1_xboole_0 @ X25))),
% 12.52/12.78      inference('cnf', [status(esa)], [cc4_relset_1])).
% 12.52/12.78  thf('16', plain, (((v1_xboole_0 @ sk_C_2) | ~ (v1_xboole_0 @ sk_B_1))),
% 12.52/12.78      inference('sup-', [status(thm)], ['14', '15'])).
% 12.52/12.78  thf('17', plain,
% 12.52/12.78      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_C_2))),
% 12.52/12.78      inference('sup-', [status(thm)], ['13', '16'])).
% 12.52/12.78  thf('18', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 12.52/12.78      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 12.52/12.78  thf(d3_tarski, axiom,
% 12.52/12.78    (![A:$i,B:$i]:
% 12.52/12.78     ( ( r1_tarski @ A @ B ) <=>
% 12.52/12.78       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 12.52/12.78  thf('19', plain,
% 12.52/12.78      (![X4 : $i, X6 : $i]:
% 12.52/12.78         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 12.52/12.78      inference('cnf', [status(esa)], [d3_tarski])).
% 12.52/12.78  thf(d1_xboole_0, axiom,
% 12.52/12.78    (![A:$i]:
% 12.52/12.78     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 12.52/12.78  thf('20', plain,
% 12.52/12.78      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 12.52/12.78      inference('cnf', [status(esa)], [d1_xboole_0])).
% 12.52/12.78  thf('21', plain,
% 12.52/12.78      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 12.52/12.78      inference('sup-', [status(thm)], ['19', '20'])).
% 12.52/12.78  thf('22', plain,
% 12.52/12.78      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 12.52/12.78      inference('sup-', [status(thm)], ['19', '20'])).
% 12.52/12.78  thf(d10_xboole_0, axiom,
% 12.52/12.78    (![A:$i,B:$i]:
% 12.52/12.78     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 12.52/12.78  thf('23', plain,
% 12.52/12.78      (![X7 : $i, X9 : $i]:
% 12.52/12.78         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 12.52/12.78      inference('cnf', [status(esa)], [d10_xboole_0])).
% 12.52/12.78  thf('24', plain,
% 12.52/12.78      (![X0 : $i, X1 : $i]:
% 12.52/12.78         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 12.52/12.78      inference('sup-', [status(thm)], ['22', '23'])).
% 12.52/12.78  thf('25', plain,
% 12.52/12.78      (![X0 : $i, X1 : $i]:
% 12.52/12.78         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 12.52/12.78      inference('sup-', [status(thm)], ['21', '24'])).
% 12.52/12.78  thf('26', plain,
% 12.52/12.78      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 12.52/12.78      inference('sup-', [status(thm)], ['18', '25'])).
% 12.52/12.78  thf('27', plain,
% 12.52/12.78      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 12.52/12.78      inference('sup-', [status(thm)], ['18', '25'])).
% 12.52/12.78  thf(t4_subset_1, axiom,
% 12.52/12.78    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 12.52/12.78  thf('28', plain,
% 12.52/12.78      (![X13 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 12.52/12.78      inference('cnf', [status(esa)], [t4_subset_1])).
% 12.52/12.78  thf(redefinition_r2_relset_1, axiom,
% 12.52/12.78    (![A:$i,B:$i,C:$i,D:$i]:
% 12.52/12.78     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 12.52/12.78         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 12.52/12.78       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 12.52/12.78  thf('29', plain,
% 12.52/12.78      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 12.52/12.78         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 12.52/12.78          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 12.52/12.78          | (r2_relset_1 @ X31 @ X32 @ X30 @ X33)
% 12.52/12.78          | ((X30) != (X33)))),
% 12.52/12.78      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 12.52/12.78  thf('30', plain,
% 12.52/12.78      (![X31 : $i, X32 : $i, X33 : $i]:
% 12.52/12.78         ((r2_relset_1 @ X31 @ X32 @ X33 @ X33)
% 12.52/12.78          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 12.52/12.78      inference('simplify', [status(thm)], ['29'])).
% 12.52/12.78  thf('31', plain,
% 12.52/12.78      (![X0 : $i, X1 : $i]: (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 12.52/12.78      inference('sup-', [status(thm)], ['28', '30'])).
% 12.52/12.78  thf('32', plain,
% 12.52/12.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.52/12.78         ((r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0))),
% 12.52/12.78      inference('sup+', [status(thm)], ['27', '31'])).
% 12.52/12.78  thf('33', plain,
% 12.52/12.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 12.52/12.78         ((r2_relset_1 @ X3 @ X2 @ X1 @ X0)
% 12.52/12.78          | ~ (v1_xboole_0 @ X0)
% 12.52/12.78          | ~ (v1_xboole_0 @ X1))),
% 12.52/12.78      inference('sup+', [status(thm)], ['26', '32'])).
% 12.52/12.78  thf('34', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 12.52/12.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.52/12.78  thf('35', plain, ((~ (v1_xboole_0 @ sk_C_2) | ~ (v1_xboole_0 @ sk_D))),
% 12.52/12.78      inference('sup-', [status(thm)], ['33', '34'])).
% 12.52/12.78  thf('36', plain,
% 12.52/12.78      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | ~ (v1_xboole_0 @ sk_D))),
% 12.52/12.78      inference('sup-', [status(thm)], ['17', '35'])).
% 12.52/12.78  thf('37', plain,
% 12.52/12.78      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 12.52/12.78      inference('sup+', [status(thm)], ['11', '12'])).
% 12.52/12.78  thf('38', plain,
% 12.52/12.78      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 12.52/12.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.52/12.78  thf('39', plain,
% 12.52/12.78      (![X24 : $i, X25 : $i, X26 : $i]:
% 12.52/12.78         (~ (v1_xboole_0 @ X24)
% 12.52/12.78          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X24)))
% 12.52/12.78          | (v1_xboole_0 @ X25))),
% 12.52/12.78      inference('cnf', [status(esa)], [cc4_relset_1])).
% 12.52/12.78  thf('40', plain, (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_B_1))),
% 12.52/12.78      inference('sup-', [status(thm)], ['38', '39'])).
% 12.52/12.78  thf('41', plain,
% 12.52/12.78      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_D))),
% 12.52/12.78      inference('sup-', [status(thm)], ['37', '40'])).
% 12.52/12.78  thf('42', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0)),
% 12.52/12.78      inference('clc', [status(thm)], ['36', '41'])).
% 12.52/12.78  thf('43', plain, ((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)),
% 12.52/12.78      inference('demod', [status(thm)], ['10', '42'])).
% 12.52/12.78  thf('44', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 12.52/12.78      inference('demod', [status(thm)], ['7', '43'])).
% 12.52/12.78  thf('45', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1)),
% 12.52/12.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.52/12.78  thf('46', plain,
% 12.52/12.78      (![X36 : $i, X37 : $i, X38 : $i]:
% 12.52/12.78         (~ (v1_funct_2 @ X38 @ X36 @ X37)
% 12.52/12.78          | ((X36) = (k1_relset_1 @ X36 @ X37 @ X38))
% 12.52/12.78          | ~ (zip_tseitin_1 @ X38 @ X37 @ X36))),
% 12.52/12.78      inference('cnf', [status(esa)], [zf_stmt_1])).
% 12.52/12.78  thf('47', plain,
% 12.52/12.78      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 12.52/12.78        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2)))),
% 12.52/12.78      inference('sup-', [status(thm)], ['45', '46'])).
% 12.52/12.78  thf('48', plain,
% 12.52/12.78      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 12.52/12.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.52/12.78  thf('49', plain,
% 12.52/12.78      (![X27 : $i, X28 : $i, X29 : $i]:
% 12.52/12.78         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 12.52/12.78          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 12.52/12.78      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 12.52/12.78  thf('50', plain,
% 12.52/12.78      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 12.52/12.78      inference('sup-', [status(thm)], ['48', '49'])).
% 12.52/12.78  thf('51', plain,
% 12.52/12.78      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 12.52/12.78        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 12.52/12.78      inference('demod', [status(thm)], ['47', '50'])).
% 12.52/12.78  thf('52', plain,
% 12.52/12.78      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 12.52/12.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.52/12.78  thf('53', plain,
% 12.52/12.78      (![X39 : $i, X40 : $i, X41 : $i]:
% 12.52/12.78         (~ (zip_tseitin_0 @ X39 @ X40)
% 12.52/12.78          | (zip_tseitin_1 @ X41 @ X39 @ X40)
% 12.52/12.78          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39))))),
% 12.52/12.78      inference('cnf', [status(esa)], [zf_stmt_5])).
% 12.52/12.78  thf('54', plain,
% 12.52/12.78      (((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 12.52/12.78        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 12.52/12.78      inference('sup-', [status(thm)], ['52', '53'])).
% 12.52/12.78  thf('55', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0)),
% 12.52/12.78      inference('clc', [status(thm)], ['36', '41'])).
% 12.52/12.78  thf('56', plain, ((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)),
% 12.52/12.78      inference('demod', [status(thm)], ['54', '55'])).
% 12.52/12.78  thf('57', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 12.52/12.78      inference('demod', [status(thm)], ['51', '56'])).
% 12.52/12.78  thf(t9_funct_1, axiom,
% 12.52/12.78    (![A:$i]:
% 12.52/12.78     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 12.52/12.78       ( ![B:$i]:
% 12.52/12.78         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 12.52/12.78           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 12.52/12.78               ( ![C:$i]:
% 12.52/12.78                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 12.52/12.78                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 12.52/12.78             ( ( A ) = ( B ) ) ) ) ) ))).
% 12.52/12.78  thf('58', plain,
% 12.52/12.78      (![X19 : $i, X20 : $i]:
% 12.52/12.78         (~ (v1_relat_1 @ X19)
% 12.52/12.78          | ~ (v1_funct_1 @ X19)
% 12.52/12.78          | ((X20) = (X19))
% 12.52/12.78          | (r2_hidden @ (sk_C_1 @ X19 @ X20) @ (k1_relat_1 @ X20))
% 12.52/12.78          | ((k1_relat_1 @ X20) != (k1_relat_1 @ X19))
% 12.52/12.78          | ~ (v1_funct_1 @ X20)
% 12.52/12.78          | ~ (v1_relat_1 @ X20))),
% 12.52/12.78      inference('cnf', [status(esa)], [t9_funct_1])).
% 12.52/12.78  thf('59', plain,
% 12.52/12.78      (![X0 : $i]:
% 12.52/12.78         (((sk_A) != (k1_relat_1 @ X0))
% 12.52/12.78          | ~ (v1_relat_1 @ sk_C_2)
% 12.52/12.78          | ~ (v1_funct_1 @ sk_C_2)
% 12.52/12.78          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 12.52/12.78          | ((sk_C_2) = (X0))
% 12.52/12.78          | ~ (v1_funct_1 @ X0)
% 12.52/12.78          | ~ (v1_relat_1 @ X0))),
% 12.52/12.78      inference('sup-', [status(thm)], ['57', '58'])).
% 12.52/12.78  thf('60', plain,
% 12.52/12.78      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 12.52/12.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.52/12.78  thf(cc1_relset_1, axiom,
% 12.52/12.78    (![A:$i,B:$i,C:$i]:
% 12.52/12.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 12.52/12.78       ( v1_relat_1 @ C ) ))).
% 12.52/12.78  thf('61', plain,
% 12.52/12.78      (![X21 : $i, X22 : $i, X23 : $i]:
% 12.52/12.78         ((v1_relat_1 @ X21)
% 12.52/12.78          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 12.52/12.78      inference('cnf', [status(esa)], [cc1_relset_1])).
% 12.52/12.78  thf('62', plain, ((v1_relat_1 @ sk_C_2)),
% 12.52/12.78      inference('sup-', [status(thm)], ['60', '61'])).
% 12.52/12.78  thf('63', plain, ((v1_funct_1 @ sk_C_2)),
% 12.52/12.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.52/12.78  thf('64', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 12.52/12.78      inference('demod', [status(thm)], ['51', '56'])).
% 12.52/12.78  thf('65', plain,
% 12.52/12.78      (![X0 : $i]:
% 12.52/12.78         (((sk_A) != (k1_relat_1 @ X0))
% 12.52/12.78          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ sk_A)
% 12.52/12.78          | ((sk_C_2) = (X0))
% 12.52/12.78          | ~ (v1_funct_1 @ X0)
% 12.52/12.78          | ~ (v1_relat_1 @ X0))),
% 12.52/12.78      inference('demod', [status(thm)], ['59', '62', '63', '64'])).
% 12.52/12.78  thf('66', plain,
% 12.52/12.78      ((((sk_A) != (sk_A))
% 12.52/12.78        | ~ (v1_relat_1 @ sk_D)
% 12.52/12.78        | ~ (v1_funct_1 @ sk_D)
% 12.52/12.78        | ((sk_C_2) = (sk_D))
% 12.52/12.78        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 12.52/12.78      inference('sup-', [status(thm)], ['44', '65'])).
% 12.52/12.78  thf('67', plain,
% 12.52/12.78      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 12.52/12.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.52/12.78  thf('68', plain,
% 12.52/12.78      (![X21 : $i, X22 : $i, X23 : $i]:
% 12.52/12.78         ((v1_relat_1 @ X21)
% 12.52/12.78          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 12.52/12.78      inference('cnf', [status(esa)], [cc1_relset_1])).
% 12.52/12.78  thf('69', plain, ((v1_relat_1 @ sk_D)),
% 12.52/12.78      inference('sup-', [status(thm)], ['67', '68'])).
% 12.52/12.78  thf('70', plain, ((v1_funct_1 @ sk_D)),
% 12.52/12.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.52/12.78  thf('71', plain,
% 12.52/12.78      ((((sk_A) != (sk_A))
% 12.52/12.78        | ((sk_C_2) = (sk_D))
% 12.52/12.78        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 12.52/12.78      inference('demod', [status(thm)], ['66', '69', '70'])).
% 12.52/12.78  thf('72', plain,
% 12.52/12.78      (((r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A) | ((sk_C_2) = (sk_D)))),
% 12.52/12.78      inference('simplify', [status(thm)], ['71'])).
% 12.52/12.78  thf(t1_subset, axiom,
% 12.52/12.78    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 12.52/12.78  thf('73', plain,
% 12.52/12.78      (![X14 : $i, X15 : $i]:
% 12.52/12.78         ((m1_subset_1 @ X14 @ X15) | ~ (r2_hidden @ X14 @ X15))),
% 12.52/12.78      inference('cnf', [status(esa)], [t1_subset])).
% 12.52/12.78  thf('74', plain,
% 12.52/12.78      ((((sk_C_2) = (sk_D)) | (m1_subset_1 @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 12.52/12.78      inference('sup-', [status(thm)], ['72', '73'])).
% 12.52/12.78  thf('75', plain,
% 12.52/12.78      (![X42 : $i]:
% 12.52/12.78         (((k1_funct_1 @ sk_C_2 @ X42) = (k1_funct_1 @ sk_D @ X42))
% 12.52/12.78          | ~ (m1_subset_1 @ X42 @ sk_A))),
% 12.52/12.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.52/12.78  thf('76', plain,
% 12.52/12.78      ((((sk_C_2) = (sk_D))
% 12.52/12.78        | ((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 12.52/12.78            = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2))))),
% 12.52/12.78      inference('sup-', [status(thm)], ['74', '75'])).
% 12.52/12.78  thf('77', plain,
% 12.52/12.78      (((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 12.52/12.78         = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2)))),
% 12.52/12.78      inference('condensation', [status(thm)], ['76'])).
% 12.52/12.78  thf('78', plain,
% 12.52/12.78      (![X19 : $i, X20 : $i]:
% 12.52/12.78         (~ (v1_relat_1 @ X19)
% 12.52/12.78          | ~ (v1_funct_1 @ X19)
% 12.52/12.78          | ((X20) = (X19))
% 12.52/12.78          | ((k1_funct_1 @ X20 @ (sk_C_1 @ X19 @ X20))
% 12.52/12.78              != (k1_funct_1 @ X19 @ (sk_C_1 @ X19 @ X20)))
% 12.52/12.78          | ((k1_relat_1 @ X20) != (k1_relat_1 @ X19))
% 12.52/12.78          | ~ (v1_funct_1 @ X20)
% 12.52/12.78          | ~ (v1_relat_1 @ X20))),
% 12.52/12.78      inference('cnf', [status(esa)], [t9_funct_1])).
% 12.52/12.78  thf('79', plain,
% 12.52/12.78      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 12.52/12.78          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 12.52/12.78        | ~ (v1_relat_1 @ sk_C_2)
% 12.52/12.78        | ~ (v1_funct_1 @ sk_C_2)
% 12.52/12.78        | ((k1_relat_1 @ sk_C_2) != (k1_relat_1 @ sk_D))
% 12.52/12.78        | ((sk_C_2) = (sk_D))
% 12.52/12.78        | ~ (v1_funct_1 @ sk_D)
% 12.52/12.78        | ~ (v1_relat_1 @ sk_D))),
% 12.52/12.78      inference('sup-', [status(thm)], ['77', '78'])).
% 12.52/12.78  thf('80', plain, ((v1_relat_1 @ sk_C_2)),
% 12.52/12.78      inference('sup-', [status(thm)], ['60', '61'])).
% 12.52/12.78  thf('81', plain, ((v1_funct_1 @ sk_C_2)),
% 12.52/12.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.52/12.78  thf('82', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 12.52/12.78      inference('demod', [status(thm)], ['51', '56'])).
% 12.52/12.78  thf('83', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 12.52/12.78      inference('demod', [status(thm)], ['7', '43'])).
% 12.52/12.78  thf('84', plain, ((v1_funct_1 @ sk_D)),
% 12.52/12.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.52/12.78  thf('85', plain, ((v1_relat_1 @ sk_D)),
% 12.52/12.78      inference('sup-', [status(thm)], ['67', '68'])).
% 12.52/12.78  thf('86', plain,
% 12.52/12.78      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 12.52/12.78          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 12.52/12.78        | ((sk_A) != (sk_A))
% 12.52/12.78        | ((sk_C_2) = (sk_D)))),
% 12.52/12.78      inference('demod', [status(thm)],
% 12.52/12.78                ['79', '80', '81', '82', '83', '84', '85'])).
% 12.52/12.78  thf('87', plain, (((sk_C_2) = (sk_D))),
% 12.52/12.78      inference('simplify', [status(thm)], ['86'])).
% 12.52/12.78  thf('88', plain,
% 12.52/12.78      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 12.52/12.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.52/12.78  thf('89', plain,
% 12.52/12.78      (![X31 : $i, X32 : $i, X33 : $i]:
% 12.52/12.78         ((r2_relset_1 @ X31 @ X32 @ X33 @ X33)
% 12.52/12.78          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 12.52/12.78      inference('simplify', [status(thm)], ['29'])).
% 12.52/12.78  thf('90', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2)),
% 12.52/12.78      inference('sup-', [status(thm)], ['88', '89'])).
% 12.52/12.78  thf('91', plain, ($false),
% 12.52/12.78      inference('demod', [status(thm)], ['0', '87', '90'])).
% 12.52/12.78  
% 12.52/12.78  % SZS output end Refutation
% 12.52/12.78  
% 12.61/12.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
