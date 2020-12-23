%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rrXaNTpm3W

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:38 EST 2020

% Result     : Theorem 2.36s
% Output     : Refutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :  180 (1203 expanded)
%              Number of leaves         :   45 ( 394 expanded)
%              Depth                    :   25
%              Number of atoms          : 1229 (12107 expanded)
%              Number of equality atoms :   87 ( 561 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( v1_funct_2 @ X42 @ X40 @ X41 )
      | ( X40
        = ( k1_relset_1 @ X40 @ X41 @ X42 ) )
      | ~ ( zip_tseitin_1 @ X42 @ X41 @ X40 ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k1_relset_1 @ X32 @ X33 @ X31 )
        = ( k1_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
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
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( zip_tseitin_0 @ X43 @ X44 )
      | ( zip_tseitin_1 @ X45 @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('10',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X38: $i,X39: $i] :
      ( ( zip_tseitin_0 @ X38 @ X39 )
      | ( X38 = k1_xboole_0 ) ) ),
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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('15',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_xboole_0 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X28 ) ) )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('16',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_D ) ) ),
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
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( r2_relset_1 @ X35 @ X36 @ X34 @ X37 )
      | ( X34 != X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('30',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( r2_relset_1 @ X35 @ X36 @ X37 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
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
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('37',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_xboole_0 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X28 ) ) )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('39',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('42',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('44',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf('47',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('48',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v4_relat_1 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('49',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('50',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v4_relat_1 @ X19 @ X20 )
      | ( r1_tarski @ ( k1_relat_1 @ X19 ) @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('52',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_zfmisc_1 @ X11 @ X12 )
        = k1_xboole_0 )
      | ( X11 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('53',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X12 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('54',plain,(
    ! [X21: $i,X22: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('55',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['51','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ k1_xboole_0 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['46','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['45','59'])).

thf('61',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['44','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf('65',plain,(
    ! [X12: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X12 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf('69',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_zfmisc_1 @ X11 @ X12 )
        = k1_xboole_0 )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('70',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_xboole_0 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X28 ) ) )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('72',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('74',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['68','74'])).

thf('76',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['67','75'])).

thf('77',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['66','76'])).

thf('78',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('79',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['63','79'])).

thf('81',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(clc,[status(thm)],['35','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B_1 @ X0 ) ),
    inference('sup-',[status(thm)],['17','81'])).

thf('83',plain,(
    zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['10','82'])).

thf('84',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','83'])).

thf('85',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( v1_funct_2 @ X42 @ X40 @ X41 )
      | ( X40
        = ( k1_relset_1 @ X40 @ X41 @ X42 ) )
      | ~ ( zip_tseitin_1 @ X42 @ X41 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('87',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k1_relset_1 @ X32 @ X33 @ X31 )
        = ( k1_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('90',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['87','90'])).

thf('92',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( zip_tseitin_0 @ X43 @ X44 )
      | ( zip_tseitin_1 @ X45 @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('94',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B_1 @ X0 ) ),
    inference('sup-',[status(thm)],['17','81'])).

thf('96',plain,(
    zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['91','96'])).

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

thf('98',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ( X24 = X23 )
      | ( r2_hidden @ ( sk_C_1 @ X23 @ X24 ) @ ( k1_relat_1 @ X24 ) )
      | ( ( k1_relat_1 @ X24 )
       != ( k1_relat_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('101',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('102',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X21: $i,X22: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('104',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['91','96'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ sk_A )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['99','104','105','106'])).

thf('108',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['84','107'])).

thf('109',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('111',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X21: $i,X22: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('113',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( sk_A != sk_A )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['108','113','114'])).

thf('116',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A )
    | ( sk_C_2 = sk_D ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    ! [X46: $i] :
      ( ( ( k1_funct_1 @ sk_C_2 @ X46 )
        = ( k1_funct_1 @ sk_D @ X46 ) )
      | ~ ( r2_hidden @ X46 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( sk_C_2 = sk_D )
    | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,
    ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ),
    inference(condensation,[status(thm)],['118'])).

thf('120',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ( X24 = X23 )
      | ( ( k1_funct_1 @ X24 @ ( sk_C_1 @ X23 @ X24 ) )
       != ( k1_funct_1 @ X23 @ ( sk_C_1 @ X23 @ X24 ) ) )
      | ( ( k1_relat_1 @ X24 )
       != ( k1_relat_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('121',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_2 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['102','103'])).

thf('123',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['91','96'])).

thf('125',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','83'])).

thf('126',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['111','112'])).

thf('128',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ( sk_A != sk_A )
    | ( sk_C_2 = sk_D ) ),
    inference(demod,[status(thm)],['121','122','123','124','125','126','127'])).

thf('129',plain,(
    sk_C_2 = sk_D ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( r2_relset_1 @ X35 @ X36 @ X37 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('132',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2 ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    $false ),
    inference(demod,[status(thm)],['0','129','132'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rrXaNTpm3W
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:38:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 2.36/2.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.36/2.53  % Solved by: fo/fo7.sh
% 2.36/2.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.36/2.53  % done 3413 iterations in 2.068s
% 2.36/2.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.36/2.53  % SZS output start Refutation
% 2.36/2.53  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.36/2.53  thf(sk_C_2_type, type, sk_C_2: $i).
% 2.36/2.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.36/2.53  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.36/2.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.36/2.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.36/2.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.36/2.53  thf(sk_A_type, type, sk_A: $i).
% 2.36/2.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.36/2.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.36/2.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.36/2.53  thf(sk_D_type, type, sk_D: $i).
% 2.36/2.53  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 2.36/2.53  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 2.36/2.53  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.36/2.53  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.36/2.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.36/2.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.36/2.53  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.36/2.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.36/2.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.36/2.53  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 2.36/2.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.36/2.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.36/2.53  thf(t18_funct_2, conjecture,
% 2.36/2.53    (![A:$i,B:$i,C:$i]:
% 2.36/2.53     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.36/2.53         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.36/2.53       ( ![D:$i]:
% 2.36/2.53         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.36/2.53             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.36/2.53           ( ( ![E:$i]:
% 2.36/2.53               ( ( r2_hidden @ E @ A ) =>
% 2.36/2.53                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 2.36/2.53             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 2.36/2.53  thf(zf_stmt_0, negated_conjecture,
% 2.36/2.53    (~( ![A:$i,B:$i,C:$i]:
% 2.36/2.53        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.36/2.53            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.36/2.53          ( ![D:$i]:
% 2.36/2.53            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.36/2.53                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.36/2.53              ( ( ![E:$i]:
% 2.36/2.53                  ( ( r2_hidden @ E @ A ) =>
% 2.36/2.53                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 2.36/2.53                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 2.36/2.53    inference('cnf.neg', [status(esa)], [t18_funct_2])).
% 2.36/2.53  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 2.36/2.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.36/2.53  thf('1', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 2.36/2.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.36/2.53  thf(d1_funct_2, axiom,
% 2.36/2.53    (![A:$i,B:$i,C:$i]:
% 2.36/2.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.36/2.53       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.36/2.53           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.36/2.53             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.36/2.53         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.36/2.53           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.36/2.53             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.36/2.53  thf(zf_stmt_1, axiom,
% 2.36/2.53    (![C:$i,B:$i,A:$i]:
% 2.36/2.53     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.36/2.53       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.36/2.53  thf('2', plain,
% 2.36/2.53      (![X40 : $i, X41 : $i, X42 : $i]:
% 2.36/2.53         (~ (v1_funct_2 @ X42 @ X40 @ X41)
% 2.36/2.53          | ((X40) = (k1_relset_1 @ X40 @ X41 @ X42))
% 2.36/2.53          | ~ (zip_tseitin_1 @ X42 @ X41 @ X40))),
% 2.36/2.53      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.36/2.53  thf('3', plain,
% 2.36/2.53      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 2.36/2.53        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 2.36/2.53      inference('sup-', [status(thm)], ['1', '2'])).
% 2.36/2.53  thf('4', plain,
% 2.36/2.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.36/2.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.36/2.53  thf(redefinition_k1_relset_1, axiom,
% 2.36/2.53    (![A:$i,B:$i,C:$i]:
% 2.36/2.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.36/2.53       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 2.36/2.53  thf('5', plain,
% 2.36/2.53      (![X31 : $i, X32 : $i, X33 : $i]:
% 2.36/2.53         (((k1_relset_1 @ X32 @ X33 @ X31) = (k1_relat_1 @ X31))
% 2.36/2.53          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 2.36/2.53      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.36/2.53  thf('6', plain,
% 2.36/2.53      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 2.36/2.53      inference('sup-', [status(thm)], ['4', '5'])).
% 2.36/2.53  thf('7', plain,
% 2.36/2.53      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 2.36/2.53        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 2.36/2.53      inference('demod', [status(thm)], ['3', '6'])).
% 2.36/2.53  thf('8', plain,
% 2.36/2.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.36/2.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.36/2.53  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.36/2.53  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 2.36/2.53  thf(zf_stmt_4, axiom,
% 2.36/2.53    (![B:$i,A:$i]:
% 2.36/2.53     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.36/2.53       ( zip_tseitin_0 @ B @ A ) ))).
% 2.36/2.53  thf(zf_stmt_5, axiom,
% 2.36/2.53    (![A:$i,B:$i,C:$i]:
% 2.36/2.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.36/2.53       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.36/2.53         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.36/2.53           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.36/2.53             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.36/2.53  thf('9', plain,
% 2.36/2.53      (![X43 : $i, X44 : $i, X45 : $i]:
% 2.36/2.53         (~ (zip_tseitin_0 @ X43 @ X44)
% 2.36/2.53          | (zip_tseitin_1 @ X45 @ X43 @ X44)
% 2.36/2.53          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43))))),
% 2.36/2.53      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.36/2.53  thf('10', plain,
% 2.36/2.53      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 2.36/2.53        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 2.36/2.53      inference('sup-', [status(thm)], ['8', '9'])).
% 2.36/2.53  thf('11', plain,
% 2.36/2.53      (![X38 : $i, X39 : $i]:
% 2.36/2.53         ((zip_tseitin_0 @ X38 @ X39) | ((X38) = (k1_xboole_0)))),
% 2.36/2.53      inference('cnf', [status(esa)], [zf_stmt_4])).
% 2.36/2.53  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 2.36/2.53  thf('12', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.36/2.53      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.36/2.53  thf('13', plain,
% 2.36/2.53      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 2.36/2.53      inference('sup+', [status(thm)], ['11', '12'])).
% 2.36/2.53  thf('14', plain,
% 2.36/2.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.36/2.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.36/2.53  thf(cc4_relset_1, axiom,
% 2.36/2.53    (![A:$i,B:$i]:
% 2.36/2.53     ( ( v1_xboole_0 @ A ) =>
% 2.36/2.53       ( ![C:$i]:
% 2.36/2.53         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 2.36/2.53           ( v1_xboole_0 @ C ) ) ) ))).
% 2.36/2.53  thf('15', plain,
% 2.36/2.53      (![X28 : $i, X29 : $i, X30 : $i]:
% 2.36/2.53         (~ (v1_xboole_0 @ X28)
% 2.36/2.53          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X28)))
% 2.36/2.53          | (v1_xboole_0 @ X29))),
% 2.36/2.53      inference('cnf', [status(esa)], [cc4_relset_1])).
% 2.36/2.53  thf('16', plain, (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_B_1))),
% 2.36/2.53      inference('sup-', [status(thm)], ['14', '15'])).
% 2.36/2.53  thf('17', plain,
% 2.36/2.53      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_D))),
% 2.36/2.53      inference('sup-', [status(thm)], ['13', '16'])).
% 2.36/2.53  thf('18', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.36/2.53      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.36/2.53  thf(d3_tarski, axiom,
% 2.36/2.53    (![A:$i,B:$i]:
% 2.36/2.53     ( ( r1_tarski @ A @ B ) <=>
% 2.36/2.53       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 2.36/2.53  thf('19', plain,
% 2.36/2.53      (![X4 : $i, X6 : $i]:
% 2.36/2.53         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 2.36/2.53      inference('cnf', [status(esa)], [d3_tarski])).
% 2.36/2.53  thf(d1_xboole_0, axiom,
% 2.36/2.53    (![A:$i]:
% 2.36/2.53     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 2.36/2.53  thf('20', plain,
% 2.36/2.53      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 2.36/2.53      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.36/2.53  thf('21', plain,
% 2.36/2.53      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 2.36/2.53      inference('sup-', [status(thm)], ['19', '20'])).
% 2.36/2.53  thf('22', plain,
% 2.36/2.53      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 2.36/2.53      inference('sup-', [status(thm)], ['19', '20'])).
% 2.36/2.53  thf(d10_xboole_0, axiom,
% 2.36/2.53    (![A:$i,B:$i]:
% 2.36/2.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.36/2.53  thf('23', plain,
% 2.36/2.53      (![X7 : $i, X9 : $i]:
% 2.36/2.53         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 2.36/2.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.36/2.53  thf('24', plain,
% 2.36/2.53      (![X0 : $i, X1 : $i]:
% 2.36/2.53         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 2.36/2.53      inference('sup-', [status(thm)], ['22', '23'])).
% 2.36/2.53  thf('25', plain,
% 2.36/2.53      (![X0 : $i, X1 : $i]:
% 2.36/2.53         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 2.36/2.53      inference('sup-', [status(thm)], ['21', '24'])).
% 2.36/2.53  thf('26', plain,
% 2.36/2.53      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 2.36/2.53      inference('sup-', [status(thm)], ['18', '25'])).
% 2.36/2.53  thf('27', plain,
% 2.36/2.53      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 2.36/2.53      inference('sup-', [status(thm)], ['18', '25'])).
% 2.36/2.53  thf(t4_subset_1, axiom,
% 2.36/2.53    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 2.36/2.53  thf('28', plain,
% 2.36/2.53      (![X13 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 2.36/2.53      inference('cnf', [status(esa)], [t4_subset_1])).
% 2.36/2.53  thf(redefinition_r2_relset_1, axiom,
% 2.36/2.53    (![A:$i,B:$i,C:$i,D:$i]:
% 2.36/2.53     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.36/2.53         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.36/2.53       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 2.36/2.53  thf('29', plain,
% 2.36/2.53      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 2.36/2.53         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 2.36/2.53          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 2.36/2.53          | (r2_relset_1 @ X35 @ X36 @ X34 @ X37)
% 2.36/2.53          | ((X34) != (X37)))),
% 2.36/2.53      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.36/2.53  thf('30', plain,
% 2.36/2.53      (![X35 : $i, X36 : $i, X37 : $i]:
% 2.36/2.53         ((r2_relset_1 @ X35 @ X36 @ X37 @ X37)
% 2.36/2.53          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 2.36/2.53      inference('simplify', [status(thm)], ['29'])).
% 2.36/2.53  thf('31', plain,
% 2.36/2.53      (![X0 : $i, X1 : $i]: (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 2.36/2.53      inference('sup-', [status(thm)], ['28', '30'])).
% 2.36/2.53  thf('32', plain,
% 2.36/2.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.36/2.53         ((r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0))),
% 2.36/2.53      inference('sup+', [status(thm)], ['27', '31'])).
% 2.36/2.53  thf('33', plain,
% 2.36/2.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.36/2.53         ((r2_relset_1 @ X3 @ X2 @ X1 @ X0)
% 2.36/2.53          | ~ (v1_xboole_0 @ X0)
% 2.36/2.53          | ~ (v1_xboole_0 @ X1))),
% 2.36/2.53      inference('sup+', [status(thm)], ['26', '32'])).
% 2.36/2.53  thf('34', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 2.36/2.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.36/2.53  thf('35', plain, ((~ (v1_xboole_0 @ sk_C_2) | ~ (v1_xboole_0 @ sk_D))),
% 2.36/2.53      inference('sup-', [status(thm)], ['33', '34'])).
% 2.36/2.53  thf('36', plain,
% 2.36/2.53      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 2.36/2.53      inference('sup+', [status(thm)], ['11', '12'])).
% 2.36/2.53  thf('37', plain,
% 2.36/2.53      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.36/2.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.36/2.53  thf('38', plain,
% 2.36/2.53      (![X28 : $i, X29 : $i, X30 : $i]:
% 2.36/2.53         (~ (v1_xboole_0 @ X28)
% 2.36/2.53          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X28)))
% 2.36/2.53          | (v1_xboole_0 @ X29))),
% 2.36/2.53      inference('cnf', [status(esa)], [cc4_relset_1])).
% 2.36/2.53  thf('39', plain, (((v1_xboole_0 @ sk_C_2) | ~ (v1_xboole_0 @ sk_B_1))),
% 2.36/2.53      inference('sup-', [status(thm)], ['37', '38'])).
% 2.36/2.53  thf('40', plain,
% 2.36/2.53      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_C_2))),
% 2.36/2.53      inference('sup-', [status(thm)], ['36', '39'])).
% 2.36/2.53  thf('41', plain,
% 2.36/2.53      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 2.36/2.53        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 2.36/2.53      inference('sup-', [status(thm)], ['8', '9'])).
% 2.36/2.53  thf('42', plain,
% 2.36/2.53      (((v1_xboole_0 @ sk_C_2) | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 2.36/2.53      inference('sup-', [status(thm)], ['40', '41'])).
% 2.36/2.53  thf('43', plain,
% 2.36/2.53      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 2.36/2.53        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 2.36/2.53      inference('demod', [status(thm)], ['3', '6'])).
% 2.36/2.53  thf('44', plain, (((v1_xboole_0 @ sk_C_2) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 2.36/2.53      inference('sup-', [status(thm)], ['42', '43'])).
% 2.36/2.53  thf('45', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.36/2.53      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.36/2.53  thf('46', plain,
% 2.36/2.53      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 2.36/2.53      inference('sup-', [status(thm)], ['18', '25'])).
% 2.36/2.53  thf('47', plain,
% 2.36/2.53      (![X13 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 2.36/2.53      inference('cnf', [status(esa)], [t4_subset_1])).
% 2.36/2.53  thf(cc2_relset_1, axiom,
% 2.36/2.53    (![A:$i,B:$i,C:$i]:
% 2.36/2.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.36/2.53       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.36/2.53  thf('48', plain,
% 2.36/2.53      (![X25 : $i, X26 : $i, X27 : $i]:
% 2.36/2.53         ((v4_relat_1 @ X25 @ X26)
% 2.36/2.53          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 2.36/2.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.36/2.53  thf('49', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 2.36/2.53      inference('sup-', [status(thm)], ['47', '48'])).
% 2.36/2.53  thf(d18_relat_1, axiom,
% 2.36/2.53    (![A:$i,B:$i]:
% 2.36/2.53     ( ( v1_relat_1 @ B ) =>
% 2.36/2.53       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 2.36/2.53  thf('50', plain,
% 2.36/2.53      (![X19 : $i, X20 : $i]:
% 2.36/2.53         (~ (v4_relat_1 @ X19 @ X20)
% 2.36/2.53          | (r1_tarski @ (k1_relat_1 @ X19) @ X20)
% 2.36/2.53          | ~ (v1_relat_1 @ X19))),
% 2.36/2.53      inference('cnf', [status(esa)], [d18_relat_1])).
% 2.36/2.53  thf('51', plain,
% 2.36/2.53      (![X0 : $i]:
% 2.36/2.53         (~ (v1_relat_1 @ k1_xboole_0)
% 2.36/2.53          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 2.36/2.53      inference('sup-', [status(thm)], ['49', '50'])).
% 2.36/2.53  thf(t113_zfmisc_1, axiom,
% 2.36/2.53    (![A:$i,B:$i]:
% 2.36/2.53     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 2.36/2.53       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 2.36/2.53  thf('52', plain,
% 2.36/2.53      (![X11 : $i, X12 : $i]:
% 2.36/2.53         (((k2_zfmisc_1 @ X11 @ X12) = (k1_xboole_0))
% 2.36/2.53          | ((X11) != (k1_xboole_0)))),
% 2.36/2.53      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.36/2.53  thf('53', plain,
% 2.36/2.53      (![X12 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X12) = (k1_xboole_0))),
% 2.36/2.53      inference('simplify', [status(thm)], ['52'])).
% 2.36/2.53  thf(fc6_relat_1, axiom,
% 2.36/2.53    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.36/2.53  thf('54', plain,
% 2.36/2.53      (![X21 : $i, X22 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X21 @ X22))),
% 2.36/2.53      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.36/2.53  thf('55', plain, ((v1_relat_1 @ k1_xboole_0)),
% 2.36/2.53      inference('sup+', [status(thm)], ['53', '54'])).
% 2.36/2.53  thf('56', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 2.36/2.53      inference('demod', [status(thm)], ['51', '55'])).
% 2.36/2.53  thf('57', plain,
% 2.36/2.53      (![X0 : $i, X1 : $i]:
% 2.36/2.53         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 2.36/2.53      inference('sup-', [status(thm)], ['22', '23'])).
% 2.36/2.53  thf('58', plain,
% 2.36/2.53      (![X0 : $i]: (((k1_relat_1 @ k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 2.36/2.53      inference('sup-', [status(thm)], ['56', '57'])).
% 2.36/2.53  thf('59', plain,
% 2.36/2.53      (![X0 : $i, X1 : $i]:
% 2.36/2.53         (((k1_relat_1 @ X0) = (X1))
% 2.36/2.53          | ~ (v1_xboole_0 @ X0)
% 2.36/2.53          | ~ (v1_xboole_0 @ X1))),
% 2.36/2.53      inference('sup+', [status(thm)], ['46', '58'])).
% 2.36/2.53  thf('60', plain,
% 2.36/2.53      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_relat_1 @ X0) = (k1_xboole_0)))),
% 2.36/2.53      inference('sup-', [status(thm)], ['45', '59'])).
% 2.36/2.53  thf('61', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.36/2.53      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.36/2.53  thf('62', plain,
% 2.36/2.53      (![X0 : $i]: ((v1_xboole_0 @ (k1_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 2.36/2.53      inference('sup+', [status(thm)], ['60', '61'])).
% 2.36/2.53  thf('63', plain,
% 2.36/2.53      (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_C_2) | ~ (v1_xboole_0 @ sk_D))),
% 2.36/2.53      inference('sup+', [status(thm)], ['44', '62'])).
% 2.36/2.53  thf('64', plain,
% 2.36/2.53      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 2.36/2.53      inference('sup-', [status(thm)], ['18', '25'])).
% 2.36/2.53  thf('65', plain,
% 2.36/2.53      (![X12 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X12) = (k1_xboole_0))),
% 2.36/2.53      inference('simplify', [status(thm)], ['52'])).
% 2.36/2.53  thf('66', plain,
% 2.36/2.53      (![X0 : $i, X1 : $i]:
% 2.36/2.53         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.36/2.53      inference('sup+', [status(thm)], ['64', '65'])).
% 2.36/2.53  thf('67', plain,
% 2.36/2.53      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.36/2.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.36/2.53  thf('68', plain,
% 2.36/2.53      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 2.36/2.53      inference('sup-', [status(thm)], ['18', '25'])).
% 2.36/2.53  thf('69', plain,
% 2.36/2.53      (![X11 : $i, X12 : $i]:
% 2.36/2.53         (((k2_zfmisc_1 @ X11 @ X12) = (k1_xboole_0))
% 2.36/2.53          | ((X12) != (k1_xboole_0)))),
% 2.36/2.53      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.36/2.53  thf('70', plain,
% 2.36/2.53      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 2.36/2.53      inference('simplify', [status(thm)], ['69'])).
% 2.36/2.53  thf('71', plain,
% 2.36/2.53      (![X28 : $i, X29 : $i, X30 : $i]:
% 2.36/2.53         (~ (v1_xboole_0 @ X28)
% 2.36/2.53          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X28)))
% 2.36/2.53          | (v1_xboole_0 @ X29))),
% 2.36/2.53      inference('cnf', [status(esa)], [cc4_relset_1])).
% 2.36/2.53  thf('72', plain,
% 2.36/2.53      (![X1 : $i]:
% 2.36/2.53         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.36/2.53          | (v1_xboole_0 @ X1)
% 2.36/2.53          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 2.36/2.53      inference('sup-', [status(thm)], ['70', '71'])).
% 2.36/2.53  thf('73', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.36/2.53      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.36/2.53  thf('74', plain,
% 2.36/2.53      (![X1 : $i]:
% 2.36/2.53         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.36/2.53          | (v1_xboole_0 @ X1))),
% 2.36/2.53      inference('demod', [status(thm)], ['72', '73'])).
% 2.36/2.53  thf('75', plain,
% 2.36/2.53      (![X0 : $i, X1 : $i]:
% 2.36/2.53         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 2.36/2.53          | ~ (v1_xboole_0 @ X0)
% 2.36/2.53          | (v1_xboole_0 @ X1))),
% 2.36/2.53      inference('sup-', [status(thm)], ['68', '74'])).
% 2.36/2.53  thf('76', plain,
% 2.36/2.53      (((v1_xboole_0 @ sk_C_2)
% 2.36/2.53        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.36/2.53      inference('sup-', [status(thm)], ['67', '75'])).
% 2.36/2.53  thf('77', plain,
% 2.36/2.53      ((~ (v1_xboole_0 @ k1_xboole_0)
% 2.36/2.53        | ~ (v1_xboole_0 @ sk_A)
% 2.36/2.53        | (v1_xboole_0 @ sk_C_2))),
% 2.36/2.53      inference('sup-', [status(thm)], ['66', '76'])).
% 2.36/2.53  thf('78', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.36/2.53      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.36/2.53  thf('79', plain, ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_C_2))),
% 2.36/2.53      inference('demod', [status(thm)], ['77', '78'])).
% 2.36/2.53  thf('80', plain, ((~ (v1_xboole_0 @ sk_D) | (v1_xboole_0 @ sk_C_2))),
% 2.36/2.53      inference('clc', [status(thm)], ['63', '79'])).
% 2.36/2.53  thf('81', plain, (~ (v1_xboole_0 @ sk_D)),
% 2.36/2.53      inference('clc', [status(thm)], ['35', '80'])).
% 2.36/2.53  thf('82', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0)),
% 2.36/2.53      inference('sup-', [status(thm)], ['17', '81'])).
% 2.36/2.53  thf('83', plain, ((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)),
% 2.36/2.53      inference('demod', [status(thm)], ['10', '82'])).
% 2.36/2.53  thf('84', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 2.36/2.53      inference('demod', [status(thm)], ['7', '83'])).
% 2.36/2.53  thf('85', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1)),
% 2.36/2.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.36/2.53  thf('86', plain,
% 2.36/2.53      (![X40 : $i, X41 : $i, X42 : $i]:
% 2.36/2.53         (~ (v1_funct_2 @ X42 @ X40 @ X41)
% 2.36/2.53          | ((X40) = (k1_relset_1 @ X40 @ X41 @ X42))
% 2.36/2.53          | ~ (zip_tseitin_1 @ X42 @ X41 @ X40))),
% 2.36/2.53      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.36/2.53  thf('87', plain,
% 2.36/2.53      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 2.36/2.53        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2)))),
% 2.36/2.53      inference('sup-', [status(thm)], ['85', '86'])).
% 2.36/2.53  thf('88', plain,
% 2.36/2.53      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.36/2.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.36/2.53  thf('89', plain,
% 2.36/2.53      (![X31 : $i, X32 : $i, X33 : $i]:
% 2.36/2.53         (((k1_relset_1 @ X32 @ X33 @ X31) = (k1_relat_1 @ X31))
% 2.36/2.53          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 2.36/2.53      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.36/2.53  thf('90', plain,
% 2.36/2.53      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 2.36/2.53      inference('sup-', [status(thm)], ['88', '89'])).
% 2.36/2.53  thf('91', plain,
% 2.36/2.53      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 2.36/2.53        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 2.36/2.53      inference('demod', [status(thm)], ['87', '90'])).
% 2.36/2.53  thf('92', plain,
% 2.36/2.53      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.36/2.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.36/2.53  thf('93', plain,
% 2.36/2.53      (![X43 : $i, X44 : $i, X45 : $i]:
% 2.36/2.53         (~ (zip_tseitin_0 @ X43 @ X44)
% 2.36/2.53          | (zip_tseitin_1 @ X45 @ X43 @ X44)
% 2.36/2.53          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43))))),
% 2.36/2.53      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.36/2.53  thf('94', plain,
% 2.36/2.53      (((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 2.36/2.53        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 2.36/2.53      inference('sup-', [status(thm)], ['92', '93'])).
% 2.36/2.53  thf('95', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0)),
% 2.36/2.53      inference('sup-', [status(thm)], ['17', '81'])).
% 2.36/2.53  thf('96', plain, ((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)),
% 2.36/2.53      inference('demod', [status(thm)], ['94', '95'])).
% 2.36/2.53  thf('97', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 2.36/2.53      inference('demod', [status(thm)], ['91', '96'])).
% 2.36/2.53  thf(t9_funct_1, axiom,
% 2.36/2.53    (![A:$i]:
% 2.36/2.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.36/2.53       ( ![B:$i]:
% 2.36/2.53         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.36/2.53           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 2.36/2.53               ( ![C:$i]:
% 2.36/2.53                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 2.36/2.53                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 2.36/2.53             ( ( A ) = ( B ) ) ) ) ) ))).
% 2.36/2.53  thf('98', plain,
% 2.36/2.53      (![X23 : $i, X24 : $i]:
% 2.36/2.53         (~ (v1_relat_1 @ X23)
% 2.36/2.53          | ~ (v1_funct_1 @ X23)
% 2.36/2.53          | ((X24) = (X23))
% 2.36/2.53          | (r2_hidden @ (sk_C_1 @ X23 @ X24) @ (k1_relat_1 @ X24))
% 2.36/2.53          | ((k1_relat_1 @ X24) != (k1_relat_1 @ X23))
% 2.36/2.53          | ~ (v1_funct_1 @ X24)
% 2.36/2.53          | ~ (v1_relat_1 @ X24))),
% 2.36/2.53      inference('cnf', [status(esa)], [t9_funct_1])).
% 2.36/2.53  thf('99', plain,
% 2.36/2.53      (![X0 : $i]:
% 2.36/2.53         (((sk_A) != (k1_relat_1 @ X0))
% 2.36/2.53          | ~ (v1_relat_1 @ sk_C_2)
% 2.36/2.53          | ~ (v1_funct_1 @ sk_C_2)
% 2.36/2.53          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 2.36/2.53          | ((sk_C_2) = (X0))
% 2.36/2.53          | ~ (v1_funct_1 @ X0)
% 2.36/2.53          | ~ (v1_relat_1 @ X0))),
% 2.36/2.53      inference('sup-', [status(thm)], ['97', '98'])).
% 2.36/2.53  thf('100', plain,
% 2.36/2.53      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.36/2.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.36/2.53  thf(cc2_relat_1, axiom,
% 2.36/2.53    (![A:$i]:
% 2.36/2.53     ( ( v1_relat_1 @ A ) =>
% 2.36/2.53       ( ![B:$i]:
% 2.36/2.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.36/2.53  thf('101', plain,
% 2.36/2.53      (![X17 : $i, X18 : $i]:
% 2.36/2.53         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 2.36/2.53          | (v1_relat_1 @ X17)
% 2.36/2.53          | ~ (v1_relat_1 @ X18))),
% 2.36/2.53      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.36/2.53  thf('102', plain,
% 2.36/2.53      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_C_2))),
% 2.36/2.53      inference('sup-', [status(thm)], ['100', '101'])).
% 2.36/2.53  thf('103', plain,
% 2.36/2.53      (![X21 : $i, X22 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X21 @ X22))),
% 2.36/2.53      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.36/2.53  thf('104', plain, ((v1_relat_1 @ sk_C_2)),
% 2.36/2.53      inference('demod', [status(thm)], ['102', '103'])).
% 2.36/2.53  thf('105', plain, ((v1_funct_1 @ sk_C_2)),
% 2.36/2.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.36/2.53  thf('106', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 2.36/2.53      inference('demod', [status(thm)], ['91', '96'])).
% 2.36/2.53  thf('107', plain,
% 2.36/2.53      (![X0 : $i]:
% 2.36/2.53         (((sk_A) != (k1_relat_1 @ X0))
% 2.36/2.53          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ sk_A)
% 2.36/2.53          | ((sk_C_2) = (X0))
% 2.36/2.53          | ~ (v1_funct_1 @ X0)
% 2.36/2.53          | ~ (v1_relat_1 @ X0))),
% 2.36/2.53      inference('demod', [status(thm)], ['99', '104', '105', '106'])).
% 2.36/2.53  thf('108', plain,
% 2.36/2.53      ((((sk_A) != (sk_A))
% 2.36/2.53        | ~ (v1_relat_1 @ sk_D)
% 2.36/2.53        | ~ (v1_funct_1 @ sk_D)
% 2.36/2.53        | ((sk_C_2) = (sk_D))
% 2.36/2.53        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 2.36/2.53      inference('sup-', [status(thm)], ['84', '107'])).
% 2.36/2.53  thf('109', plain,
% 2.36/2.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.36/2.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.36/2.53  thf('110', plain,
% 2.36/2.53      (![X17 : $i, X18 : $i]:
% 2.36/2.53         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 2.36/2.53          | (v1_relat_1 @ X17)
% 2.36/2.53          | ~ (v1_relat_1 @ X18))),
% 2.36/2.53      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.36/2.53  thf('111', plain,
% 2.36/2.53      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_D))),
% 2.36/2.53      inference('sup-', [status(thm)], ['109', '110'])).
% 2.36/2.53  thf('112', plain,
% 2.36/2.53      (![X21 : $i, X22 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X21 @ X22))),
% 2.36/2.53      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.36/2.53  thf('113', plain, ((v1_relat_1 @ sk_D)),
% 2.36/2.53      inference('demod', [status(thm)], ['111', '112'])).
% 2.36/2.53  thf('114', plain, ((v1_funct_1 @ sk_D)),
% 2.36/2.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.36/2.53  thf('115', plain,
% 2.36/2.53      ((((sk_A) != (sk_A))
% 2.36/2.53        | ((sk_C_2) = (sk_D))
% 2.36/2.53        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 2.36/2.53      inference('demod', [status(thm)], ['108', '113', '114'])).
% 2.36/2.53  thf('116', plain,
% 2.36/2.53      (((r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A) | ((sk_C_2) = (sk_D)))),
% 2.36/2.53      inference('simplify', [status(thm)], ['115'])).
% 2.36/2.53  thf('117', plain,
% 2.36/2.53      (![X46 : $i]:
% 2.36/2.53         (((k1_funct_1 @ sk_C_2 @ X46) = (k1_funct_1 @ sk_D @ X46))
% 2.36/2.53          | ~ (r2_hidden @ X46 @ sk_A))),
% 2.36/2.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.36/2.53  thf('118', plain,
% 2.36/2.53      ((((sk_C_2) = (sk_D))
% 2.36/2.53        | ((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 2.36/2.53            = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2))))),
% 2.36/2.53      inference('sup-', [status(thm)], ['116', '117'])).
% 2.36/2.53  thf('119', plain,
% 2.36/2.53      (((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 2.36/2.53         = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2)))),
% 2.36/2.53      inference('condensation', [status(thm)], ['118'])).
% 2.36/2.53  thf('120', plain,
% 2.36/2.53      (![X23 : $i, X24 : $i]:
% 2.36/2.53         (~ (v1_relat_1 @ X23)
% 2.36/2.53          | ~ (v1_funct_1 @ X23)
% 2.36/2.53          | ((X24) = (X23))
% 2.36/2.53          | ((k1_funct_1 @ X24 @ (sk_C_1 @ X23 @ X24))
% 2.36/2.53              != (k1_funct_1 @ X23 @ (sk_C_1 @ X23 @ X24)))
% 2.36/2.53          | ((k1_relat_1 @ X24) != (k1_relat_1 @ X23))
% 2.36/2.53          | ~ (v1_funct_1 @ X24)
% 2.36/2.53          | ~ (v1_relat_1 @ X24))),
% 2.36/2.53      inference('cnf', [status(esa)], [t9_funct_1])).
% 2.36/2.53  thf('121', plain,
% 2.36/2.53      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 2.36/2.53          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 2.36/2.53        | ~ (v1_relat_1 @ sk_C_2)
% 2.36/2.53        | ~ (v1_funct_1 @ sk_C_2)
% 2.36/2.53        | ((k1_relat_1 @ sk_C_2) != (k1_relat_1 @ sk_D))
% 2.36/2.53        | ((sk_C_2) = (sk_D))
% 2.36/2.53        | ~ (v1_funct_1 @ sk_D)
% 2.36/2.53        | ~ (v1_relat_1 @ sk_D))),
% 2.36/2.53      inference('sup-', [status(thm)], ['119', '120'])).
% 2.36/2.53  thf('122', plain, ((v1_relat_1 @ sk_C_2)),
% 2.36/2.53      inference('demod', [status(thm)], ['102', '103'])).
% 2.36/2.53  thf('123', plain, ((v1_funct_1 @ sk_C_2)),
% 2.36/2.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.36/2.53  thf('124', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 2.36/2.53      inference('demod', [status(thm)], ['91', '96'])).
% 2.36/2.53  thf('125', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 2.36/2.53      inference('demod', [status(thm)], ['7', '83'])).
% 2.36/2.53  thf('126', plain, ((v1_funct_1 @ sk_D)),
% 2.36/2.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.36/2.53  thf('127', plain, ((v1_relat_1 @ sk_D)),
% 2.36/2.53      inference('demod', [status(thm)], ['111', '112'])).
% 2.36/2.53  thf('128', plain,
% 2.36/2.53      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 2.36/2.53          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 2.36/2.53        | ((sk_A) != (sk_A))
% 2.36/2.53        | ((sk_C_2) = (sk_D)))),
% 2.36/2.53      inference('demod', [status(thm)],
% 2.36/2.53                ['121', '122', '123', '124', '125', '126', '127'])).
% 2.36/2.53  thf('129', plain, (((sk_C_2) = (sk_D))),
% 2.36/2.53      inference('simplify', [status(thm)], ['128'])).
% 2.36/2.53  thf('130', plain,
% 2.36/2.53      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.36/2.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.36/2.53  thf('131', plain,
% 2.36/2.53      (![X35 : $i, X36 : $i, X37 : $i]:
% 2.36/2.53         ((r2_relset_1 @ X35 @ X36 @ X37 @ X37)
% 2.36/2.53          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 2.36/2.53      inference('simplify', [status(thm)], ['29'])).
% 2.36/2.53  thf('132', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2)),
% 2.36/2.53      inference('sup-', [status(thm)], ['130', '131'])).
% 2.36/2.53  thf('133', plain, ($false),
% 2.36/2.53      inference('demod', [status(thm)], ['0', '129', '132'])).
% 2.36/2.53  
% 2.36/2.53  % SZS output end Refutation
% 2.36/2.53  
% 2.36/2.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
