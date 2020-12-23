%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.z2soEuP7tg

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:12 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :  242 (2720 expanded)
%              Number of leaves         :   42 ( 811 expanded)
%              Depth                    :   28
%              Number of atoms          : 1663 (25200 expanded)
%              Number of equality atoms :  150 (2031 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t9_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ B @ C )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ C )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( r1_tarski @ B @ C )
         => ( ( ( B = k1_xboole_0 )
              & ( A != k1_xboole_0 ) )
            | ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ C )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t9_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_D )
   <= ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('4',plain,(
    v1_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v5_relat_1 @ X25 @ X27 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('8',plain,(
    v5_relat_1 @ sk_D @ sk_B_1 ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('9',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v5_relat_1 @ X20 @ X21 )
      | ( r1_tarski @ ( k2_relat_1 @ X20 ) @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('12',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('13',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B_1 ),
    inference(demod,[status(thm)],['10','13'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('15',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 )
      | ~ ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['5','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t14_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) )).

thf('19',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X34 ) @ X35 )
      | ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[t14_relset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('23',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('25',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['4','23','24'])).

thf('26',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['1','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('28',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k1_relset_1 @ X32 @ X33 @ X31 )
        = ( k1_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('29',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B_1 ),
    inference(demod,[status(thm)],['10','13'])).

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

thf('31',plain,(
    ! [X38: $i,X39: $i] :
      ( ( zip_tseitin_0 @ X38 @ X39 )
      | ( X38 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('32',plain,(
    ! [X13: $i] :
      ( ( X13 = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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

thf('36',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( zip_tseitin_0 @ X43 @ X44 )
      | ( zip_tseitin_1 @ X45 @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('37',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( v1_funct_2 @ X42 @ X40 @ X41 )
      | ( X40
        = ( k1_relset_1 @ X40 @ X41 @ X42 ) )
      | ~ ( zip_tseitin_1 @ X42 @ X41 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('41',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k1_relset_1 @ X32 @ X33 @ X31 )
        = ( k1_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('44',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['41','44'])).

thf('46',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['38','45'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('47',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['38','45'])).

thf('51',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B_1 ),
    inference(demod,[status(thm)],['10','13'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('52',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('53',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k2_relat_1 @ sk_D ) )
    | ( sk_B_1
      = ( k2_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( sk_B_1
      = ( k2_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( sk_B_1
      = ( k2_relat_1 @ sk_D ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['49','54'])).

thf('56',plain,(
    ! [X38: $i,X39: $i] :
      ( ( zip_tseitin_0 @ X38 @ X39 )
      | ( X38 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('57',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('60',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['41','44'])).

thf('62',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( sk_B_1
      = ( k2_relat_1 @ sk_D ) ) ),
    inference(clc,[status(thm)],['55','62'])).

thf('64',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['46','63'])).

thf('65',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['66'])).

thf('68',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['66'])).

thf('69',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B_1 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('71',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_zfmisc_1 @ X15 @ X16 )
        = k1_xboole_0 )
      | ( X15 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('72',plain,(
    ! [X16: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X16 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['66'])).

thf('74',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['72','75'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('77',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('78',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X13: $i] :
      ( ( X13 = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('80',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_B_1 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['70','80'])).

thf('82',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( v1_funct_2 @ X42 @ X40 @ X41 )
      | ( X40
        = ( k1_relset_1 @ X40 @ X41 @ X42 ) )
      | ~ ( zip_tseitin_1 @ X42 @ X41 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('83',plain,
    ( ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ sk_B_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ sk_B_1 @ k1_xboole_0 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('85',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X17: $i,X19: $i] :
      ( ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('87',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_zfmisc_1 @ X15 @ X16 )
        = k1_xboole_0 )
      | ( X16 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('89',plain,(
    ! [X15: $i] :
      ( ( k2_zfmisc_1 @ X15 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v5_relat_1 @ X25 @ X27 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('91',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v5_relat_1 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v5_relat_1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['87','91'])).

thf('93',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v5_relat_1 @ X20 @ X21 )
      | ( r1_tarski @ ( k2_relat_1 @ X20 ) @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('94',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('96',plain,(
    ! [X15: $i] :
      ( ( k2_zfmisc_1 @ X15 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['88'])).

thf('97',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('98',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['95','98'])).

thf('100',plain,(
    r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['94','99'])).

thf('101',plain,(
    ! [X13: $i] :
      ( ( X13 = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('102',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('104',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X20 ) @ X21 )
      | ( v5_relat_1 @ X20 @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( v5_relat_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v5_relat_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['102','105'])).

thf('107',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('108',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['95','98'])).

thf('109',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v5_relat_1 @ X20 @ X21 )
      | ( r1_tarski @ ( k2_relat_1 @ X20 ) @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['95','98'])).

thf('113',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['100','101'])).

thf('114',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['111','112','113'])).

thf('115',plain,(
    ! [X17: $i,X19: $i] :
      ( ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('116',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k1_relset_1 @ X32 @ X33 @ X31 )
        = ( k1_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,
    ( ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ sk_B_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relat_1 @ k1_xboole_0 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['83','118'])).

thf('120',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['66'])).

thf('121',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('122',plain,
    ( ( ~ ( zip_tseitin_0 @ sk_B_1 @ k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X38: $i,X39: $i] :
      ( ( zip_tseitin_0 @ X38 @ X39 )
      | ( X39 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('124',plain,(
    ! [X38: $i] :
      ( zip_tseitin_0 @ X38 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('126',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['66'])).

thf('127',plain,
    ( ( zip_tseitin_1 @ k1_xboole_0 @ sk_B_1 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['122','124','125','126'])).

thf('128',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['119','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('130',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( X40
       != ( k1_relset_1 @ X40 @ X41 @ X42 ) )
      | ( v1_funct_2 @ X42 @ X40 @ X41 )
      | ~ ( zip_tseitin_1 @ X42 @ X41 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
       != ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['128','132'])).

thf('134',plain,(
    ! [X38: $i] :
      ( zip_tseitin_0 @ X38 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['123'])).

thf('135',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('136',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( zip_tseitin_0 @ X43 @ X44 )
      | ( zip_tseitin_1 @ X45 @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['134','137'])).

thf('139',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['119','127'])).

thf('140',plain,
    ( ! [X0: $i] :
        ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['133','138','139'])).

thf('141',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['66'])).

thf('142',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('143',plain,
    ( ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C_1 )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('145',plain,(
    ! [X38: $i,X39: $i] :
      ( ( zip_tseitin_0 @ X38 @ X39 )
      | ( X38 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( zip_tseitin_1 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('151',plain,(
    ! [X13: $i] :
      ( ( X13 = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('152',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('154',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('155',plain,
    ( ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C_1 )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('156',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_funct_2 @ k1_xboole_0 @ X0 @ sk_C_1 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['153','156'])).

thf('158',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_funct_2 @ X0 @ X1 @ sk_C_1 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['152','157'])).

thf('159',plain,
    ( ( ( sk_C_1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['149','158'])).

thf('160',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['119','127'])).

thf('161',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('162',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('163',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['159','160','161','162'])).

thf('164',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['143','144','163'])).

thf('165',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['140','164'])).

thf('166',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['72','75'])).

thf('167',plain,(
    ! [X16: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X16 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['71'])).

thf('168',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['66'])).

thf('169',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('170',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C_1 ) ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['167','170'])).

thf('172',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['166','171'])).

thf('173',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('174',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['66'])).

thf('175',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['4','165','172','173','174'])).

thf('176',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['67','175'])).

thf('177',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['65','176'])).

thf('178',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['29','177'])).

thf('179',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( X40
       != ( k1_relset_1 @ X40 @ X41 @ X42 ) )
      | ( v1_funct_2 @ X42 @ X40 @ X41 )
      | ~ ( zip_tseitin_1 @ X42 @ X41 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('180',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A )
    | ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['180'])).

thf('182',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('183',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( zip_tseitin_0 @ X43 @ X44 )
      | ( zip_tseitin_1 @ X45 @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('184',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,(
    ! [X38: $i,X39: $i] :
      ( ( zip_tseitin_0 @ X38 @ X39 )
      | ( X38 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('186',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['111','112','113'])).

thf('187',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['185','186'])).

thf('188',plain,(
    r1_tarski @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('190',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_C_1 @ X1 )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['187','190'])).

thf('192',plain,(
    ! [X13: $i] :
      ( ( X13 = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('193',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_C_1 @ X0 )
      | ( sk_B_1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['191','192'])).

thf('194',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['67','175'])).

thf('195',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C_1 @ X0 ) ),
    inference('simplify_reflect-',[status(thm)],['193','194'])).

thf('196',plain,(
    zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A ),
    inference(demod,[status(thm)],['184','195'])).

thf('197',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ),
    inference(demod,[status(thm)],['181','196'])).

thf('198',plain,(
    $false ),
    inference(demod,[status(thm)],['26','197'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.z2soEuP7tg
% 0.13/0.35  % Computer   : n012.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 19:37:07 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.91/1.12  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.91/1.12  % Solved by: fo/fo7.sh
% 0.91/1.12  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.12  % done 935 iterations in 0.649s
% 0.91/1.12  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.91/1.12  % SZS output start Refutation
% 0.91/1.12  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.91/1.12  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.91/1.12  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.91/1.12  thf(sk_D_type, type, sk_D: $i).
% 0.91/1.12  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.91/1.12  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.91/1.12  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.91/1.12  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.91/1.12  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.91/1.12  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.91/1.12  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.91/1.12  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.91/1.12  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.91/1.12  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.12  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.91/1.12  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.91/1.12  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.91/1.12  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.91/1.12  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.91/1.12  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.91/1.12  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.91/1.12  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.91/1.12  thf(t9_funct_2, conjecture,
% 0.91/1.12    (![A:$i,B:$i,C:$i,D:$i]:
% 0.91/1.12     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.91/1.12         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.91/1.12       ( ( r1_tarski @ B @ C ) =>
% 0.91/1.12         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.91/1.12           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.91/1.12             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 0.91/1.12  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.12    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.91/1.12        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.91/1.12            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.91/1.12          ( ( r1_tarski @ B @ C ) =>
% 0.91/1.12            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.91/1.12              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.91/1.12                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 0.91/1.12    inference('cnf.neg', [status(esa)], [t9_funct_2])).
% 0.91/1.12  thf('0', plain,
% 0.91/1.12      ((~ (v1_funct_1 @ sk_D)
% 0.91/1.12        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1)
% 0.91/1.12        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('1', plain,
% 0.91/1.12      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1))
% 0.91/1.12         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)))),
% 0.91/1.12      inference('split', [status(esa)], ['0'])).
% 0.91/1.12  thf('2', plain, ((v1_funct_1 @ sk_D)),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('3', plain, ((~ (v1_funct_1 @ sk_D)) <= (~ ((v1_funct_1 @ sk_D)))),
% 0.91/1.12      inference('split', [status(esa)], ['0'])).
% 0.91/1.12  thf('4', plain, (((v1_funct_1 @ sk_D))),
% 0.91/1.12      inference('sup-', [status(thm)], ['2', '3'])).
% 0.91/1.12  thf('5', plain, ((r1_tarski @ sk_B_1 @ sk_C_1)),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('6', plain,
% 0.91/1.12      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf(cc2_relset_1, axiom,
% 0.91/1.12    (![A:$i,B:$i,C:$i]:
% 0.91/1.12     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.91/1.12       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.91/1.12  thf('7', plain,
% 0.91/1.12      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.91/1.12         ((v5_relat_1 @ X25 @ X27)
% 0.91/1.12          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.91/1.12      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.91/1.12  thf('8', plain, ((v5_relat_1 @ sk_D @ sk_B_1)),
% 0.91/1.12      inference('sup-', [status(thm)], ['6', '7'])).
% 0.91/1.12  thf(d19_relat_1, axiom,
% 0.91/1.12    (![A:$i,B:$i]:
% 0.91/1.12     ( ( v1_relat_1 @ B ) =>
% 0.91/1.12       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.91/1.12  thf('9', plain,
% 0.91/1.12      (![X20 : $i, X21 : $i]:
% 0.91/1.12         (~ (v5_relat_1 @ X20 @ X21)
% 0.91/1.12          | (r1_tarski @ (k2_relat_1 @ X20) @ X21)
% 0.91/1.12          | ~ (v1_relat_1 @ X20))),
% 0.91/1.12      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.91/1.12  thf('10', plain,
% 0.91/1.12      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B_1))),
% 0.91/1.12      inference('sup-', [status(thm)], ['8', '9'])).
% 0.91/1.12  thf('11', plain,
% 0.91/1.12      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf(cc1_relset_1, axiom,
% 0.91/1.12    (![A:$i,B:$i,C:$i]:
% 0.91/1.12     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.91/1.12       ( v1_relat_1 @ C ) ))).
% 0.91/1.12  thf('12', plain,
% 0.91/1.12      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.91/1.12         ((v1_relat_1 @ X22)
% 0.91/1.12          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.91/1.12      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.91/1.12  thf('13', plain, ((v1_relat_1 @ sk_D)),
% 0.91/1.12      inference('sup-', [status(thm)], ['11', '12'])).
% 0.91/1.12  thf('14', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B_1)),
% 0.91/1.12      inference('demod', [status(thm)], ['10', '13'])).
% 0.91/1.12  thf(t1_xboole_1, axiom,
% 0.91/1.12    (![A:$i,B:$i,C:$i]:
% 0.91/1.12     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.91/1.12       ( r1_tarski @ A @ C ) ))).
% 0.91/1.12  thf('15', plain,
% 0.91/1.12      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.91/1.12         (~ (r1_tarski @ X10 @ X11)
% 0.91/1.12          | ~ (r1_tarski @ X11 @ X12)
% 0.91/1.12          | (r1_tarski @ X10 @ X12))),
% 0.91/1.12      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.91/1.12  thf('16', plain,
% 0.91/1.12      (![X0 : $i]:
% 0.91/1.12         ((r1_tarski @ (k2_relat_1 @ sk_D) @ X0) | ~ (r1_tarski @ sk_B_1 @ X0))),
% 0.91/1.12      inference('sup-', [status(thm)], ['14', '15'])).
% 0.91/1.12  thf('17', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C_1)),
% 0.91/1.12      inference('sup-', [status(thm)], ['5', '16'])).
% 0.91/1.12  thf('18', plain,
% 0.91/1.12      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf(t14_relset_1, axiom,
% 0.91/1.12    (![A:$i,B:$i,C:$i,D:$i]:
% 0.91/1.12     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.91/1.12       ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B ) =>
% 0.91/1.12         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ))).
% 0.91/1.12  thf('19', plain,
% 0.91/1.12      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.91/1.12         (~ (r1_tarski @ (k2_relat_1 @ X34) @ X35)
% 0.91/1.12          | (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 0.91/1.12          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 0.91/1.12      inference('cnf', [status(esa)], [t14_relset_1])).
% 0.91/1.12  thf('20', plain,
% 0.91/1.12      (![X0 : $i]:
% 0.91/1.12         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.91/1.12          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 0.91/1.12      inference('sup-', [status(thm)], ['18', '19'])).
% 0.91/1.12  thf('21', plain,
% 0.91/1.12      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.91/1.12      inference('sup-', [status(thm)], ['17', '20'])).
% 0.91/1.12  thf('22', plain,
% 0.91/1.12      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))
% 0.91/1.12         <= (~
% 0.91/1.12             ((m1_subset_1 @ sk_D @ 
% 0.91/1.12               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))))),
% 0.91/1.12      inference('split', [status(esa)], ['0'])).
% 0.91/1.12  thf('23', plain,
% 0.91/1.12      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 0.91/1.12      inference('sup-', [status(thm)], ['21', '22'])).
% 0.91/1.12  thf('24', plain,
% 0.91/1.12      (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) | 
% 0.91/1.12       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) | 
% 0.91/1.12       ~ ((v1_funct_1 @ sk_D))),
% 0.91/1.12      inference('split', [status(esa)], ['0'])).
% 0.91/1.12  thf('25', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1))),
% 0.91/1.12      inference('sat_resolution*', [status(thm)], ['4', '23', '24'])).
% 0.91/1.12  thf('26', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1)),
% 0.91/1.12      inference('simpl_trail', [status(thm)], ['1', '25'])).
% 0.91/1.12  thf('27', plain,
% 0.91/1.12      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.91/1.12      inference('sup-', [status(thm)], ['17', '20'])).
% 0.91/1.12  thf(redefinition_k1_relset_1, axiom,
% 0.91/1.12    (![A:$i,B:$i,C:$i]:
% 0.91/1.12     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.91/1.12       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.91/1.12  thf('28', plain,
% 0.91/1.12      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.91/1.12         (((k1_relset_1 @ X32 @ X33 @ X31) = (k1_relat_1 @ X31))
% 0.91/1.12          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.91/1.12      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.91/1.12  thf('29', plain,
% 0.91/1.12      (((k1_relset_1 @ sk_A @ sk_C_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.91/1.12      inference('sup-', [status(thm)], ['27', '28'])).
% 0.91/1.12  thf('30', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B_1)),
% 0.91/1.12      inference('demod', [status(thm)], ['10', '13'])).
% 0.91/1.12  thf(d1_funct_2, axiom,
% 0.91/1.12    (![A:$i,B:$i,C:$i]:
% 0.91/1.12     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.91/1.12       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.91/1.12           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.91/1.12             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.91/1.12         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.91/1.12           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.91/1.12             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.91/1.12  thf(zf_stmt_1, axiom,
% 0.91/1.12    (![B:$i,A:$i]:
% 0.91/1.12     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.91/1.12       ( zip_tseitin_0 @ B @ A ) ))).
% 0.91/1.12  thf('31', plain,
% 0.91/1.12      (![X38 : $i, X39 : $i]:
% 0.91/1.12         ((zip_tseitin_0 @ X38 @ X39) | ((X38) = (k1_xboole_0)))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.12  thf(t3_xboole_1, axiom,
% 0.91/1.12    (![A:$i]:
% 0.91/1.12     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.91/1.12  thf('32', plain,
% 0.91/1.12      (![X13 : $i]:
% 0.91/1.12         (((X13) = (k1_xboole_0)) | ~ (r1_tarski @ X13 @ k1_xboole_0))),
% 0.91/1.12      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.91/1.12  thf('33', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.12         (~ (r1_tarski @ X1 @ X0)
% 0.91/1.12          | (zip_tseitin_0 @ X0 @ X2)
% 0.91/1.12          | ((X1) = (k1_xboole_0)))),
% 0.91/1.12      inference('sup-', [status(thm)], ['31', '32'])).
% 0.91/1.12  thf('34', plain,
% 0.91/1.12      (![X0 : $i]:
% 0.91/1.12         (((k2_relat_1 @ sk_D) = (k1_xboole_0)) | (zip_tseitin_0 @ sk_B_1 @ X0))),
% 0.91/1.12      inference('sup-', [status(thm)], ['30', '33'])).
% 0.91/1.12  thf('35', plain,
% 0.91/1.12      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.91/1.12  thf(zf_stmt_3, axiom,
% 0.91/1.12    (![C:$i,B:$i,A:$i]:
% 0.91/1.12     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.91/1.12       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.91/1.12  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.91/1.12  thf(zf_stmt_5, axiom,
% 0.91/1.12    (![A:$i,B:$i,C:$i]:
% 0.91/1.12     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.91/1.12       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.91/1.12         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.91/1.12           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.91/1.12             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.91/1.12  thf('36', plain,
% 0.91/1.12      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.91/1.12         (~ (zip_tseitin_0 @ X43 @ X44)
% 0.91/1.12          | (zip_tseitin_1 @ X45 @ X43 @ X44)
% 0.91/1.12          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43))))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.91/1.12  thf('37', plain,
% 0.91/1.12      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 0.91/1.12        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.91/1.12      inference('sup-', [status(thm)], ['35', '36'])).
% 0.91/1.12  thf('38', plain,
% 0.91/1.12      ((((k2_relat_1 @ sk_D) = (k1_xboole_0))
% 0.91/1.12        | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 0.91/1.12      inference('sup-', [status(thm)], ['34', '37'])).
% 0.91/1.12  thf('39', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('40', plain,
% 0.91/1.12      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.91/1.12         (~ (v1_funct_2 @ X42 @ X40 @ X41)
% 0.91/1.12          | ((X40) = (k1_relset_1 @ X40 @ X41 @ X42))
% 0.91/1.12          | ~ (zip_tseitin_1 @ X42 @ X41 @ X40))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.91/1.12  thf('41', plain,
% 0.91/1.12      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 0.91/1.12        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 0.91/1.12      inference('sup-', [status(thm)], ['39', '40'])).
% 0.91/1.12  thf('42', plain,
% 0.91/1.12      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('43', plain,
% 0.91/1.12      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.91/1.12         (((k1_relset_1 @ X32 @ X33 @ X31) = (k1_relat_1 @ X31))
% 0.91/1.12          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.91/1.12      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.91/1.12  thf('44', plain,
% 0.91/1.12      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.91/1.12      inference('sup-', [status(thm)], ['42', '43'])).
% 0.91/1.12  thf('45', plain,
% 0.91/1.12      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 0.91/1.12        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.91/1.12      inference('demod', [status(thm)], ['41', '44'])).
% 0.91/1.12  thf('46', plain,
% 0.91/1.12      ((((k2_relat_1 @ sk_D) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.91/1.12      inference('sup-', [status(thm)], ['38', '45'])).
% 0.91/1.12  thf(d3_tarski, axiom,
% 0.91/1.12    (![A:$i,B:$i]:
% 0.91/1.12     ( ( r1_tarski @ A @ B ) <=>
% 0.91/1.12       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.91/1.12  thf('47', plain,
% 0.91/1.12      (![X4 : $i, X6 : $i]:
% 0.91/1.12         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.91/1.12      inference('cnf', [status(esa)], [d3_tarski])).
% 0.91/1.12  thf(d1_xboole_0, axiom,
% 0.91/1.12    (![A:$i]:
% 0.91/1.12     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.91/1.12  thf('48', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.91/1.12      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.91/1.12  thf('49', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.91/1.12      inference('sup-', [status(thm)], ['47', '48'])).
% 0.91/1.12  thf('50', plain,
% 0.91/1.12      ((((k2_relat_1 @ sk_D) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.91/1.12      inference('sup-', [status(thm)], ['38', '45'])).
% 0.91/1.12  thf('51', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B_1)),
% 0.91/1.12      inference('demod', [status(thm)], ['10', '13'])).
% 0.91/1.12  thf(d10_xboole_0, axiom,
% 0.91/1.12    (![A:$i,B:$i]:
% 0.91/1.12     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.91/1.12  thf('52', plain,
% 0.91/1.12      (![X7 : $i, X9 : $i]:
% 0.91/1.12         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.91/1.12      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.91/1.12  thf('53', plain,
% 0.91/1.12      ((~ (r1_tarski @ sk_B_1 @ (k2_relat_1 @ sk_D))
% 0.91/1.12        | ((sk_B_1) = (k2_relat_1 @ sk_D)))),
% 0.91/1.12      inference('sup-', [status(thm)], ['51', '52'])).
% 0.91/1.12  thf('54', plain,
% 0.91/1.12      ((~ (r1_tarski @ sk_B_1 @ k1_xboole_0)
% 0.91/1.12        | ((sk_A) = (k1_relat_1 @ sk_D))
% 0.91/1.12        | ((sk_B_1) = (k2_relat_1 @ sk_D)))),
% 0.91/1.12      inference('sup-', [status(thm)], ['50', '53'])).
% 0.91/1.12  thf('55', plain,
% 0.91/1.12      ((~ (v1_xboole_0 @ sk_B_1)
% 0.91/1.12        | ((sk_B_1) = (k2_relat_1 @ sk_D))
% 0.91/1.12        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.91/1.12      inference('sup-', [status(thm)], ['49', '54'])).
% 0.91/1.12  thf('56', plain,
% 0.91/1.12      (![X38 : $i, X39 : $i]:
% 0.91/1.12         ((zip_tseitin_0 @ X38 @ X39) | ((X38) = (k1_xboole_0)))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.12  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.91/1.12  thf('57', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.91/1.12      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.91/1.12  thf('58', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.91/1.12      inference('sup+', [status(thm)], ['56', '57'])).
% 0.91/1.12  thf('59', plain,
% 0.91/1.12      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 0.91/1.12        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.91/1.12      inference('sup-', [status(thm)], ['35', '36'])).
% 0.91/1.12  thf('60', plain,
% 0.91/1.12      (((v1_xboole_0 @ sk_B_1) | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 0.91/1.12      inference('sup-', [status(thm)], ['58', '59'])).
% 0.91/1.12  thf('61', plain,
% 0.91/1.12      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 0.91/1.12        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.91/1.12      inference('demod', [status(thm)], ['41', '44'])).
% 0.91/1.12  thf('62', plain, (((v1_xboole_0 @ sk_B_1) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.91/1.12      inference('sup-', [status(thm)], ['60', '61'])).
% 0.91/1.12  thf('63', plain,
% 0.91/1.12      ((((sk_A) = (k1_relat_1 @ sk_D)) | ((sk_B_1) = (k2_relat_1 @ sk_D)))),
% 0.91/1.12      inference('clc', [status(thm)], ['55', '62'])).
% 0.91/1.12  thf('64', plain,
% 0.91/1.12      ((((sk_B_1) = (k1_xboole_0))
% 0.91/1.12        | ((sk_A) = (k1_relat_1 @ sk_D))
% 0.91/1.12        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.91/1.12      inference('sup+', [status(thm)], ['46', '63'])).
% 0.91/1.12  thf('65', plain,
% 0.91/1.12      ((((sk_A) = (k1_relat_1 @ sk_D)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.91/1.12      inference('simplify', [status(thm)], ['64'])).
% 0.91/1.12  thf('66', plain, ((((sk_B_1) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('67', plain,
% 0.91/1.12      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.91/1.12      inference('split', [status(esa)], ['66'])).
% 0.91/1.12  thf('68', plain,
% 0.91/1.12      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.91/1.12      inference('split', [status(esa)], ['66'])).
% 0.91/1.12  thf('69', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('70', plain,
% 0.91/1.12      (((v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B_1))
% 0.91/1.12         <= ((((sk_A) = (k1_xboole_0))))),
% 0.91/1.12      inference('sup+', [status(thm)], ['68', '69'])).
% 0.91/1.12  thf(t113_zfmisc_1, axiom,
% 0.91/1.12    (![A:$i,B:$i]:
% 0.91/1.12     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.91/1.12       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.91/1.12  thf('71', plain,
% 0.91/1.12      (![X15 : $i, X16 : $i]:
% 0.91/1.12         (((k2_zfmisc_1 @ X15 @ X16) = (k1_xboole_0))
% 0.91/1.12          | ((X15) != (k1_xboole_0)))),
% 0.91/1.12      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.91/1.12  thf('72', plain,
% 0.91/1.12      (![X16 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X16) = (k1_xboole_0))),
% 0.91/1.12      inference('simplify', [status(thm)], ['71'])).
% 0.91/1.12  thf('73', plain,
% 0.91/1.12      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.91/1.12      inference('split', [status(esa)], ['66'])).
% 0.91/1.12  thf('74', plain,
% 0.91/1.12      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('75', plain,
% 0.91/1.12      (((m1_subset_1 @ sk_D @ 
% 0.91/1.12         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 0.91/1.12         <= ((((sk_A) = (k1_xboole_0))))),
% 0.91/1.12      inference('sup+', [status(thm)], ['73', '74'])).
% 0.91/1.12  thf('76', plain,
% 0.91/1.12      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.91/1.12         <= ((((sk_A) = (k1_xboole_0))))),
% 0.91/1.12      inference('sup+', [status(thm)], ['72', '75'])).
% 0.91/1.12  thf(t3_subset, axiom,
% 0.91/1.12    (![A:$i,B:$i]:
% 0.91/1.12     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.91/1.12  thf('77', plain,
% 0.91/1.12      (![X17 : $i, X18 : $i]:
% 0.91/1.12         ((r1_tarski @ X17 @ X18) | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 0.91/1.12      inference('cnf', [status(esa)], [t3_subset])).
% 0.91/1.12  thf('78', plain,
% 0.91/1.12      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.91/1.12      inference('sup-', [status(thm)], ['76', '77'])).
% 0.91/1.12  thf('79', plain,
% 0.91/1.12      (![X13 : $i]:
% 0.91/1.12         (((X13) = (k1_xboole_0)) | ~ (r1_tarski @ X13 @ k1_xboole_0))),
% 0.91/1.12      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.91/1.12  thf('80', plain,
% 0.91/1.12      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.91/1.12      inference('sup-', [status(thm)], ['78', '79'])).
% 0.91/1.12  thf('81', plain,
% 0.91/1.12      (((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_B_1))
% 0.91/1.12         <= ((((sk_A) = (k1_xboole_0))))),
% 0.91/1.12      inference('demod', [status(thm)], ['70', '80'])).
% 0.91/1.12  thf('82', plain,
% 0.91/1.12      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.91/1.12         (~ (v1_funct_2 @ X42 @ X40 @ X41)
% 0.91/1.12          | ((X40) = (k1_relset_1 @ X40 @ X41 @ X42))
% 0.91/1.12          | ~ (zip_tseitin_1 @ X42 @ X41 @ X40))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.91/1.12  thf('83', plain,
% 0.91/1.12      (((~ (zip_tseitin_1 @ k1_xboole_0 @ sk_B_1 @ k1_xboole_0)
% 0.91/1.12         | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ sk_B_1 @ k1_xboole_0))))
% 0.91/1.12         <= ((((sk_A) = (k1_xboole_0))))),
% 0.91/1.12      inference('sup-', [status(thm)], ['81', '82'])).
% 0.91/1.12  thf('84', plain,
% 0.91/1.12      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 0.91/1.12      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.91/1.12  thf('85', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 0.91/1.12      inference('simplify', [status(thm)], ['84'])).
% 0.91/1.12  thf('86', plain,
% 0.91/1.12      (![X17 : $i, X19 : $i]:
% 0.91/1.12         ((m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X19)) | ~ (r1_tarski @ X17 @ X19))),
% 0.91/1.12      inference('cnf', [status(esa)], [t3_subset])).
% 0.91/1.12  thf('87', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.91/1.12      inference('sup-', [status(thm)], ['85', '86'])).
% 0.91/1.12  thf('88', plain,
% 0.91/1.12      (![X15 : $i, X16 : $i]:
% 0.91/1.12         (((k2_zfmisc_1 @ X15 @ X16) = (k1_xboole_0))
% 0.91/1.12          | ((X16) != (k1_xboole_0)))),
% 0.91/1.12      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.91/1.12  thf('89', plain,
% 0.91/1.12      (![X15 : $i]: ((k2_zfmisc_1 @ X15 @ k1_xboole_0) = (k1_xboole_0))),
% 0.91/1.12      inference('simplify', [status(thm)], ['88'])).
% 0.91/1.12  thf('90', plain,
% 0.91/1.12      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.91/1.12         ((v5_relat_1 @ X25 @ X27)
% 0.91/1.12          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.91/1.12      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.91/1.12  thf('91', plain,
% 0.91/1.12      (![X1 : $i]:
% 0.91/1.12         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.91/1.12          | (v5_relat_1 @ X1 @ k1_xboole_0))),
% 0.91/1.12      inference('sup-', [status(thm)], ['89', '90'])).
% 0.91/1.12  thf('92', plain, ((v5_relat_1 @ k1_xboole_0 @ k1_xboole_0)),
% 0.91/1.12      inference('sup-', [status(thm)], ['87', '91'])).
% 0.91/1.12  thf('93', plain,
% 0.91/1.12      (![X20 : $i, X21 : $i]:
% 0.91/1.12         (~ (v5_relat_1 @ X20 @ X21)
% 0.91/1.12          | (r1_tarski @ (k2_relat_1 @ X20) @ X21)
% 0.91/1.12          | ~ (v1_relat_1 @ X20))),
% 0.91/1.12      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.91/1.12  thf('94', plain,
% 0.91/1.12      ((~ (v1_relat_1 @ k1_xboole_0)
% 0.91/1.12        | (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ k1_xboole_0))),
% 0.91/1.12      inference('sup-', [status(thm)], ['92', '93'])).
% 0.91/1.12  thf('95', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.91/1.12      inference('sup-', [status(thm)], ['85', '86'])).
% 0.91/1.12  thf('96', plain,
% 0.91/1.12      (![X15 : $i]: ((k2_zfmisc_1 @ X15 @ k1_xboole_0) = (k1_xboole_0))),
% 0.91/1.12      inference('simplify', [status(thm)], ['88'])).
% 0.91/1.12  thf('97', plain,
% 0.91/1.12      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.91/1.12         ((v1_relat_1 @ X22)
% 0.91/1.12          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.91/1.12      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.91/1.12  thf('98', plain,
% 0.91/1.12      (![X1 : $i]:
% 0.91/1.12         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.91/1.12          | (v1_relat_1 @ X1))),
% 0.91/1.12      inference('sup-', [status(thm)], ['96', '97'])).
% 0.91/1.12  thf('99', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.91/1.12      inference('sup-', [status(thm)], ['95', '98'])).
% 0.91/1.12  thf('100', plain, ((r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ k1_xboole_0)),
% 0.91/1.12      inference('demod', [status(thm)], ['94', '99'])).
% 0.91/1.12  thf('101', plain,
% 0.91/1.12      (![X13 : $i]:
% 0.91/1.12         (((X13) = (k1_xboole_0)) | ~ (r1_tarski @ X13 @ k1_xboole_0))),
% 0.91/1.12      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.91/1.12  thf('102', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.91/1.12      inference('sup-', [status(thm)], ['100', '101'])).
% 0.91/1.12  thf('103', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.91/1.12      inference('sup-', [status(thm)], ['47', '48'])).
% 0.91/1.12  thf('104', plain,
% 0.91/1.12      (![X20 : $i, X21 : $i]:
% 0.91/1.12         (~ (r1_tarski @ (k2_relat_1 @ X20) @ X21)
% 0.91/1.12          | (v5_relat_1 @ X20 @ X21)
% 0.91/1.12          | ~ (v1_relat_1 @ X20))),
% 0.91/1.12      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.91/1.12  thf('105', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]:
% 0.91/1.12         (~ (v1_xboole_0 @ (k2_relat_1 @ X1))
% 0.91/1.12          | ~ (v1_relat_1 @ X1)
% 0.91/1.12          | (v5_relat_1 @ X1 @ X0))),
% 0.91/1.12      inference('sup-', [status(thm)], ['103', '104'])).
% 0.91/1.12  thf('106', plain,
% 0.91/1.12      (![X0 : $i]:
% 0.91/1.12         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.91/1.12          | (v5_relat_1 @ k1_xboole_0 @ X0)
% 0.91/1.12          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.91/1.12      inference('sup-', [status(thm)], ['102', '105'])).
% 0.91/1.12  thf('107', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.91/1.12      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.91/1.12  thf('108', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.91/1.12      inference('sup-', [status(thm)], ['95', '98'])).
% 0.91/1.12  thf('109', plain, (![X0 : $i]: (v5_relat_1 @ k1_xboole_0 @ X0)),
% 0.91/1.12      inference('demod', [status(thm)], ['106', '107', '108'])).
% 0.91/1.12  thf('110', plain,
% 0.91/1.12      (![X20 : $i, X21 : $i]:
% 0.91/1.12         (~ (v5_relat_1 @ X20 @ X21)
% 0.91/1.12          | (r1_tarski @ (k2_relat_1 @ X20) @ X21)
% 0.91/1.12          | ~ (v1_relat_1 @ X20))),
% 0.91/1.12      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.91/1.12  thf('111', plain,
% 0.91/1.12      (![X0 : $i]:
% 0.91/1.12         (~ (v1_relat_1 @ k1_xboole_0)
% 0.91/1.12          | (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0))),
% 0.91/1.12      inference('sup-', [status(thm)], ['109', '110'])).
% 0.91/1.12  thf('112', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.91/1.12      inference('sup-', [status(thm)], ['95', '98'])).
% 0.91/1.12  thf('113', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.91/1.12      inference('sup-', [status(thm)], ['100', '101'])).
% 0.91/1.12  thf('114', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.91/1.12      inference('demod', [status(thm)], ['111', '112', '113'])).
% 0.91/1.12  thf('115', plain,
% 0.91/1.12      (![X17 : $i, X19 : $i]:
% 0.91/1.12         ((m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X19)) | ~ (r1_tarski @ X17 @ X19))),
% 0.91/1.12      inference('cnf', [status(esa)], [t3_subset])).
% 0.91/1.12  thf('116', plain,
% 0.91/1.12      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.91/1.12      inference('sup-', [status(thm)], ['114', '115'])).
% 0.91/1.12  thf('117', plain,
% 0.91/1.12      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.91/1.12         (((k1_relset_1 @ X32 @ X33 @ X31) = (k1_relat_1 @ X31))
% 0.91/1.12          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.91/1.12      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.91/1.12  thf('118', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]:
% 0.91/1.12         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.91/1.12      inference('sup-', [status(thm)], ['116', '117'])).
% 0.91/1.12  thf('119', plain,
% 0.91/1.12      (((~ (zip_tseitin_1 @ k1_xboole_0 @ sk_B_1 @ k1_xboole_0)
% 0.91/1.12         | ((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))))
% 0.91/1.12         <= ((((sk_A) = (k1_xboole_0))))),
% 0.91/1.12      inference('demod', [status(thm)], ['83', '118'])).
% 0.91/1.12  thf('120', plain,
% 0.91/1.12      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.91/1.12      inference('split', [status(esa)], ['66'])).
% 0.91/1.12  thf('121', plain,
% 0.91/1.12      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 0.91/1.12        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.91/1.12      inference('sup-', [status(thm)], ['35', '36'])).
% 0.91/1.12  thf('122', plain,
% 0.91/1.12      (((~ (zip_tseitin_0 @ sk_B_1 @ k1_xboole_0)
% 0.91/1.12         | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)))
% 0.91/1.12         <= ((((sk_A) = (k1_xboole_0))))),
% 0.91/1.12      inference('sup-', [status(thm)], ['120', '121'])).
% 0.91/1.12  thf('123', plain,
% 0.91/1.12      (![X38 : $i, X39 : $i]:
% 0.91/1.12         ((zip_tseitin_0 @ X38 @ X39) | ((X39) != (k1_xboole_0)))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.12  thf('124', plain, (![X38 : $i]: (zip_tseitin_0 @ X38 @ k1_xboole_0)),
% 0.91/1.12      inference('simplify', [status(thm)], ['123'])).
% 0.91/1.12  thf('125', plain,
% 0.91/1.12      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.91/1.12      inference('sup-', [status(thm)], ['78', '79'])).
% 0.91/1.12  thf('126', plain,
% 0.91/1.12      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.91/1.12      inference('split', [status(esa)], ['66'])).
% 0.91/1.12  thf('127', plain,
% 0.91/1.12      (((zip_tseitin_1 @ k1_xboole_0 @ sk_B_1 @ k1_xboole_0))
% 0.91/1.12         <= ((((sk_A) = (k1_xboole_0))))),
% 0.91/1.12      inference('demod', [status(thm)], ['122', '124', '125', '126'])).
% 0.91/1.12  thf('128', plain,
% 0.91/1.12      ((((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0)))
% 0.91/1.12         <= ((((sk_A) = (k1_xboole_0))))),
% 0.91/1.12      inference('demod', [status(thm)], ['119', '127'])).
% 0.91/1.12  thf('129', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]:
% 0.91/1.12         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.91/1.12      inference('sup-', [status(thm)], ['116', '117'])).
% 0.91/1.12  thf('130', plain,
% 0.91/1.12      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.91/1.12         (((X40) != (k1_relset_1 @ X40 @ X41 @ X42))
% 0.91/1.12          | (v1_funct_2 @ X42 @ X40 @ X41)
% 0.91/1.12          | ~ (zip_tseitin_1 @ X42 @ X41 @ X40))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.91/1.12  thf('131', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]:
% 0.91/1.12         (((X1) != (k1_relat_1 @ k1_xboole_0))
% 0.91/1.12          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 0.91/1.12          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 0.91/1.12      inference('sup-', [status(thm)], ['129', '130'])).
% 0.91/1.12  thf('132', plain,
% 0.91/1.12      (![X0 : $i]:
% 0.91/1.12         ((v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ X0)
% 0.91/1.12          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ (k1_relat_1 @ k1_xboole_0)))),
% 0.91/1.12      inference('simplify', [status(thm)], ['131'])).
% 0.91/1.12  thf('133', plain,
% 0.91/1.12      ((![X0 : $i]:
% 0.91/1.12          (~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)
% 0.91/1.12           | (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ X0)))
% 0.91/1.12         <= ((((sk_A) = (k1_xboole_0))))),
% 0.91/1.12      inference('sup-', [status(thm)], ['128', '132'])).
% 0.91/1.12  thf('134', plain, (![X38 : $i]: (zip_tseitin_0 @ X38 @ k1_xboole_0)),
% 0.91/1.12      inference('simplify', [status(thm)], ['123'])).
% 0.91/1.12  thf('135', plain,
% 0.91/1.12      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.91/1.12      inference('sup-', [status(thm)], ['114', '115'])).
% 0.91/1.12  thf('136', plain,
% 0.91/1.12      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.91/1.12         (~ (zip_tseitin_0 @ X43 @ X44)
% 0.91/1.12          | (zip_tseitin_1 @ X45 @ X43 @ X44)
% 0.91/1.12          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43))))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.91/1.12  thf('137', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]:
% 0.91/1.12         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 0.91/1.12      inference('sup-', [status(thm)], ['135', '136'])).
% 0.91/1.12  thf('138', plain,
% 0.91/1.12      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.91/1.12      inference('sup-', [status(thm)], ['134', '137'])).
% 0.91/1.12  thf('139', plain,
% 0.91/1.12      ((((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0)))
% 0.91/1.12         <= ((((sk_A) = (k1_xboole_0))))),
% 0.91/1.12      inference('demod', [status(thm)], ['119', '127'])).
% 0.91/1.12  thf('140', plain,
% 0.91/1.12      ((![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0))
% 0.91/1.12         <= ((((sk_A) = (k1_xboole_0))))),
% 0.91/1.12      inference('demod', [status(thm)], ['133', '138', '139'])).
% 0.91/1.12  thf('141', plain,
% 0.91/1.12      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.91/1.12      inference('split', [status(esa)], ['66'])).
% 0.91/1.12  thf('142', plain,
% 0.91/1.12      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1))
% 0.91/1.12         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)))),
% 0.91/1.12      inference('split', [status(esa)], ['0'])).
% 0.91/1.12  thf('143', plain,
% 0.91/1.12      ((~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C_1))
% 0.91/1.12         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) & 
% 0.91/1.12             (((sk_A) = (k1_xboole_0))))),
% 0.91/1.12      inference('sup-', [status(thm)], ['141', '142'])).
% 0.91/1.12  thf('144', plain,
% 0.91/1.12      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.91/1.12      inference('sup-', [status(thm)], ['78', '79'])).
% 0.91/1.12  thf('145', plain,
% 0.91/1.12      (![X38 : $i, X39 : $i]:
% 0.91/1.12         ((zip_tseitin_0 @ X38 @ X39) | ((X38) = (k1_xboole_0)))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.12  thf('146', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]:
% 0.91/1.12         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 0.91/1.12      inference('sup-', [status(thm)], ['135', '136'])).
% 0.91/1.12  thf('147', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]:
% 0.91/1.12         (((X1) = (k1_xboole_0)) | (zip_tseitin_1 @ k1_xboole_0 @ X1 @ X0))),
% 0.91/1.12      inference('sup-', [status(thm)], ['145', '146'])).
% 0.91/1.12  thf('148', plain,
% 0.91/1.12      (![X0 : $i]:
% 0.91/1.12         ((v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ X0)
% 0.91/1.12          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ (k1_relat_1 @ k1_xboole_0)))),
% 0.91/1.12      inference('simplify', [status(thm)], ['131'])).
% 0.91/1.12  thf('149', plain,
% 0.91/1.12      (![X0 : $i]:
% 0.91/1.12         (((X0) = (k1_xboole_0))
% 0.91/1.12          | (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 0.91/1.12      inference('sup-', [status(thm)], ['147', '148'])).
% 0.91/1.12  thf('150', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.91/1.12      inference('sup-', [status(thm)], ['47', '48'])).
% 0.91/1.12  thf('151', plain,
% 0.91/1.12      (![X13 : $i]:
% 0.91/1.12         (((X13) = (k1_xboole_0)) | ~ (r1_tarski @ X13 @ k1_xboole_0))),
% 0.91/1.12      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.91/1.12  thf('152', plain,
% 0.91/1.12      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.91/1.12      inference('sup-', [status(thm)], ['150', '151'])).
% 0.91/1.12  thf('153', plain,
% 0.91/1.12      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.91/1.12      inference('sup-', [status(thm)], ['150', '151'])).
% 0.91/1.12  thf('154', plain,
% 0.91/1.12      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.91/1.12      inference('sup-', [status(thm)], ['78', '79'])).
% 0.91/1.12  thf('155', plain,
% 0.91/1.12      ((~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C_1))
% 0.91/1.12         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) & 
% 0.91/1.12             (((sk_A) = (k1_xboole_0))))),
% 0.91/1.12      inference('sup-', [status(thm)], ['141', '142'])).
% 0.91/1.12  thf('156', plain,
% 0.91/1.12      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1))
% 0.91/1.12         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) & 
% 0.91/1.12             (((sk_A) = (k1_xboole_0))))),
% 0.91/1.12      inference('sup-', [status(thm)], ['154', '155'])).
% 0.91/1.12  thf('157', plain,
% 0.91/1.12      ((![X0 : $i]:
% 0.91/1.12          (~ (v1_funct_2 @ k1_xboole_0 @ X0 @ sk_C_1) | ~ (v1_xboole_0 @ X0)))
% 0.91/1.12         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) & 
% 0.91/1.12             (((sk_A) = (k1_xboole_0))))),
% 0.91/1.12      inference('sup-', [status(thm)], ['153', '156'])).
% 0.91/1.12  thf('158', plain,
% 0.91/1.12      ((![X0 : $i, X1 : $i]:
% 0.91/1.12          (~ (v1_funct_2 @ X0 @ X1 @ sk_C_1)
% 0.91/1.12           | ~ (v1_xboole_0 @ X0)
% 0.91/1.12           | ~ (v1_xboole_0 @ X1)))
% 0.91/1.12         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) & 
% 0.91/1.12             (((sk_A) = (k1_xboole_0))))),
% 0.91/1.12      inference('sup-', [status(thm)], ['152', '157'])).
% 0.91/1.12  thf('159', plain,
% 0.91/1.12      (((((sk_C_1) = (k1_xboole_0))
% 0.91/1.12         | ~ (v1_xboole_0 @ (k1_relat_1 @ k1_xboole_0))
% 0.91/1.12         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.91/1.12         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) & 
% 0.91/1.12             (((sk_A) = (k1_xboole_0))))),
% 0.91/1.12      inference('sup-', [status(thm)], ['149', '158'])).
% 0.91/1.12  thf('160', plain,
% 0.91/1.12      ((((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0)))
% 0.91/1.12         <= ((((sk_A) = (k1_xboole_0))))),
% 0.91/1.12      inference('demod', [status(thm)], ['119', '127'])).
% 0.91/1.12  thf('161', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.91/1.12      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.91/1.12  thf('162', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.91/1.12      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.91/1.12  thf('163', plain,
% 0.91/1.12      ((((sk_C_1) = (k1_xboole_0)))
% 0.91/1.12         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) & 
% 0.91/1.12             (((sk_A) = (k1_xboole_0))))),
% 0.91/1.12      inference('demod', [status(thm)], ['159', '160', '161', '162'])).
% 0.91/1.12  thf('164', plain,
% 0.91/1.12      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))
% 0.91/1.12         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) & 
% 0.91/1.12             (((sk_A) = (k1_xboole_0))))),
% 0.91/1.12      inference('demod', [status(thm)], ['143', '144', '163'])).
% 0.91/1.12  thf('165', plain,
% 0.91/1.12      (((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) | ~ (((sk_A) = (k1_xboole_0)))),
% 0.91/1.12      inference('sup-', [status(thm)], ['140', '164'])).
% 0.91/1.12  thf('166', plain,
% 0.91/1.12      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.91/1.12         <= ((((sk_A) = (k1_xboole_0))))),
% 0.91/1.12      inference('sup+', [status(thm)], ['72', '75'])).
% 0.91/1.12  thf('167', plain,
% 0.91/1.12      (![X16 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X16) = (k1_xboole_0))),
% 0.91/1.12      inference('simplify', [status(thm)], ['71'])).
% 0.91/1.12  thf('168', plain,
% 0.91/1.12      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.91/1.12      inference('split', [status(esa)], ['66'])).
% 0.91/1.12  thf('169', plain,
% 0.91/1.12      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))
% 0.91/1.12         <= (~
% 0.91/1.12             ((m1_subset_1 @ sk_D @ 
% 0.91/1.12               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))))),
% 0.91/1.12      inference('split', [status(esa)], ['0'])).
% 0.91/1.12  thf('170', plain,
% 0.91/1.12      ((~ (m1_subset_1 @ sk_D @ 
% 0.91/1.12           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C_1))))
% 0.91/1.12         <= (~
% 0.91/1.12             ((m1_subset_1 @ sk_D @ 
% 0.91/1.12               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) & 
% 0.91/1.12             (((sk_A) = (k1_xboole_0))))),
% 0.91/1.12      inference('sup-', [status(thm)], ['168', '169'])).
% 0.91/1.12  thf('171', plain,
% 0.91/1.12      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.91/1.12         <= (~
% 0.91/1.12             ((m1_subset_1 @ sk_D @ 
% 0.91/1.12               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) & 
% 0.91/1.12             (((sk_A) = (k1_xboole_0))))),
% 0.91/1.12      inference('sup-', [status(thm)], ['167', '170'])).
% 0.91/1.12  thf('172', plain,
% 0.91/1.12      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.91/1.12       ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 0.91/1.12      inference('sup-', [status(thm)], ['166', '171'])).
% 0.91/1.12  thf('173', plain,
% 0.91/1.12      (~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) | 
% 0.91/1.12       ~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) | ~ ((v1_funct_1 @ sk_D))),
% 0.91/1.12      inference('split', [status(esa)], ['0'])).
% 0.91/1.12  thf('174', plain,
% 0.91/1.12      (~ (((sk_B_1) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.91/1.12      inference('split', [status(esa)], ['66'])).
% 0.91/1.12  thf('175', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 0.91/1.12      inference('sat_resolution*', [status(thm)],
% 0.91/1.12                ['4', '165', '172', '173', '174'])).
% 0.91/1.12  thf('176', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.91/1.12      inference('simpl_trail', [status(thm)], ['67', '175'])).
% 0.91/1.12  thf('177', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.91/1.12      inference('simplify_reflect-', [status(thm)], ['65', '176'])).
% 0.91/1.12  thf('178', plain, (((k1_relset_1 @ sk_A @ sk_C_1 @ sk_D) = (sk_A))),
% 0.91/1.12      inference('demod', [status(thm)], ['29', '177'])).
% 0.91/1.12  thf('179', plain,
% 0.91/1.12      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.91/1.12         (((X40) != (k1_relset_1 @ X40 @ X41 @ X42))
% 0.91/1.12          | (v1_funct_2 @ X42 @ X40 @ X41)
% 0.91/1.12          | ~ (zip_tseitin_1 @ X42 @ X41 @ X40))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.91/1.12  thf('180', plain,
% 0.91/1.12      ((((sk_A) != (sk_A))
% 0.91/1.12        | ~ (zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A)
% 0.91/1.12        | (v1_funct_2 @ sk_D @ sk_A @ sk_C_1))),
% 0.91/1.12      inference('sup-', [status(thm)], ['178', '179'])).
% 0.91/1.12  thf('181', plain,
% 0.91/1.12      (((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)
% 0.91/1.12        | ~ (zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A))),
% 0.91/1.12      inference('simplify', [status(thm)], ['180'])).
% 0.91/1.12  thf('182', plain,
% 0.91/1.12      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.91/1.12      inference('sup-', [status(thm)], ['17', '20'])).
% 0.91/1.12  thf('183', plain,
% 0.91/1.12      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.91/1.12         (~ (zip_tseitin_0 @ X43 @ X44)
% 0.91/1.12          | (zip_tseitin_1 @ X45 @ X43 @ X44)
% 0.91/1.12          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43))))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.91/1.12  thf('184', plain,
% 0.91/1.12      (((zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A)
% 0.91/1.12        | ~ (zip_tseitin_0 @ sk_C_1 @ sk_A))),
% 0.91/1.12      inference('sup-', [status(thm)], ['182', '183'])).
% 0.91/1.12  thf('185', plain,
% 0.91/1.12      (![X38 : $i, X39 : $i]:
% 0.91/1.12         ((zip_tseitin_0 @ X38 @ X39) | ((X38) = (k1_xboole_0)))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.12  thf('186', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.91/1.12      inference('demod', [status(thm)], ['111', '112', '113'])).
% 0.91/1.12  thf('187', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.12         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 0.91/1.12      inference('sup+', [status(thm)], ['185', '186'])).
% 0.91/1.12  thf('188', plain, ((r1_tarski @ sk_B_1 @ sk_C_1)),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('189', plain,
% 0.91/1.12      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.91/1.12         (~ (r1_tarski @ X10 @ X11)
% 0.91/1.12          | ~ (r1_tarski @ X11 @ X12)
% 0.91/1.12          | (r1_tarski @ X10 @ X12))),
% 0.91/1.12      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.91/1.12  thf('190', plain,
% 0.91/1.12      (![X0 : $i]: ((r1_tarski @ sk_B_1 @ X0) | ~ (r1_tarski @ sk_C_1 @ X0))),
% 0.91/1.12      inference('sup-', [status(thm)], ['188', '189'])).
% 0.91/1.12  thf('191', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]:
% 0.91/1.12         ((zip_tseitin_0 @ sk_C_1 @ X1) | (r1_tarski @ sk_B_1 @ X0))),
% 0.91/1.12      inference('sup-', [status(thm)], ['187', '190'])).
% 0.91/1.12  thf('192', plain,
% 0.91/1.12      (![X13 : $i]:
% 0.91/1.12         (((X13) = (k1_xboole_0)) | ~ (r1_tarski @ X13 @ k1_xboole_0))),
% 0.91/1.12      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.91/1.12  thf('193', plain,
% 0.91/1.12      (![X0 : $i]: ((zip_tseitin_0 @ sk_C_1 @ X0) | ((sk_B_1) = (k1_xboole_0)))),
% 0.91/1.12      inference('sup-', [status(thm)], ['191', '192'])).
% 0.91/1.12  thf('194', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.91/1.12      inference('simpl_trail', [status(thm)], ['67', '175'])).
% 0.91/1.12  thf('195', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C_1 @ X0)),
% 0.91/1.12      inference('simplify_reflect-', [status(thm)], ['193', '194'])).
% 0.91/1.12  thf('196', plain, ((zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A)),
% 0.91/1.12      inference('demod', [status(thm)], ['184', '195'])).
% 0.91/1.12  thf('197', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)),
% 0.91/1.12      inference('demod', [status(thm)], ['181', '196'])).
% 0.91/1.12  thf('198', plain, ($false), inference('demod', [status(thm)], ['26', '197'])).
% 0.91/1.12  
% 0.91/1.12  % SZS output end Refutation
% 0.91/1.12  
% 0.96/1.13  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
