%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.M8gPqVI9mU

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:12 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 605 expanded)
%              Number of leaves         :   34 ( 182 expanded)
%              Depth                    :   19
%              Number of atoms          :  949 (8804 expanded)
%              Number of equality atoms :   76 ( 550 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
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

thf('5',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ( X21
        = ( k1_relset_1 @ X21 @ X22 @ X23 ) )
      | ~ ( zip_tseitin_1 @ X23 @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('10',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['5'])).

thf('12',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('14',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('15',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D )
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relat_1 @ sk_D ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('17',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

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

thf('18',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( zip_tseitin_0 @ X24 @ X25 )
      | ( zip_tseitin_1 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('19',plain,
    ( ( ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ sk_B @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 )
      | ( X20 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('21',plain,(
    ! [X19: $i] :
      ( zip_tseitin_0 @ X19 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','21'])).

thf('23',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','22'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('24',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('25',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('26',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v5_relat_1 @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('27',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['25','26'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('28',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v5_relat_1 @ X8 @ X9 )
      | ( r1_tarski @ ( k2_relat_1 @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('31',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('32',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_D ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','35'])).

thf('37',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_D ) ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('42',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C_1 ),
    inference(simplify,[status(thm)],['42'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('44',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X27 ) @ X28 )
      | ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X27 ) @ X28 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['30','31'])).

thf('47',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','48'])).

thf('50',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['5'])).

thf('51',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('52',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C_1 ) ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','22'])).

thf('55',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C_1 ),
    inference(simplify,[status(thm)],['42'])).

thf('56',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X27 ) @ X28 )
      | ( v1_funct_2 @ X27 @ ( k1_relat_1 @ X27 ) @ X28 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('57',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['30','31'])).

thf('59',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ sk_C_1 ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C_1 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['54','60'])).

thf('62',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['5'])).

thf('63',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('64',plain,
    ( ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C_1 )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['5'])).

thf('67',plain,(
    ! [X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('68',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( zip_tseitin_0 @ X24 @ X25 )
      | ( zip_tseitin_1 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('70',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf('72',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ( X21
        = ( k1_relset_1 @ X21 @ X22 @ X23 ) )
      | ~ ( zip_tseitin_1 @ X23 @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('74',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('77',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['74','77'])).

thf('79',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['71','78'])).

thf('80',plain,(
    v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ sk_C_1 ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('81',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('83',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['5'])).

thf('85',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( sk_B != k1_xboole_0 )
      & ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('88',plain,(
    ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['4','53','65','66','86','87'])).

thf('89',plain,(
    ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','88'])).

thf('90',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['71','78'])).

thf('91',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('92',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['5'])).

thf('94',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['4','53','65','87','66'])).

thf('95',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['93','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['92','95'])).

thf('97',plain,(
    $false ),
    inference(demod,[status(thm)],['89','96'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.M8gPqVI9mU
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:34:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.59/0.84  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.84  % Solved by: fo/fo7.sh
% 0.59/0.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.84  % done 419 iterations in 0.407s
% 0.59/0.84  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.84  % SZS output start Refutation
% 0.59/0.84  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.59/0.84  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.84  thf(sk_D_type, type, sk_D: $i).
% 0.59/0.84  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.59/0.84  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.59/0.84  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.59/0.84  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.84  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.84  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.59/0.84  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.59/0.84  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.59/0.84  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.59/0.84  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.59/0.84  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.59/0.84  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.84  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.84  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.59/0.84  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.59/0.84  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.59/0.84  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.59/0.84  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.59/0.84  thf(t9_funct_2, conjecture,
% 0.59/0.84    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.84     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.59/0.84         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.59/0.84       ( ( r1_tarski @ B @ C ) =>
% 0.59/0.84         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.59/0.84           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.59/0.84             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 0.59/0.84  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.84    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.84        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.59/0.84            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.59/0.84          ( ( r1_tarski @ B @ C ) =>
% 0.59/0.84            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.59/0.84              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.59/0.84                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 0.59/0.84    inference('cnf.neg', [status(esa)], [t9_funct_2])).
% 0.59/0.84  thf('0', plain,
% 0.59/0.84      ((~ (v1_funct_1 @ sk_D)
% 0.59/0.84        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1)
% 0.59/0.84        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 0.59/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.84  thf('1', plain,
% 0.59/0.84      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))
% 0.59/0.84         <= (~
% 0.59/0.84             ((m1_subset_1 @ sk_D @ 
% 0.59/0.84               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))))),
% 0.59/0.84      inference('split', [status(esa)], ['0'])).
% 0.59/0.84  thf('2', plain, ((v1_funct_1 @ sk_D)),
% 0.59/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.84  thf('3', plain, ((~ (v1_funct_1 @ sk_D)) <= (~ ((v1_funct_1 @ sk_D)))),
% 0.59/0.84      inference('split', [status(esa)], ['0'])).
% 0.59/0.84  thf('4', plain, (((v1_funct_1 @ sk_D))),
% 0.59/0.84      inference('sup-', [status(thm)], ['2', '3'])).
% 0.59/0.84  thf('5', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.59/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.84  thf('6', plain, ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.59/0.84      inference('split', [status(esa)], ['5'])).
% 0.59/0.84  thf('7', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.59/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.84  thf('8', plain,
% 0.59/0.84      (((v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B))
% 0.59/0.84         <= ((((sk_A) = (k1_xboole_0))))),
% 0.59/0.84      inference('sup+', [status(thm)], ['6', '7'])).
% 0.59/0.84  thf(d1_funct_2, axiom,
% 0.59/0.84    (![A:$i,B:$i,C:$i]:
% 0.59/0.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.84       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.59/0.84           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.59/0.84             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.59/0.84         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.59/0.84           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.59/0.84             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.59/0.84  thf(zf_stmt_1, axiom,
% 0.59/0.84    (![C:$i,B:$i,A:$i]:
% 0.59/0.84     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.59/0.84       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.59/0.84  thf('9', plain,
% 0.59/0.84      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.59/0.84         (~ (v1_funct_2 @ X23 @ X21 @ X22)
% 0.59/0.84          | ((X21) = (k1_relset_1 @ X21 @ X22 @ X23))
% 0.59/0.84          | ~ (zip_tseitin_1 @ X23 @ X22 @ X21))),
% 0.59/0.84      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.59/0.84  thf('10', plain,
% 0.59/0.84      (((~ (zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 0.59/0.84         | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D))))
% 0.59/0.84         <= ((((sk_A) = (k1_xboole_0))))),
% 0.59/0.84      inference('sup-', [status(thm)], ['8', '9'])).
% 0.59/0.84  thf('11', plain,
% 0.59/0.84      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.59/0.84      inference('split', [status(esa)], ['5'])).
% 0.59/0.84  thf('12', plain,
% 0.59/0.84      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.59/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.84  thf('13', plain,
% 0.59/0.84      (((m1_subset_1 @ sk_D @ 
% 0.59/0.84         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.59/0.84         <= ((((sk_A) = (k1_xboole_0))))),
% 0.59/0.84      inference('sup+', [status(thm)], ['11', '12'])).
% 0.59/0.84  thf(redefinition_k1_relset_1, axiom,
% 0.59/0.84    (![A:$i,B:$i,C:$i]:
% 0.59/0.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.84       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.59/0.84  thf('14', plain,
% 0.59/0.84      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.59/0.84         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 0.59/0.84          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.59/0.84      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.59/0.84  thf('15', plain,
% 0.59/0.84      ((((k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D) = (k1_relat_1 @ sk_D)))
% 0.59/0.84         <= ((((sk_A) = (k1_xboole_0))))),
% 0.59/0.84      inference('sup-', [status(thm)], ['13', '14'])).
% 0.59/0.84  thf('16', plain,
% 0.59/0.84      (((~ (zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 0.59/0.84         | ((k1_xboole_0) = (k1_relat_1 @ sk_D))))
% 0.59/0.84         <= ((((sk_A) = (k1_xboole_0))))),
% 0.59/0.84      inference('demod', [status(thm)], ['10', '15'])).
% 0.59/0.84  thf('17', plain,
% 0.59/0.84      (((m1_subset_1 @ sk_D @ 
% 0.59/0.84         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.59/0.84         <= ((((sk_A) = (k1_xboole_0))))),
% 0.59/0.84      inference('sup+', [status(thm)], ['11', '12'])).
% 0.59/0.84  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.59/0.84  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.59/0.84  thf(zf_stmt_4, axiom,
% 0.59/0.84    (![B:$i,A:$i]:
% 0.59/0.84     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.59/0.84       ( zip_tseitin_0 @ B @ A ) ))).
% 0.59/0.84  thf(zf_stmt_5, axiom,
% 0.59/0.84    (![A:$i,B:$i,C:$i]:
% 0.59/0.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.84       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.59/0.84         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.59/0.84           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.59/0.84             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.59/0.84  thf('18', plain,
% 0.59/0.84      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.59/0.84         (~ (zip_tseitin_0 @ X24 @ X25)
% 0.59/0.84          | (zip_tseitin_1 @ X26 @ X24 @ X25)
% 0.59/0.84          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24))))),
% 0.59/0.84      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.59/0.84  thf('19', plain,
% 0.59/0.84      ((((zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 0.59/0.84         | ~ (zip_tseitin_0 @ sk_B @ k1_xboole_0)))
% 0.59/0.84         <= ((((sk_A) = (k1_xboole_0))))),
% 0.59/0.84      inference('sup-', [status(thm)], ['17', '18'])).
% 0.59/0.84  thf('20', plain,
% 0.59/0.84      (![X19 : $i, X20 : $i]:
% 0.59/0.84         ((zip_tseitin_0 @ X19 @ X20) | ((X20) != (k1_xboole_0)))),
% 0.59/0.84      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.59/0.84  thf('21', plain, (![X19 : $i]: (zip_tseitin_0 @ X19 @ k1_xboole_0)),
% 0.59/0.84      inference('simplify', [status(thm)], ['20'])).
% 0.59/0.84  thf('22', plain,
% 0.59/0.84      (((zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0))
% 0.59/0.84         <= ((((sk_A) = (k1_xboole_0))))),
% 0.59/0.84      inference('demod', [status(thm)], ['19', '21'])).
% 0.59/0.84  thf('23', plain,
% 0.59/0.84      ((((k1_xboole_0) = (k1_relat_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.59/0.84      inference('demod', [status(thm)], ['16', '22'])).
% 0.59/0.84  thf(d3_tarski, axiom,
% 0.59/0.84    (![A:$i,B:$i]:
% 0.59/0.84     ( ( r1_tarski @ A @ B ) <=>
% 0.59/0.84       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.59/0.84  thf('24', plain,
% 0.59/0.84      (![X1 : $i, X3 : $i]:
% 0.59/0.84         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.59/0.84      inference('cnf', [status(esa)], [d3_tarski])).
% 0.59/0.84  thf('25', plain,
% 0.59/0.84      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.59/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.84  thf(cc2_relset_1, axiom,
% 0.59/0.84    (![A:$i,B:$i,C:$i]:
% 0.59/0.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.84       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.59/0.84  thf('26', plain,
% 0.59/0.84      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.59/0.84         ((v5_relat_1 @ X13 @ X15)
% 0.59/0.84          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.59/0.84      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.59/0.84  thf('27', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 0.59/0.84      inference('sup-', [status(thm)], ['25', '26'])).
% 0.59/0.84  thf(d19_relat_1, axiom,
% 0.59/0.84    (![A:$i,B:$i]:
% 0.59/0.84     ( ( v1_relat_1 @ B ) =>
% 0.59/0.84       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.59/0.84  thf('28', plain,
% 0.59/0.84      (![X8 : $i, X9 : $i]:
% 0.59/0.84         (~ (v5_relat_1 @ X8 @ X9)
% 0.59/0.84          | (r1_tarski @ (k2_relat_1 @ X8) @ X9)
% 0.59/0.84          | ~ (v1_relat_1 @ X8))),
% 0.59/0.84      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.59/0.84  thf('29', plain,
% 0.59/0.84      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 0.59/0.84      inference('sup-', [status(thm)], ['27', '28'])).
% 0.59/0.84  thf('30', plain,
% 0.59/0.84      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.59/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.84  thf(cc1_relset_1, axiom,
% 0.59/0.84    (![A:$i,B:$i,C:$i]:
% 0.59/0.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.84       ( v1_relat_1 @ C ) ))).
% 0.59/0.84  thf('31', plain,
% 0.59/0.84      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.59/0.84         ((v1_relat_1 @ X10)
% 0.59/0.84          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.59/0.84      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.59/0.84  thf('32', plain, ((v1_relat_1 @ sk_D)),
% 0.59/0.84      inference('sup-', [status(thm)], ['30', '31'])).
% 0.59/0.84  thf('33', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 0.59/0.84      inference('demod', [status(thm)], ['29', '32'])).
% 0.59/0.84  thf('34', plain,
% 0.59/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.84         (~ (r2_hidden @ X0 @ X1)
% 0.59/0.84          | (r2_hidden @ X0 @ X2)
% 0.59/0.84          | ~ (r1_tarski @ X1 @ X2))),
% 0.59/0.84      inference('cnf', [status(esa)], [d3_tarski])).
% 0.59/0.84  thf('35', plain,
% 0.59/0.84      (![X0 : $i]:
% 0.59/0.84         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D)))),
% 0.59/0.84      inference('sup-', [status(thm)], ['33', '34'])).
% 0.59/0.84  thf('36', plain,
% 0.59/0.84      (![X0 : $i]:
% 0.59/0.84         ((r1_tarski @ (k2_relat_1 @ sk_D) @ X0)
% 0.59/0.84          | (r2_hidden @ (sk_C @ X0 @ (k2_relat_1 @ sk_D)) @ sk_B))),
% 0.59/0.84      inference('sup-', [status(thm)], ['24', '35'])).
% 0.59/0.84  thf('37', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 0.59/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.84  thf('38', plain,
% 0.59/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.84         (~ (r2_hidden @ X0 @ X1)
% 0.59/0.84          | (r2_hidden @ X0 @ X2)
% 0.59/0.84          | ~ (r1_tarski @ X1 @ X2))),
% 0.59/0.84      inference('cnf', [status(esa)], [d3_tarski])).
% 0.59/0.84  thf('39', plain,
% 0.59/0.84      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C_1) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.59/0.84      inference('sup-', [status(thm)], ['37', '38'])).
% 0.59/0.84  thf('40', plain,
% 0.59/0.84      (![X0 : $i]:
% 0.59/0.84         ((r1_tarski @ (k2_relat_1 @ sk_D) @ X0)
% 0.59/0.84          | (r2_hidden @ (sk_C @ X0 @ (k2_relat_1 @ sk_D)) @ sk_C_1))),
% 0.59/0.84      inference('sup-', [status(thm)], ['36', '39'])).
% 0.59/0.84  thf('41', plain,
% 0.59/0.84      (![X1 : $i, X3 : $i]:
% 0.59/0.84         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.59/0.84      inference('cnf', [status(esa)], [d3_tarski])).
% 0.59/0.84  thf('42', plain,
% 0.59/0.84      (((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C_1)
% 0.59/0.84        | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C_1))),
% 0.59/0.84      inference('sup-', [status(thm)], ['40', '41'])).
% 0.59/0.84  thf('43', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C_1)),
% 0.59/0.84      inference('simplify', [status(thm)], ['42'])).
% 0.59/0.84  thf(t4_funct_2, axiom,
% 0.59/0.84    (![A:$i,B:$i]:
% 0.59/0.84     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.59/0.84       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.59/0.84         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.59/0.84           ( m1_subset_1 @
% 0.59/0.84             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.59/0.84  thf('44', plain,
% 0.59/0.84      (![X27 : $i, X28 : $i]:
% 0.59/0.84         (~ (r1_tarski @ (k2_relat_1 @ X27) @ X28)
% 0.59/0.84          | (m1_subset_1 @ X27 @ 
% 0.59/0.84             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X27) @ X28)))
% 0.59/0.84          | ~ (v1_funct_1 @ X27)
% 0.59/0.84          | ~ (v1_relat_1 @ X27))),
% 0.59/0.84      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.59/0.84  thf('45', plain,
% 0.59/0.84      ((~ (v1_relat_1 @ sk_D)
% 0.59/0.84        | ~ (v1_funct_1 @ sk_D)
% 0.59/0.84        | (m1_subset_1 @ sk_D @ 
% 0.59/0.84           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_C_1))))),
% 0.59/0.84      inference('sup-', [status(thm)], ['43', '44'])).
% 0.59/0.84  thf('46', plain, ((v1_relat_1 @ sk_D)),
% 0.59/0.84      inference('sup-', [status(thm)], ['30', '31'])).
% 0.59/0.84  thf('47', plain, ((v1_funct_1 @ sk_D)),
% 0.59/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.84  thf('48', plain,
% 0.59/0.84      ((m1_subset_1 @ sk_D @ 
% 0.59/0.84        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_C_1)))),
% 0.59/0.84      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.59/0.84  thf('49', plain,
% 0.59/0.84      (((m1_subset_1 @ sk_D @ 
% 0.59/0.84         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C_1))))
% 0.59/0.84         <= ((((sk_A) = (k1_xboole_0))))),
% 0.59/0.84      inference('sup+', [status(thm)], ['23', '48'])).
% 0.59/0.84  thf('50', plain,
% 0.59/0.84      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.59/0.84      inference('split', [status(esa)], ['5'])).
% 0.59/0.84  thf('51', plain,
% 0.59/0.84      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))
% 0.59/0.84         <= (~
% 0.59/0.84             ((m1_subset_1 @ sk_D @ 
% 0.59/0.84               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))))),
% 0.59/0.84      inference('split', [status(esa)], ['0'])).
% 0.59/0.84  thf('52', plain,
% 0.59/0.84      ((~ (m1_subset_1 @ sk_D @ 
% 0.59/0.84           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C_1))))
% 0.59/0.84         <= (~
% 0.59/0.84             ((m1_subset_1 @ sk_D @ 
% 0.59/0.84               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) & 
% 0.59/0.84             (((sk_A) = (k1_xboole_0))))),
% 0.59/0.84      inference('sup-', [status(thm)], ['50', '51'])).
% 0.59/0.84  thf('53', plain,
% 0.59/0.84      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.59/0.84       ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 0.59/0.84      inference('sup-', [status(thm)], ['49', '52'])).
% 0.59/0.84  thf('54', plain,
% 0.59/0.84      ((((k1_xboole_0) = (k1_relat_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.59/0.84      inference('demod', [status(thm)], ['16', '22'])).
% 0.59/0.84  thf('55', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C_1)),
% 0.59/0.84      inference('simplify', [status(thm)], ['42'])).
% 0.59/0.84  thf('56', plain,
% 0.59/0.84      (![X27 : $i, X28 : $i]:
% 0.59/0.84         (~ (r1_tarski @ (k2_relat_1 @ X27) @ X28)
% 0.59/0.84          | (v1_funct_2 @ X27 @ (k1_relat_1 @ X27) @ X28)
% 0.59/0.84          | ~ (v1_funct_1 @ X27)
% 0.59/0.84          | ~ (v1_relat_1 @ X27))),
% 0.59/0.84      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.59/0.84  thf('57', plain,
% 0.59/0.84      ((~ (v1_relat_1 @ sk_D)
% 0.59/0.84        | ~ (v1_funct_1 @ sk_D)
% 0.59/0.84        | (v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ sk_C_1))),
% 0.59/0.84      inference('sup-', [status(thm)], ['55', '56'])).
% 0.59/0.84  thf('58', plain, ((v1_relat_1 @ sk_D)),
% 0.59/0.84      inference('sup-', [status(thm)], ['30', '31'])).
% 0.59/0.84  thf('59', plain, ((v1_funct_1 @ sk_D)),
% 0.59/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.84  thf('60', plain, ((v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ sk_C_1)),
% 0.59/0.84      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.59/0.84  thf('61', plain,
% 0.59/0.84      (((v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C_1))
% 0.59/0.84         <= ((((sk_A) = (k1_xboole_0))))),
% 0.59/0.84      inference('sup+', [status(thm)], ['54', '60'])).
% 0.59/0.84  thf('62', plain,
% 0.59/0.84      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.59/0.84      inference('split', [status(esa)], ['5'])).
% 0.59/0.84  thf('63', plain,
% 0.59/0.84      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1))
% 0.59/0.84         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)))),
% 0.59/0.84      inference('split', [status(esa)], ['0'])).
% 0.59/0.84  thf('64', plain,
% 0.59/0.84      ((~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C_1))
% 0.59/0.84         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) & 
% 0.59/0.84             (((sk_A) = (k1_xboole_0))))),
% 0.59/0.84      inference('sup-', [status(thm)], ['62', '63'])).
% 0.59/0.84  thf('65', plain,
% 0.59/0.84      (((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) | ~ (((sk_A) = (k1_xboole_0)))),
% 0.59/0.84      inference('sup-', [status(thm)], ['61', '64'])).
% 0.59/0.84  thf('66', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.59/0.84      inference('split', [status(esa)], ['5'])).
% 0.59/0.84  thf('67', plain,
% 0.59/0.84      (![X19 : $i, X20 : $i]:
% 0.59/0.84         ((zip_tseitin_0 @ X19 @ X20) | ((X19) = (k1_xboole_0)))),
% 0.59/0.84      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.59/0.84  thf('68', plain,
% 0.59/0.84      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.59/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.84  thf('69', plain,
% 0.59/0.84      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.59/0.84         (~ (zip_tseitin_0 @ X24 @ X25)
% 0.59/0.84          | (zip_tseitin_1 @ X26 @ X24 @ X25)
% 0.59/0.84          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24))))),
% 0.59/0.84      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.59/0.84  thf('70', plain,
% 0.59/0.84      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.59/0.84      inference('sup-', [status(thm)], ['68', '69'])).
% 0.59/0.84  thf('71', plain,
% 0.59/0.84      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 0.59/0.84      inference('sup-', [status(thm)], ['67', '70'])).
% 0.59/0.84  thf('72', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.59/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.84  thf('73', plain,
% 0.59/0.84      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.59/0.84         (~ (v1_funct_2 @ X23 @ X21 @ X22)
% 0.59/0.84          | ((X21) = (k1_relset_1 @ X21 @ X22 @ X23))
% 0.59/0.84          | ~ (zip_tseitin_1 @ X23 @ X22 @ X21))),
% 0.59/0.84      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.59/0.84  thf('74', plain,
% 0.59/0.84      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 0.59/0.84        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.59/0.84      inference('sup-', [status(thm)], ['72', '73'])).
% 0.59/0.84  thf('75', plain,
% 0.59/0.84      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.59/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.84  thf('76', plain,
% 0.59/0.84      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.59/0.84         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 0.59/0.84          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.59/0.84      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.59/0.84  thf('77', plain,
% 0.59/0.84      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.59/0.84      inference('sup-', [status(thm)], ['75', '76'])).
% 0.59/0.84  thf('78', plain,
% 0.59/0.84      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.59/0.84      inference('demod', [status(thm)], ['74', '77'])).
% 0.59/0.84  thf('79', plain,
% 0.59/0.84      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.59/0.84      inference('sup-', [status(thm)], ['71', '78'])).
% 0.59/0.84  thf('80', plain, ((v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ sk_C_1)),
% 0.59/0.84      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.59/0.84  thf('81', plain,
% 0.59/0.84      (((v1_funct_2 @ sk_D @ sk_A @ sk_C_1) | ((sk_B) = (k1_xboole_0)))),
% 0.59/0.84      inference('sup+', [status(thm)], ['79', '80'])).
% 0.59/0.84  thf('82', plain,
% 0.59/0.84      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1))
% 0.59/0.84         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)))),
% 0.59/0.84      inference('split', [status(esa)], ['0'])).
% 0.59/0.84  thf('83', plain,
% 0.59/0.84      ((((sk_B) = (k1_xboole_0))) <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)))),
% 0.59/0.84      inference('sup-', [status(thm)], ['81', '82'])).
% 0.59/0.84  thf('84', plain,
% 0.59/0.84      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.59/0.84      inference('split', [status(esa)], ['5'])).
% 0.59/0.84  thf('85', plain,
% 0.59/0.84      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.59/0.84         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 0.59/0.84             ~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)))),
% 0.59/0.84      inference('sup-', [status(thm)], ['83', '84'])).
% 0.59/0.84  thf('86', plain,
% 0.59/0.84      (((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) | (((sk_B) = (k1_xboole_0)))),
% 0.59/0.84      inference('simplify', [status(thm)], ['85'])).
% 0.59/0.84  thf('87', plain,
% 0.59/0.84      (~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) | 
% 0.59/0.84       ~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) | ~ ((v1_funct_1 @ sk_D))),
% 0.59/0.84      inference('split', [status(esa)], ['0'])).
% 0.59/0.84  thf('88', plain,
% 0.59/0.84      (~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 0.59/0.84      inference('sat_resolution*', [status(thm)],
% 0.59/0.84                ['4', '53', '65', '66', '86', '87'])).
% 0.59/0.84  thf('89', plain,
% 0.59/0.84      (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.59/0.84      inference('simpl_trail', [status(thm)], ['1', '88'])).
% 0.59/0.84  thf('90', plain,
% 0.59/0.84      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.59/0.84      inference('sup-', [status(thm)], ['71', '78'])).
% 0.59/0.84  thf('91', plain,
% 0.59/0.84      ((m1_subset_1 @ sk_D @ 
% 0.59/0.84        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_C_1)))),
% 0.59/0.84      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.59/0.84  thf('92', plain,
% 0.59/0.84      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))
% 0.59/0.84        | ((sk_B) = (k1_xboole_0)))),
% 0.59/0.84      inference('sup+', [status(thm)], ['90', '91'])).
% 0.59/0.84  thf('93', plain,
% 0.59/0.84      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.59/0.84      inference('split', [status(esa)], ['5'])).
% 0.59/0.84  thf('94', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.59/0.84      inference('sat_resolution*', [status(thm)], ['4', '53', '65', '87', '66'])).
% 0.59/0.84  thf('95', plain, (((sk_B) != (k1_xboole_0))),
% 0.59/0.84      inference('simpl_trail', [status(thm)], ['93', '94'])).
% 0.59/0.84  thf('96', plain,
% 0.59/0.84      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.59/0.84      inference('simplify_reflect-', [status(thm)], ['92', '95'])).
% 0.59/0.84  thf('97', plain, ($false), inference('demod', [status(thm)], ['89', '96'])).
% 0.59/0.84  
% 0.59/0.84  % SZS output end Refutation
% 0.59/0.84  
% 0.59/0.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
