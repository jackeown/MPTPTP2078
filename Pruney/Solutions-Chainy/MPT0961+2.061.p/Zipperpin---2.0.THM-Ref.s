%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4E4XHc4qUV

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:47 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  139 (4440 expanded)
%              Number of leaves         :   31 (1233 expanded)
%              Depth                    :   21
%              Number of atoms          : 1036 (51076 expanded)
%              Number of equality atoms :   78 (1576 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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

thf(zf_stmt_0,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_4,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('0',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( X22 != k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ( v1_funct_2 @ X24 @ X23 @ X22 )
      | ( X24 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('1',plain,(
    ! [X23: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('3',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X23: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['1','3'])).

thf('5',plain,
    ( ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0 ) )
   <= ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0 ) ) ),
    inference(split,[status(esa)],['4'])).

thf(t3_funct_2,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf(zf_stmt_5,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ( v1_funct_1 @ A )
          & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
          & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t3_funct_2])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('7',plain,
    ( ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
   <= ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('9',plain,
    ( ~ ( v1_funct_1 @ sk_A )
   <= ~ ( v1_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('10',plain,(
    v1_funct_1 @ sk_A ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('11',plain,(
    ! [X10: $i] :
      ( ( r1_tarski @ X10 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X10 ) @ ( k2_relat_1 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X4: $i,X6: $i] :
      ( ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) )
   <= ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference(split,[status(esa)],['6'])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ sk_A )
   <= ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('17',plain,(
    m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('19',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['10','17','18'])).

thf('20',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['7','19'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('21',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('22',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('23',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['2'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('26',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('29',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('33',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X23 )
      | ( zip_tseitin_1 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0 = k1_xboole_0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('38',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X16 @ X14 )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( X19
       != ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ~ ( zip_tseitin_1 @ X21 @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['7','19'])).

thf('46',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('48',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['46','47'])).

thf('50',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['46','47'])).

thf('51',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['20','48','49','50'])).

thf('52',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['7','19'])).

thf('59',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('61',plain,
    ( ( k2_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['46','47'])).

thf('63',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','63'])).

thf('65',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','64'])).

thf('66',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','63'])).

thf('67',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
   <= ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['61','62'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('70',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['2'])).

thf('72',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('73',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['46','47'])).

thf('74',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['70','71','74'])).

thf('76',plain,
    ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference(split,[status(esa)],['4'])).

thf('77',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0 ) )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference(split,[status(esa)],['4'])).

thf('79',plain,(
    ! [X23: $i] :
      ( ( X23 = k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0 ) ) ),
    inference('sat_resolution*',[status(thm)],['77','78'])).

thf('80',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['67','79'])).

thf('81',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','64'])).

thf('82',plain,(
    ! [X23: $i] :
      ( ( X23 = k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0 ) ) ),
    inference('sat_resolution*',[status(thm)],['77','78'])).

thf('83',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('85',plain,
    ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['61','62'])).

thf('87',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','64'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('89',plain,
    ( ( ~ ( zip_tseitin_0 @ ( k2_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( zip_tseitin_1 @ k1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) @ ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) )
   <= ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['61','62'])).

thf('91',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('92',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X18 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('93',plain,(
    ! [X17: $i] :
      ( zip_tseitin_0 @ X17 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['91','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['94'])).

thf('96',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['61','62'])).

thf('97',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','64'])).

thf('98',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['72','73'])).

thf('99',plain,
    ( ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
   <= ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['89','90','95','96','97','98'])).

thf('100',plain,(
    ! [X23: $i] :
      ( ( X23 = k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0 ) ) ),
    inference('sat_resolution*',[status(thm)],['77','78'])).

thf('101',plain,(
    zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['99','100'])).

thf('102',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['72','73'])).

thf('103',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['81','82'])).

thf('104',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['61','62'])).

thf('105',plain,(
    v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['85','86','101','102','103','104'])).

thf('106',plain,(
    $false ),
    inference(demod,[status(thm)],['80','105'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4E4XHc4qUV
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:56:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.56  % Solved by: fo/fo7.sh
% 0.22/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.56  % done 117 iterations in 0.090s
% 0.22/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.56  % SZS output start Refutation
% 0.22/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.56  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.22/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.56  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.22/0.56  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.56  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.22/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.56  thf(d1_funct_2, axiom,
% 0.22/0.56    (![A:$i,B:$i,C:$i]:
% 0.22/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.56       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.22/0.56           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.22/0.56             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.22/0.56         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.22/0.56           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.22/0.56             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.22/0.56  thf(zf_stmt_0, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.22/0.56  thf(zf_stmt_1, axiom,
% 0.22/0.56    (![C:$i,B:$i,A:$i]:
% 0.22/0.56     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.22/0.56       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.22/0.56  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $o).
% 0.22/0.56  thf(zf_stmt_3, axiom,
% 0.22/0.56    (![B:$i,A:$i]:
% 0.22/0.56     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.22/0.56       ( zip_tseitin_0 @ B @ A ) ))).
% 0.22/0.56  thf(zf_stmt_4, axiom,
% 0.22/0.56    (![A:$i,B:$i,C:$i]:
% 0.22/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.56       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.22/0.56         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.22/0.56           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.22/0.56             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.22/0.56  thf('0', plain,
% 0.22/0.56      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.22/0.56         (((X22) != (k1_xboole_0))
% 0.22/0.56          | ((X23) = (k1_xboole_0))
% 0.22/0.56          | (v1_funct_2 @ X24 @ X23 @ X22)
% 0.22/0.56          | ((X24) != (k1_xboole_0))
% 0.22/0.56          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.22/0.56  thf('1', plain,
% 0.22/0.56      (![X23 : $i]:
% 0.22/0.56         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 0.22/0.56             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ k1_xboole_0)))
% 0.22/0.56          | (v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0)
% 0.22/0.56          | ((X23) = (k1_xboole_0)))),
% 0.22/0.56      inference('simplify', [status(thm)], ['0'])).
% 0.22/0.56  thf(t113_zfmisc_1, axiom,
% 0.22/0.56    (![A:$i,B:$i]:
% 0.22/0.56     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.22/0.56       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.22/0.56  thf('2', plain,
% 0.22/0.56      (![X2 : $i, X3 : $i]:
% 0.22/0.56         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 0.22/0.56      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.22/0.56  thf('3', plain,
% 0.22/0.56      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.56      inference('simplify', [status(thm)], ['2'])).
% 0.22/0.56  thf('4', plain,
% 0.22/0.56      (![X23 : $i]:
% 0.22/0.56         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.22/0.56          | (v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0)
% 0.22/0.56          | ((X23) = (k1_xboole_0)))),
% 0.22/0.56      inference('demod', [status(thm)], ['1', '3'])).
% 0.22/0.56  thf('5', plain,
% 0.22/0.56      ((![X23 : $i]:
% 0.22/0.56          (((X23) = (k1_xboole_0))
% 0.22/0.56           | (v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0)))
% 0.22/0.56         <= ((![X23 : $i]:
% 0.22/0.56                (((X23) = (k1_xboole_0))
% 0.22/0.56                 | (v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0))))),
% 0.22/0.56      inference('split', [status(esa)], ['4'])).
% 0.22/0.56  thf(t3_funct_2, conjecture,
% 0.22/0.56    (![A:$i]:
% 0.22/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.56       ( ( v1_funct_1 @ A ) & 
% 0.22/0.56         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.22/0.56         ( m1_subset_1 @
% 0.22/0.56           A @ 
% 0.22/0.56           ( k1_zfmisc_1 @
% 0.22/0.56             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.22/0.56  thf(zf_stmt_5, negated_conjecture,
% 0.22/0.56    (~( ![A:$i]:
% 0.22/0.56        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.56          ( ( v1_funct_1 @ A ) & 
% 0.22/0.56            ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.22/0.56            ( m1_subset_1 @
% 0.22/0.56              A @ 
% 0.22/0.56              ( k1_zfmisc_1 @
% 0.22/0.56                ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )),
% 0.22/0.56    inference('cnf.neg', [status(esa)], [t3_funct_2])).
% 0.22/0.56  thf('6', plain,
% 0.22/0.56      ((~ (v1_funct_1 @ sk_A)
% 0.22/0.56        | ~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 0.22/0.56        | ~ (m1_subset_1 @ sk_A @ 
% 0.22/0.56             (k1_zfmisc_1 @ 
% 0.22/0.56              (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.22/0.56  thf('7', plain,
% 0.22/0.56      ((~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))
% 0.22/0.56         <= (~
% 0.22/0.56             ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))),
% 0.22/0.56      inference('split', [status(esa)], ['6'])).
% 0.22/0.56  thf('8', plain, ((v1_funct_1 @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.22/0.56  thf('9', plain, ((~ (v1_funct_1 @ sk_A)) <= (~ ((v1_funct_1 @ sk_A)))),
% 0.22/0.56      inference('split', [status(esa)], ['6'])).
% 0.22/0.56  thf('10', plain, (((v1_funct_1 @ sk_A))),
% 0.22/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.56  thf(t21_relat_1, axiom,
% 0.22/0.56    (![A:$i]:
% 0.22/0.56     ( ( v1_relat_1 @ A ) =>
% 0.22/0.56       ( r1_tarski @
% 0.22/0.56         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.22/0.56  thf('11', plain,
% 0.22/0.56      (![X10 : $i]:
% 0.22/0.56         ((r1_tarski @ X10 @ 
% 0.22/0.56           (k2_zfmisc_1 @ (k1_relat_1 @ X10) @ (k2_relat_1 @ X10)))
% 0.22/0.56          | ~ (v1_relat_1 @ X10))),
% 0.22/0.56      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.22/0.56  thf(t3_subset, axiom,
% 0.22/0.56    (![A:$i,B:$i]:
% 0.22/0.56     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.56  thf('12', plain,
% 0.22/0.56      (![X4 : $i, X6 : $i]:
% 0.22/0.56         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.22/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.56  thf('13', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         (~ (v1_relat_1 @ X0)
% 0.22/0.56          | (m1_subset_1 @ X0 @ 
% 0.22/0.56             (k1_zfmisc_1 @ 
% 0.22/0.56              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.22/0.56      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.56  thf('14', plain,
% 0.22/0.56      ((~ (m1_subset_1 @ sk_A @ 
% 0.22/0.56           (k1_zfmisc_1 @ 
% 0.22/0.56            (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))
% 0.22/0.56         <= (~
% 0.22/0.56             ((m1_subset_1 @ sk_A @ 
% 0.22/0.56               (k1_zfmisc_1 @ 
% 0.22/0.56                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.22/0.56      inference('split', [status(esa)], ['6'])).
% 0.22/0.56  thf('15', plain,
% 0.22/0.56      ((~ (v1_relat_1 @ sk_A))
% 0.22/0.56         <= (~
% 0.22/0.56             ((m1_subset_1 @ sk_A @ 
% 0.22/0.56               (k1_zfmisc_1 @ 
% 0.22/0.56                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.22/0.56      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.56  thf('16', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.22/0.56  thf('17', plain,
% 0.22/0.56      (((m1_subset_1 @ sk_A @ 
% 0.22/0.56         (k1_zfmisc_1 @ 
% 0.22/0.56          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.22/0.56      inference('demod', [status(thm)], ['15', '16'])).
% 0.22/0.56  thf('18', plain,
% 0.22/0.56      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))) | 
% 0.22/0.56       ~
% 0.22/0.56       ((m1_subset_1 @ sk_A @ 
% 0.22/0.56         (k1_zfmisc_1 @ 
% 0.22/0.56          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))) | 
% 0.22/0.56       ~ ((v1_funct_1 @ sk_A))),
% 0.22/0.56      inference('split', [status(esa)], ['6'])).
% 0.22/0.56  thf('19', plain,
% 0.22/0.56      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))),
% 0.22/0.56      inference('sat_resolution*', [status(thm)], ['10', '17', '18'])).
% 0.22/0.56  thf('20', plain,
% 0.22/0.56      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.22/0.56      inference('simpl_trail', [status(thm)], ['7', '19'])).
% 0.22/0.56  thf(t7_xboole_0, axiom,
% 0.22/0.56    (![A:$i]:
% 0.22/0.56     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.56          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.22/0.56  thf('21', plain,
% 0.22/0.56      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.22/0.56      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.22/0.56  thf('22', plain,
% 0.22/0.56      (![X17 : $i, X18 : $i]:
% 0.22/0.56         ((zip_tseitin_0 @ X17 @ X18) | ((X17) = (k1_xboole_0)))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.56  thf('23', plain,
% 0.22/0.56      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.56      inference('simplify', [status(thm)], ['2'])).
% 0.22/0.56  thf('24', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.56         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 0.22/0.56      inference('sup+', [status(thm)], ['22', '23'])).
% 0.22/0.56  thf('25', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         (~ (v1_relat_1 @ X0)
% 0.22/0.56          | (m1_subset_1 @ X0 @ 
% 0.22/0.56             (k1_zfmisc_1 @ 
% 0.22/0.56              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.22/0.56      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.56  thf(t5_subset, axiom,
% 0.22/0.56    (![A:$i,B:$i,C:$i]:
% 0.22/0.56     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.22/0.56          ( v1_xboole_0 @ C ) ) ))).
% 0.22/0.56  thf('26', plain,
% 0.22/0.56      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.56         (~ (r2_hidden @ X7 @ X8)
% 0.22/0.56          | ~ (v1_xboole_0 @ X9)
% 0.22/0.56          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.22/0.56      inference('cnf', [status(esa)], [t5_subset])).
% 0.22/0.56  thf('27', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i]:
% 0.22/0.56         (~ (v1_relat_1 @ X0)
% 0.22/0.56          | ~ (v1_xboole_0 @ 
% 0.22/0.56               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 0.22/0.56          | ~ (r2_hidden @ X1 @ X0))),
% 0.22/0.56      inference('sup-', [status(thm)], ['25', '26'])).
% 0.22/0.56  thf('28', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.56         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.22/0.56          | (zip_tseitin_0 @ (k2_relat_1 @ X0) @ X2)
% 0.22/0.56          | ~ (r2_hidden @ X1 @ X0)
% 0.22/0.56          | ~ (v1_relat_1 @ X0))),
% 0.22/0.56      inference('sup-', [status(thm)], ['24', '27'])).
% 0.22/0.56  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.22/0.56  thf('29', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.56  thf('30', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.56         ((zip_tseitin_0 @ (k2_relat_1 @ X0) @ X2)
% 0.22/0.56          | ~ (r2_hidden @ X1 @ X0)
% 0.22/0.56          | ~ (v1_relat_1 @ X0))),
% 0.22/0.56      inference('demod', [status(thm)], ['28', '29'])).
% 0.22/0.56  thf('31', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i]:
% 0.22/0.56         (((X0) = (k1_xboole_0))
% 0.22/0.56          | ~ (v1_relat_1 @ X0)
% 0.22/0.56          | (zip_tseitin_0 @ (k2_relat_1 @ X0) @ X1))),
% 0.22/0.56      inference('sup-', [status(thm)], ['21', '30'])).
% 0.22/0.56  thf('32', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         (~ (v1_relat_1 @ X0)
% 0.22/0.56          | (m1_subset_1 @ X0 @ 
% 0.22/0.56             (k1_zfmisc_1 @ 
% 0.22/0.56              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.22/0.56      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.56  thf('33', plain,
% 0.22/0.56      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.22/0.56         (~ (zip_tseitin_0 @ X22 @ X23)
% 0.22/0.56          | (zip_tseitin_1 @ X24 @ X22 @ X23)
% 0.22/0.56          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.22/0.56  thf('34', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         (~ (v1_relat_1 @ X0)
% 0.22/0.56          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.22/0.56          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.56  thf('35', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         (~ (v1_relat_1 @ X0)
% 0.22/0.56          | ((X0) = (k1_xboole_0))
% 0.22/0.56          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.22/0.56          | ~ (v1_relat_1 @ X0))),
% 0.22/0.56      inference('sup-', [status(thm)], ['31', '34'])).
% 0.22/0.56  thf('36', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         ((zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.22/0.56          | ((X0) = (k1_xboole_0))
% 0.22/0.56          | ~ (v1_relat_1 @ X0))),
% 0.22/0.56      inference('simplify', [status(thm)], ['35'])).
% 0.22/0.56  thf('37', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         (~ (v1_relat_1 @ X0)
% 0.22/0.56          | (m1_subset_1 @ X0 @ 
% 0.22/0.56             (k1_zfmisc_1 @ 
% 0.22/0.56              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.22/0.56      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.56  thf(redefinition_k1_relset_1, axiom,
% 0.22/0.56    (![A:$i,B:$i,C:$i]:
% 0.22/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.56       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.22/0.56  thf('38', plain,
% 0.22/0.56      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.56         (((k1_relset_1 @ X15 @ X16 @ X14) = (k1_relat_1 @ X14))
% 0.22/0.56          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.22/0.56      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.22/0.56  thf('39', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         (~ (v1_relat_1 @ X0)
% 0.22/0.56          | ((k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.22/0.56              = (k1_relat_1 @ X0)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['37', '38'])).
% 0.22/0.56  thf('40', plain,
% 0.22/0.56      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.22/0.56         (((X19) != (k1_relset_1 @ X19 @ X20 @ X21))
% 0.22/0.56          | (v1_funct_2 @ X21 @ X19 @ X20)
% 0.22/0.56          | ~ (zip_tseitin_1 @ X21 @ X20 @ X19))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.56  thf('41', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 0.22/0.56          | ~ (v1_relat_1 @ X0)
% 0.22/0.56          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.22/0.56          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['39', '40'])).
% 0.22/0.56  thf('42', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.22/0.56          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.22/0.56          | ~ (v1_relat_1 @ X0))),
% 0.22/0.56      inference('simplify', [status(thm)], ['41'])).
% 0.22/0.56  thf('43', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         (~ (v1_relat_1 @ X0)
% 0.22/0.56          | ((X0) = (k1_xboole_0))
% 0.22/0.56          | ~ (v1_relat_1 @ X0)
% 0.22/0.56          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['36', '42'])).
% 0.22/0.56  thf('44', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.22/0.56          | ((X0) = (k1_xboole_0))
% 0.22/0.56          | ~ (v1_relat_1 @ X0))),
% 0.22/0.56      inference('simplify', [status(thm)], ['43'])).
% 0.22/0.56  thf('45', plain,
% 0.22/0.56      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.22/0.56      inference('simpl_trail', [status(thm)], ['7', '19'])).
% 0.22/0.56  thf('46', plain, ((~ (v1_relat_1 @ sk_A) | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['44', '45'])).
% 0.22/0.56  thf('47', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.22/0.56  thf('48', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.56      inference('demod', [status(thm)], ['46', '47'])).
% 0.22/0.56  thf('49', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.56      inference('demod', [status(thm)], ['46', '47'])).
% 0.22/0.56  thf('50', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.56      inference('demod', [status(thm)], ['46', '47'])).
% 0.22/0.56  thf('51', plain,
% 0.22/0.56      (~ (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ 
% 0.22/0.56          (k2_relat_1 @ k1_xboole_0))),
% 0.22/0.56      inference('demod', [status(thm)], ['20', '48', '49', '50'])).
% 0.22/0.56  thf('52', plain,
% 0.22/0.56      (![X17 : $i, X18 : $i]:
% 0.22/0.56         ((zip_tseitin_0 @ X17 @ X18) | ((X17) = (k1_xboole_0)))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.56  thf('53', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         (~ (v1_relat_1 @ X0)
% 0.22/0.56          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.22/0.56          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.56  thf('54', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.22/0.56          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.22/0.56          | ~ (v1_relat_1 @ X0))),
% 0.22/0.56      inference('sup-', [status(thm)], ['52', '53'])).
% 0.22/0.56  thf('55', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.22/0.56          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.22/0.56          | ~ (v1_relat_1 @ X0))),
% 0.22/0.56      inference('simplify', [status(thm)], ['41'])).
% 0.22/0.56  thf('56', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         (~ (v1_relat_1 @ X0)
% 0.22/0.56          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.22/0.56          | ~ (v1_relat_1 @ X0)
% 0.22/0.56          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['54', '55'])).
% 0.22/0.56  thf('57', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.22/0.56          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.22/0.56          | ~ (v1_relat_1 @ X0))),
% 0.22/0.56      inference('simplify', [status(thm)], ['56'])).
% 0.22/0.56  thf('58', plain,
% 0.22/0.56      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.22/0.56      inference('simpl_trail', [status(thm)], ['7', '19'])).
% 0.22/0.56  thf('59', plain,
% 0.22/0.56      ((~ (v1_relat_1 @ sk_A) | ((k2_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['57', '58'])).
% 0.22/0.56  thf('60', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.22/0.56  thf('61', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.22/0.56      inference('demod', [status(thm)], ['59', '60'])).
% 0.22/0.56  thf('62', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.56      inference('demod', [status(thm)], ['46', '47'])).
% 0.22/0.56  thf('63', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.56      inference('demod', [status(thm)], ['61', '62'])).
% 0.22/0.56  thf('64', plain,
% 0.22/0.56      (~ (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0)),
% 0.22/0.56      inference('demod', [status(thm)], ['51', '63'])).
% 0.22/0.56  thf('65', plain,
% 0.22/0.56      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))
% 0.22/0.56         <= ((![X23 : $i]:
% 0.22/0.56                (((X23) = (k1_xboole_0))
% 0.22/0.56                 | (v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0))))),
% 0.22/0.56      inference('sup-', [status(thm)], ['5', '64'])).
% 0.22/0.56  thf('66', plain,
% 0.22/0.56      (~ (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0)),
% 0.22/0.56      inference('demod', [status(thm)], ['51', '63'])).
% 0.22/0.56  thf('67', plain,
% 0.22/0.56      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))
% 0.22/0.56         <= ((![X23 : $i]:
% 0.22/0.56                (((X23) = (k1_xboole_0))
% 0.22/0.56                 | (v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0))))),
% 0.22/0.56      inference('sup-', [status(thm)], ['65', '66'])).
% 0.22/0.56  thf('68', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.56      inference('demod', [status(thm)], ['61', '62'])).
% 0.22/0.56  thf('69', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         (~ (v1_relat_1 @ X0)
% 0.22/0.56          | (m1_subset_1 @ X0 @ 
% 0.22/0.56             (k1_zfmisc_1 @ 
% 0.22/0.56              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.22/0.56      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.56  thf('70', plain,
% 0.22/0.56      (((m1_subset_1 @ k1_xboole_0 @ 
% 0.22/0.56         (k1_zfmisc_1 @ 
% 0.22/0.56          (k2_zfmisc_1 @ (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0)))
% 0.22/0.56        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.22/0.56      inference('sup+', [status(thm)], ['68', '69'])).
% 0.22/0.56  thf('71', plain,
% 0.22/0.56      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.56      inference('simplify', [status(thm)], ['2'])).
% 0.22/0.56  thf('72', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.22/0.56  thf('73', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.56      inference('demod', [status(thm)], ['46', '47'])).
% 0.22/0.56  thf('74', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.22/0.56      inference('demod', [status(thm)], ['72', '73'])).
% 0.22/0.56  thf('75', plain, ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.22/0.56      inference('demod', [status(thm)], ['70', '71', '74'])).
% 0.22/0.56  thf('76', plain,
% 0.22/0.56      ((~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.22/0.56         <= (~ ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))))),
% 0.22/0.56      inference('split', [status(esa)], ['4'])).
% 0.22/0.56  thf('77', plain,
% 0.22/0.56      (((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['75', '76'])).
% 0.22/0.56  thf('78', plain,
% 0.22/0.56      ((![X23 : $i]:
% 0.22/0.56          (((X23) = (k1_xboole_0))
% 0.22/0.56           | (v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0))) | 
% 0.22/0.56       ~ ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 0.22/0.56      inference('split', [status(esa)], ['4'])).
% 0.22/0.56  thf('79', plain,
% 0.22/0.56      ((![X23 : $i]:
% 0.22/0.56          (((X23) = (k1_xboole_0))
% 0.22/0.56           | (v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0)))),
% 0.22/0.56      inference('sat_resolution*', [status(thm)], ['77', '78'])).
% 0.22/0.56  thf('80', plain, (~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.22/0.56      inference('simpl_trail', [status(thm)], ['67', '79'])).
% 0.22/0.56  thf('81', plain,
% 0.22/0.56      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))
% 0.22/0.56         <= ((![X23 : $i]:
% 0.22/0.56                (((X23) = (k1_xboole_0))
% 0.22/0.56                 | (v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0))))),
% 0.22/0.56      inference('sup-', [status(thm)], ['5', '64'])).
% 0.22/0.56  thf('82', plain,
% 0.22/0.56      ((![X23 : $i]:
% 0.22/0.56          (((X23) = (k1_xboole_0))
% 0.22/0.56           | (v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0)))),
% 0.22/0.56      inference('sat_resolution*', [status(thm)], ['77', '78'])).
% 0.22/0.56  thf('83', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.56      inference('simpl_trail', [status(thm)], ['81', '82'])).
% 0.22/0.56  thf('84', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.22/0.56          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.22/0.56          | ~ (v1_relat_1 @ X0))),
% 0.22/0.56      inference('simplify', [status(thm)], ['41'])).
% 0.22/0.56  thf('85', plain,
% 0.22/0.56      ((~ (zip_tseitin_1 @ k1_xboole_0 @ (k2_relat_1 @ k1_xboole_0) @ 
% 0.22/0.56           k1_xboole_0)
% 0.22/0.56        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.22/0.56        | (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ 
% 0.22/0.56           (k2_relat_1 @ k1_xboole_0)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['83', '84'])).
% 0.22/0.56  thf('86', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.56      inference('demod', [status(thm)], ['61', '62'])).
% 0.22/0.56  thf('87', plain,
% 0.22/0.56      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))
% 0.22/0.56         <= ((![X23 : $i]:
% 0.22/0.56                (((X23) = (k1_xboole_0))
% 0.22/0.56                 | (v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0))))),
% 0.22/0.56      inference('sup-', [status(thm)], ['5', '64'])).
% 0.22/0.56  thf('88', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         (~ (v1_relat_1 @ X0)
% 0.22/0.56          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.22/0.56          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.56  thf('89', plain,
% 0.22/0.56      (((~ (zip_tseitin_0 @ (k2_relat_1 @ k1_xboole_0) @ k1_xboole_0)
% 0.22/0.56         | (zip_tseitin_1 @ k1_xboole_0 @ (k2_relat_1 @ k1_xboole_0) @ 
% 0.22/0.56            (k1_relat_1 @ k1_xboole_0))
% 0.22/0.56         | ~ (v1_relat_1 @ k1_xboole_0)))
% 0.22/0.56         <= ((![X23 : $i]:
% 0.22/0.56                (((X23) = (k1_xboole_0))
% 0.22/0.56                 | (v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0))))),
% 0.22/0.56      inference('sup-', [status(thm)], ['87', '88'])).
% 0.22/0.56  thf('90', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.56      inference('demod', [status(thm)], ['61', '62'])).
% 0.22/0.56  thf('91', plain,
% 0.22/0.56      (![X17 : $i, X18 : $i]:
% 0.22/0.56         ((zip_tseitin_0 @ X17 @ X18) | ((X17) = (k1_xboole_0)))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.56  thf('92', plain,
% 0.22/0.56      (![X17 : $i, X18 : $i]:
% 0.22/0.56         ((zip_tseitin_0 @ X17 @ X18) | ((X18) != (k1_xboole_0)))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.56  thf('93', plain, (![X17 : $i]: (zip_tseitin_0 @ X17 @ k1_xboole_0)),
% 0.22/0.56      inference('simplify', [status(thm)], ['92'])).
% 0.22/0.56  thf('94', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.56         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 0.22/0.56      inference('sup+', [status(thm)], ['91', '93'])).
% 0.22/0.56  thf('95', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 0.22/0.56      inference('eq_fact', [status(thm)], ['94'])).
% 0.22/0.56  thf('96', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.56      inference('demod', [status(thm)], ['61', '62'])).
% 0.22/0.56  thf('97', plain,
% 0.22/0.56      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))
% 0.22/0.56         <= ((![X23 : $i]:
% 0.22/0.56                (((X23) = (k1_xboole_0))
% 0.22/0.56                 | (v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0))))),
% 0.22/0.56      inference('sup-', [status(thm)], ['5', '64'])).
% 0.22/0.56  thf('98', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.22/0.56      inference('demod', [status(thm)], ['72', '73'])).
% 0.22/0.56  thf('99', plain,
% 0.22/0.56      (((zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))
% 0.22/0.56         <= ((![X23 : $i]:
% 0.22/0.56                (((X23) = (k1_xboole_0))
% 0.22/0.56                 | (v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0))))),
% 0.22/0.56      inference('demod', [status(thm)], ['89', '90', '95', '96', '97', '98'])).
% 0.22/0.56  thf('100', plain,
% 0.22/0.56      ((![X23 : $i]:
% 0.22/0.56          (((X23) = (k1_xboole_0))
% 0.22/0.56           | (v1_funct_2 @ k1_xboole_0 @ X23 @ k1_xboole_0)))),
% 0.22/0.56      inference('sat_resolution*', [status(thm)], ['77', '78'])).
% 0.22/0.56  thf('101', plain,
% 0.22/0.56      ((zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.22/0.56      inference('simpl_trail', [status(thm)], ['99', '100'])).
% 0.22/0.56  thf('102', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.22/0.56      inference('demod', [status(thm)], ['72', '73'])).
% 0.22/0.56  thf('103', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.56      inference('simpl_trail', [status(thm)], ['81', '82'])).
% 0.22/0.56  thf('104', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.56      inference('demod', [status(thm)], ['61', '62'])).
% 0.22/0.56  thf('105', plain, ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.22/0.56      inference('demod', [status(thm)],
% 0.22/0.56                ['85', '86', '101', '102', '103', '104'])).
% 0.22/0.56  thf('106', plain, ($false), inference('demod', [status(thm)], ['80', '105'])).
% 0.22/0.56  
% 0.22/0.56  % SZS output end Refutation
% 0.22/0.56  
% 0.22/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
