%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GrJnCMPkAw

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:38 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 327 expanded)
%              Number of leaves         :   27 (  98 expanded)
%              Depth                    :   15
%              Number of atoms          :  670 (3628 expanded)
%              Number of equality atoms :   47 ( 136 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(t3_funct_2,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ( v1_funct_1 @ A )
          & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
          & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t3_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
   <= ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_A )
   <= ~ ( v1_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('4',plain,(
    v1_funct_1 @ sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('8',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X22 ) @ X23 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X22 ) @ X24 )
      | ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,
    ( ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) )
   <= ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ sk_A )
   <= ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['4','14','15'])).

thf('17',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['1','16'])).

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
     => ( zip_tseitin_4 @ B @ A ) ) )).

thf('18',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_4 @ X31 @ X32 )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(zf_stmt_2,type,(
    zip_tseitin_5: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_5 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_4 @ B @ A )
         => ( zip_tseitin_5 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('20',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_4 @ X36 @ X37 )
      | ( zip_tseitin_5 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_5 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_4 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_5 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('24',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( X33
       != ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ~ ( zip_tseitin_5 @ X35 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( zip_tseitin_5 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_5 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['1','16'])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( k2_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','34'])).

thf('36',plain,
    ( ( k2_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['32','33'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('37',plain,(
    ! [X7: $i] :
      ( ( ( k2_relat_1 @ X7 )
       != k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('38',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['40'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('43',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('44',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('45',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( X33
       != ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ~ ( zip_tseitin_5 @ X35 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_5 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_5 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_4 @ X31 @ X32 )
      | ( X32 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('53',plain,(
    ! [X31: $i] :
      ( zip_tseitin_4 @ X31 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('55',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_4 @ X36 @ X37 )
      | ( zip_tseitin_5 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_5 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_4 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( zip_tseitin_5 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('simplify_reflect+',[status(thm)],['51','57'])).

thf('59',plain,(
    $false ),
    inference(demod,[status(thm)],['35','41','42','43','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GrJnCMPkAw
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:08:48 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.37/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.59  % Solved by: fo/fo7.sh
% 0.37/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.59  % done 156 iterations in 0.141s
% 0.37/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.59  % SZS output start Refutation
% 0.37/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.59  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $i > $o).
% 0.37/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.59  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.37/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.37/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.37/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.37/0.59  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 0.37/0.59  thf(t3_funct_2, conjecture,
% 0.37/0.59    (![A:$i]:
% 0.37/0.59     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.37/0.59       ( ( v1_funct_1 @ A ) & 
% 0.37/0.59         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.37/0.59         ( m1_subset_1 @
% 0.37/0.59           A @ 
% 0.37/0.59           ( k1_zfmisc_1 @
% 0.37/0.59             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.37/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.59    (~( ![A:$i]:
% 0.37/0.59        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.37/0.59          ( ( v1_funct_1 @ A ) & 
% 0.37/0.59            ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.37/0.59            ( m1_subset_1 @
% 0.37/0.59              A @ 
% 0.37/0.59              ( k1_zfmisc_1 @
% 0.37/0.59                ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )),
% 0.37/0.59    inference('cnf.neg', [status(esa)], [t3_funct_2])).
% 0.37/0.59  thf('0', plain,
% 0.37/0.59      ((~ (v1_funct_1 @ sk_A)
% 0.37/0.59        | ~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 0.37/0.59        | ~ (m1_subset_1 @ sk_A @ 
% 0.37/0.59             (k1_zfmisc_1 @ 
% 0.37/0.59              (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('1', plain,
% 0.37/0.59      ((~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))
% 0.37/0.59         <= (~
% 0.37/0.59             ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))),
% 0.37/0.59      inference('split', [status(esa)], ['0'])).
% 0.37/0.59  thf('2', plain, ((v1_funct_1 @ sk_A)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('3', plain, ((~ (v1_funct_1 @ sk_A)) <= (~ ((v1_funct_1 @ sk_A)))),
% 0.37/0.59      inference('split', [status(esa)], ['0'])).
% 0.37/0.59  thf('4', plain, (((v1_funct_1 @ sk_A))),
% 0.37/0.59      inference('sup-', [status(thm)], ['2', '3'])).
% 0.37/0.59  thf(d10_xboole_0, axiom,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.59  thf('5', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.37/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.59  thf('6', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.37/0.59      inference('simplify', [status(thm)], ['5'])).
% 0.37/0.59  thf('7', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.37/0.59      inference('simplify', [status(thm)], ['5'])).
% 0.37/0.59  thf(t11_relset_1, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i]:
% 0.37/0.59     ( ( v1_relat_1 @ C ) =>
% 0.37/0.59       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.37/0.59           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.37/0.59         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.37/0.59  thf('8', plain,
% 0.37/0.59      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.37/0.59         (~ (r1_tarski @ (k1_relat_1 @ X22) @ X23)
% 0.37/0.59          | ~ (r1_tarski @ (k2_relat_1 @ X22) @ X24)
% 0.37/0.59          | (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.37/0.59          | ~ (v1_relat_1 @ X22))),
% 0.37/0.59      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.37/0.59  thf('9', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         (~ (v1_relat_1 @ X0)
% 0.37/0.59          | (m1_subset_1 @ X0 @ 
% 0.37/0.59             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.37/0.59          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.37/0.59      inference('sup-', [status(thm)], ['7', '8'])).
% 0.37/0.59  thf('10', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         ((m1_subset_1 @ X0 @ 
% 0.37/0.59           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.37/0.59          | ~ (v1_relat_1 @ X0))),
% 0.37/0.59      inference('sup-', [status(thm)], ['6', '9'])).
% 0.37/0.59  thf('11', plain,
% 0.37/0.59      ((~ (m1_subset_1 @ sk_A @ 
% 0.37/0.59           (k1_zfmisc_1 @ 
% 0.37/0.59            (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))
% 0.37/0.59         <= (~
% 0.37/0.59             ((m1_subset_1 @ sk_A @ 
% 0.37/0.59               (k1_zfmisc_1 @ 
% 0.37/0.59                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.37/0.59      inference('split', [status(esa)], ['0'])).
% 0.37/0.59  thf('12', plain,
% 0.37/0.59      ((~ (v1_relat_1 @ sk_A))
% 0.37/0.59         <= (~
% 0.37/0.59             ((m1_subset_1 @ sk_A @ 
% 0.37/0.59               (k1_zfmisc_1 @ 
% 0.37/0.59                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.37/0.59      inference('sup-', [status(thm)], ['10', '11'])).
% 0.37/0.59  thf('13', plain, ((v1_relat_1 @ sk_A)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('14', plain,
% 0.37/0.59      (((m1_subset_1 @ sk_A @ 
% 0.37/0.59         (k1_zfmisc_1 @ 
% 0.37/0.59          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.37/0.59      inference('demod', [status(thm)], ['12', '13'])).
% 0.37/0.59  thf('15', plain,
% 0.37/0.59      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))) | 
% 0.37/0.59       ~
% 0.37/0.59       ((m1_subset_1 @ sk_A @ 
% 0.37/0.59         (k1_zfmisc_1 @ 
% 0.37/0.59          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))) | 
% 0.37/0.59       ~ ((v1_funct_1 @ sk_A))),
% 0.37/0.59      inference('split', [status(esa)], ['0'])).
% 0.37/0.59  thf('16', plain,
% 0.37/0.59      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))),
% 0.37/0.59      inference('sat_resolution*', [status(thm)], ['4', '14', '15'])).
% 0.37/0.59  thf('17', plain,
% 0.37/0.59      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.37/0.59      inference('simpl_trail', [status(thm)], ['1', '16'])).
% 0.37/0.59  thf(d1_funct_2, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i]:
% 0.37/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.59       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.37/0.59           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.37/0.59             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.37/0.59         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.37/0.59           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.37/0.59             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.37/0.59  thf(zf_stmt_1, axiom,
% 0.37/0.59    (![B:$i,A:$i]:
% 0.37/0.59     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.37/0.59       ( zip_tseitin_4 @ B @ A ) ))).
% 0.37/0.59  thf('18', plain,
% 0.37/0.59      (![X31 : $i, X32 : $i]:
% 0.37/0.59         ((zip_tseitin_4 @ X31 @ X32) | ((X31) = (k1_xboole_0)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.37/0.59  thf('19', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         ((m1_subset_1 @ X0 @ 
% 0.37/0.59           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.37/0.59          | ~ (v1_relat_1 @ X0))),
% 0.37/0.59      inference('sup-', [status(thm)], ['6', '9'])).
% 0.37/0.59  thf(zf_stmt_2, type, zip_tseitin_5 : $i > $i > $i > $o).
% 0.37/0.59  thf(zf_stmt_3, axiom,
% 0.37/0.59    (![C:$i,B:$i,A:$i]:
% 0.37/0.59     ( ( zip_tseitin_5 @ C @ B @ A ) =>
% 0.37/0.59       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.37/0.59  thf(zf_stmt_4, type, zip_tseitin_4 : $i > $i > $o).
% 0.37/0.59  thf(zf_stmt_5, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i]:
% 0.37/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.59       ( ( ( zip_tseitin_4 @ B @ A ) => ( zip_tseitin_5 @ C @ B @ A ) ) & 
% 0.37/0.59         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.37/0.59           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.37/0.59             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.37/0.59  thf('20', plain,
% 0.37/0.59      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.37/0.59         (~ (zip_tseitin_4 @ X36 @ X37)
% 0.37/0.59          | (zip_tseitin_5 @ X38 @ X36 @ X37)
% 0.37/0.59          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.37/0.59  thf('21', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         (~ (v1_relat_1 @ X0)
% 0.37/0.59          | (zip_tseitin_5 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.37/0.59          | ~ (zip_tseitin_4 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['19', '20'])).
% 0.37/0.59  thf('22', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.37/0.59          | (zip_tseitin_5 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.37/0.59          | ~ (v1_relat_1 @ X0))),
% 0.37/0.59      inference('sup-', [status(thm)], ['18', '21'])).
% 0.37/0.59  thf('23', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         ((m1_subset_1 @ X0 @ 
% 0.37/0.59           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.37/0.59          | ~ (v1_relat_1 @ X0))),
% 0.37/0.59      inference('sup-', [status(thm)], ['6', '9'])).
% 0.37/0.59  thf(redefinition_k1_relset_1, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i]:
% 0.37/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.59       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.37/0.59  thf('24', plain,
% 0.37/0.59      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.37/0.59         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 0.37/0.59          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.37/0.59      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.37/0.59  thf('25', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         (~ (v1_relat_1 @ X0)
% 0.37/0.59          | ((k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.37/0.59              = (k1_relat_1 @ X0)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['23', '24'])).
% 0.37/0.59  thf('26', plain,
% 0.37/0.59      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.37/0.59         (((X33) != (k1_relset_1 @ X33 @ X34 @ X35))
% 0.37/0.59          | (v1_funct_2 @ X35 @ X33 @ X34)
% 0.37/0.59          | ~ (zip_tseitin_5 @ X35 @ X34 @ X33))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.37/0.59  thf('27', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 0.37/0.59          | ~ (v1_relat_1 @ X0)
% 0.37/0.59          | ~ (zip_tseitin_5 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.37/0.59          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['25', '26'])).
% 0.37/0.59  thf('28', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.37/0.59          | ~ (zip_tseitin_5 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.37/0.59          | ~ (v1_relat_1 @ X0))),
% 0.37/0.59      inference('simplify', [status(thm)], ['27'])).
% 0.37/0.59  thf('29', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         (~ (v1_relat_1 @ X0)
% 0.37/0.59          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.37/0.59          | ~ (v1_relat_1 @ X0)
% 0.37/0.59          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['22', '28'])).
% 0.37/0.59  thf('30', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.37/0.59          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.37/0.59          | ~ (v1_relat_1 @ X0))),
% 0.37/0.59      inference('simplify', [status(thm)], ['29'])).
% 0.37/0.59  thf('31', plain,
% 0.37/0.59      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.37/0.59      inference('simpl_trail', [status(thm)], ['1', '16'])).
% 0.37/0.59  thf('32', plain,
% 0.37/0.59      ((~ (v1_relat_1 @ sk_A) | ((k2_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['30', '31'])).
% 0.37/0.59  thf('33', plain, ((v1_relat_1 @ sk_A)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('34', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.37/0.59      inference('demod', [status(thm)], ['32', '33'])).
% 0.37/0.59  thf('35', plain, (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ k1_xboole_0)),
% 0.37/0.59      inference('demod', [status(thm)], ['17', '34'])).
% 0.37/0.59  thf('36', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.37/0.59      inference('demod', [status(thm)], ['32', '33'])).
% 0.37/0.59  thf(t64_relat_1, axiom,
% 0.37/0.59    (![A:$i]:
% 0.37/0.59     ( ( v1_relat_1 @ A ) =>
% 0.37/0.59       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.37/0.59           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.37/0.59         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.37/0.59  thf('37', plain,
% 0.37/0.59      (![X7 : $i]:
% 0.37/0.59         (((k2_relat_1 @ X7) != (k1_xboole_0))
% 0.37/0.59          | ((X7) = (k1_xboole_0))
% 0.37/0.59          | ~ (v1_relat_1 @ X7))),
% 0.37/0.59      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.37/0.59  thf('38', plain,
% 0.37/0.59      ((((k1_xboole_0) != (k1_xboole_0))
% 0.37/0.59        | ~ (v1_relat_1 @ sk_A)
% 0.37/0.59        | ((sk_A) = (k1_xboole_0)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['36', '37'])).
% 0.37/0.59  thf('39', plain, ((v1_relat_1 @ sk_A)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('40', plain,
% 0.37/0.59      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.37/0.59      inference('demod', [status(thm)], ['38', '39'])).
% 0.37/0.59  thf('41', plain, (((sk_A) = (k1_xboole_0))),
% 0.37/0.59      inference('simplify', [status(thm)], ['40'])).
% 0.37/0.59  thf('42', plain, (((sk_A) = (k1_xboole_0))),
% 0.37/0.59      inference('simplify', [status(thm)], ['40'])).
% 0.37/0.59  thf(t60_relat_1, axiom,
% 0.37/0.59    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.37/0.59     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.37/0.59  thf('43', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.59      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.37/0.59  thf(t4_subset_1, axiom,
% 0.37/0.59    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.37/0.59  thf('44', plain,
% 0.37/0.59      (![X3 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X3))),
% 0.37/0.59      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.37/0.59  thf('45', plain,
% 0.37/0.59      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.37/0.59         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 0.37/0.59          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.37/0.59      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.37/0.59  thf('46', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.37/0.59      inference('sup-', [status(thm)], ['44', '45'])).
% 0.37/0.59  thf('47', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.59      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.37/0.59  thf('48', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.59      inference('demod', [status(thm)], ['46', '47'])).
% 0.37/0.59  thf('49', plain,
% 0.37/0.59      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.37/0.59         (((X33) != (k1_relset_1 @ X33 @ X34 @ X35))
% 0.37/0.59          | (v1_funct_2 @ X35 @ X33 @ X34)
% 0.37/0.59          | ~ (zip_tseitin_5 @ X35 @ X34 @ X33))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.37/0.59  thf('50', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         (((X1) != (k1_xboole_0))
% 0.37/0.59          | ~ (zip_tseitin_5 @ k1_xboole_0 @ X0 @ X1)
% 0.37/0.59          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 0.37/0.59      inference('sup-', [status(thm)], ['48', '49'])).
% 0.37/0.59  thf('51', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 0.37/0.59          | ~ (zip_tseitin_5 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.37/0.59      inference('simplify', [status(thm)], ['50'])).
% 0.37/0.59  thf('52', plain,
% 0.37/0.59      (![X31 : $i, X32 : $i]:
% 0.37/0.59         ((zip_tseitin_4 @ X31 @ X32) | ((X32) != (k1_xboole_0)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.37/0.59  thf('53', plain, (![X31 : $i]: (zip_tseitin_4 @ X31 @ k1_xboole_0)),
% 0.37/0.59      inference('simplify', [status(thm)], ['52'])).
% 0.37/0.59  thf('54', plain,
% 0.37/0.59      (![X3 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X3))),
% 0.37/0.59      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.37/0.59  thf('55', plain,
% 0.37/0.59      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.37/0.59         (~ (zip_tseitin_4 @ X36 @ X37)
% 0.37/0.59          | (zip_tseitin_5 @ X38 @ X36 @ X37)
% 0.37/0.59          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.37/0.59  thf('56', plain,
% 0.37/0.59      (![X0 : $i, X1 : $i]:
% 0.37/0.59         ((zip_tseitin_5 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_4 @ X0 @ X1))),
% 0.37/0.59      inference('sup-', [status(thm)], ['54', '55'])).
% 0.37/0.59  thf('57', plain,
% 0.37/0.59      (![X0 : $i]: (zip_tseitin_5 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.37/0.59      inference('sup-', [status(thm)], ['53', '56'])).
% 0.37/0.59  thf('58', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.37/0.59      inference('simplify_reflect+', [status(thm)], ['51', '57'])).
% 0.37/0.59  thf('59', plain, ($false),
% 0.37/0.59      inference('demod', [status(thm)], ['35', '41', '42', '43', '58'])).
% 0.37/0.59  
% 0.37/0.59  % SZS output end Refutation
% 0.37/0.59  
% 0.37/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
