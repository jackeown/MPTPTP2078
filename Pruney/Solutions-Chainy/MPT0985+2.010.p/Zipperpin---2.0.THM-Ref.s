%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2vxL0gRkPp

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:28 EST 2020

% Result     : Theorem 6.34s
% Output     : Refutation 6.34s
% Verified   : 
% Statistics : Number of formulae       :  272 (2252 expanded)
%              Number of leaves         :   50 ( 711 expanded)
%              Depth                    :   27
%              Number of atoms          : 1811 (31402 expanded)
%              Number of equality atoms :  111 (1230 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(v5_ordinal1_type,type,(
    v5_ordinal1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_funct_1 @ X18 )
        = ( k4_relat_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('6',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v1_relat_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('7',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['4','7','8'])).

thf('10',plain,
    ( ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B_1 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['1','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('12',plain,(
    ! [X19: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('13',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['4','7','8'])).

thf('19',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('20',plain,
    ( ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('22',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['21'])).

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

thf('23',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('24',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('25',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('26',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( r1_tarski @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','28'])).

thf(fc14_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( ( v1_xboole_0 @ ( k4_relat_1 @ A ) )
        & ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) ) )).

thf('30',plain,(
    ! [X15: $i] :
      ( ( v1_xboole_0 @ ( k4_relat_1 @ X15 ) )
      | ~ ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc14_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('31',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('32',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('33',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X41 ) @ X42 )
      | ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X41 ) @ X42 ) ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t45_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v5_ordinal1 @ k1_xboole_0 )
      & ( v1_funct_1 @ k1_xboole_0 )
      & ( v5_relat_1 @ k1_xboole_0 @ A )
      & ( v1_relat_1 @ k1_xboole_0 ) ) )).

thf('36',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('37',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('38',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

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

thf('41',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35','36','37','38','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','41'])).

thf('43',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('44',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('47',plain,
    ( ( ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ sk_B_1 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ~ ( v1_xboole_0 @ ( k4_relat_1 @ sk_C ) )
      | ~ ( v1_xboole_0 @ sk_B_1 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,
    ( ( ~ ( v1_xboole_0 @ sk_C )
      | ~ ( v1_xboole_0 @ sk_B_1 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['30','48'])).

thf('50',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('51',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('52',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','52'])).

thf('54',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('56',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ( r2_hidden @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r2_hidden @ ( sk_B @ sk_C ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('60',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['53','60'])).

thf('62',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['24','27'])).

thf('63',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['49','63'])).

thf('65',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ sk_B_1 @ X0 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['29','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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

thf('67',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X39 )
      | ( zip_tseitin_1 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('68',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ( X35
        = ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ~ ( zip_tseitin_1 @ X37 @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('72',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('74',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('75',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['72','75'])).

thf('77',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['69','76'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('78',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k1_relat_1 @ X20 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('79',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X41 ) @ X42 )
      | ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X41 ) @ X42 ) ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_A @ X0 )
        | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 ) ) )
        | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
        | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
        | ~ ( v2_funct_1 @ sk_C )
        | ~ ( v1_funct_1 @ sk_C )
        | ~ ( v1_relat_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('82',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['4','7','8'])).

thf('83',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['4','7','8'])).

thf('84',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['4','7','8'])).

thf('85',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_relat_1 @ X20 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('86',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf('88',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['86','87','88','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('92',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k2_relset_1 @ X31 @ X32 @ X30 )
        = ( k2_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('93',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C )
    = sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,
    ( sk_B_1
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['90','95'])).

thf('97',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['4','7','8'])).

thf('98',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['4','7','8'])).

thf('99',plain,(
    ! [X19: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('100',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf('102',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['4','7','8'])).

thf('105',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['4','7','8'])).

thf('106',plain,(
    ! [X19: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('107',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf('109',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf('114',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_A @ X0 )
        | ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ X0 ) ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['81','82','83','96','97','103','104','110','111','112','113'])).

thf('115',plain,
    ( ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['22','114'])).

thf('116',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','115'])).

thf('117',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('118',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['17','116','117'])).

thf('119',plain,(
    ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['10','118'])).

thf('120',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['4','7','8'])).

thf('121',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k1_relat_1 @ X20 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('122',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['5','6'])).

thf('124',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['122','123','124','125'])).

thf('127',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('128',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('129',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X41 ) @ X42 )
      | ( v1_funct_2 @ X41 @ ( k1_relat_1 @ X41 ) @ X42 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('130',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('132',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('133',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('134',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('135',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['130','131','132','133','134'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['127','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','28'])).

thf('138',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('139',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['72','75'])).

thf('141',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('143',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('145',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('146',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_funct_1 @ X18 )
        = ( k4_relat_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('147',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k2_funct_1 @ k1_xboole_0 )
      = ( k4_relat_1 @ k1_xboole_0 ) )
    | ~ ( v2_funct_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('149',plain,
    ( ( ( k2_funct_1 @ k1_xboole_0 )
      = ( k4_relat_1 @ k1_xboole_0 ) )
    | ~ ( v2_funct_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['24','27'])).

thf('151',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('152',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf(cc2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) ) ) )).

thf('153',plain,(
    ! [X17: $i] :
      ( ( v2_funct_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_1])).

thf('154',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( v2_funct_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('156',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v2_funct_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v2_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['151','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['157'])).

thf('159',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['150','158'])).

thf('160',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = ( k4_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['149','159'])).

thf('161',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['24','27'])).

thf('162',plain,(
    ! [X15: $i] :
      ( ( v1_xboole_0 @ ( k4_relat_1 @ X15 ) )
      | ~ ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc14_relat_1])).

thf('163',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('164',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k4_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['161','164'])).

thf('166',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['160','165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['144','166'])).

thf('168',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
    | ( ( k2_funct_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['143','167'])).

thf('169',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('170',plain,
    ( ( ~ ( v1_funct_2 @ k1_xboole_0 @ sk_B_1 @ sk_A )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,
    ( ( ~ ( v1_xboole_0 @ sk_B_1 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['136','170'])).

thf('172',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('173',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['171','172'])).

thf('174',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['17','116','117'])).

thf('175',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['173','174'])).

thf('176',plain,
    ( sk_A
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['126','175'])).

thf('177',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('178',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X41 ) @ X42 )
      | ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X41 ) @ X42 ) ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('179',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,
    ( ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['176','179'])).

thf('181',plain,
    ( sk_B_1
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['90','95'])).

thf('182',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('183',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('184',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['180','181','182','183'])).

thf('185',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('186',plain,
    ( ( k1_relset_1 @ sk_B_1 @ sk_A @ ( k4_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,
    ( sk_B_1
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['90','95'])).

thf('188',plain,
    ( ( k1_relset_1 @ sk_B_1 @ sk_A @ ( k4_relat_1 @ sk_C ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['186','187'])).

thf('189',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( X35
       != ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ~ ( zip_tseitin_1 @ X37 @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('190',plain,
    ( ( sk_B_1 != sk_B_1 )
    | ~ ( zip_tseitin_1 @ ( k4_relat_1 @ sk_C ) @ sk_A @ sk_B_1 )
    | ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['180','181','182','183'])).

thf('192',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X39 )
      | ( zip_tseitin_1 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('193',plain,
    ( ( zip_tseitin_1 @ ( k4_relat_1 @ sk_C ) @ sk_A @ sk_B_1 )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['191','192'])).

thf('194',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','28'])).

thf('195',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('196',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('197',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['24','27'])).

thf('199',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['197','198'])).

thf('200',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['194','199'])).

thf('201',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['144','166'])).

thf('202',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['127','135'])).

thf('203',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ X2 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['201','202'])).

thf('204',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('205',plain,
    ( ( ~ ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ sk_C ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['203','204'])).

thf('206',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['93','94'])).

thf('207',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('208',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('209',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['207','208'])).

thf('210',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['24','27'])).

thf('211',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['209','210'])).

thf('212',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['206','211'])).

thf('213',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['205','212'])).

thf('214',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ sk_A @ X0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['200','213'])).

thf('215',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['17','116','117'])).

thf('216',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_A @ X0 ) ),
    inference(simpl_trail,[status(thm)],['214','215'])).

thf('217',plain,(
    zip_tseitin_1 @ ( k4_relat_1 @ sk_C ) @ sk_A @ sk_B_1 ),
    inference(demod,[status(thm)],['193','216'])).

thf('218',plain,
    ( ( sk_B_1 != sk_B_1 )
    | ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['190','217'])).

thf('219',plain,(
    v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B_1 @ sk_A ),
    inference(simplify,[status(thm)],['218'])).

thf('220',plain,(
    $false ),
    inference(demod,[status(thm)],['119','219'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2vxL0gRkPp
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:44:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 6.34/6.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.34/6.50  % Solved by: fo/fo7.sh
% 6.34/6.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.34/6.50  % done 6860 iterations in 6.055s
% 6.34/6.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.34/6.50  % SZS output start Refutation
% 6.34/6.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 6.34/6.50  thf(sk_B_type, type, sk_B: $i > $i).
% 6.34/6.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 6.34/6.50  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 6.34/6.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.34/6.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 6.34/6.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 6.34/6.50  thf(sk_A_type, type, sk_A: $i).
% 6.34/6.50  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 6.34/6.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 6.34/6.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 6.34/6.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 6.34/6.50  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 6.34/6.50  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 6.34/6.50  thf(v5_ordinal1_type, type, v5_ordinal1: $i > $o).
% 6.34/6.50  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 6.34/6.50  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 6.34/6.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 6.34/6.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.34/6.50  thf(sk_C_type, type, sk_C: $i).
% 6.34/6.50  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 6.34/6.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.34/6.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 6.34/6.50  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 6.34/6.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.34/6.50  thf(t31_funct_2, conjecture,
% 6.34/6.50    (![A:$i,B:$i,C:$i]:
% 6.34/6.50     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 6.34/6.50         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.34/6.50       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 6.34/6.50         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 6.34/6.50           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 6.34/6.50           ( m1_subset_1 @
% 6.34/6.50             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 6.34/6.50  thf(zf_stmt_0, negated_conjecture,
% 6.34/6.50    (~( ![A:$i,B:$i,C:$i]:
% 6.34/6.50        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 6.34/6.50            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.34/6.50          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 6.34/6.50            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 6.34/6.50              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 6.34/6.50              ( m1_subset_1 @
% 6.34/6.50                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 6.34/6.50    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 6.34/6.50  thf('0', plain,
% 6.34/6.50      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 6.34/6.50        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)
% 6.34/6.50        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.34/6.50             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))),
% 6.34/6.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.34/6.50  thf('1', plain,
% 6.34/6.50      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A))
% 6.34/6.50         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 6.34/6.50      inference('split', [status(esa)], ['0'])).
% 6.34/6.50  thf('2', plain, ((v1_funct_1 @ sk_C)),
% 6.34/6.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.34/6.50  thf(d9_funct_1, axiom,
% 6.34/6.50    (![A:$i]:
% 6.34/6.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 6.34/6.50       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 6.34/6.50  thf('3', plain,
% 6.34/6.50      (![X18 : $i]:
% 6.34/6.50         (~ (v2_funct_1 @ X18)
% 6.34/6.50          | ((k2_funct_1 @ X18) = (k4_relat_1 @ X18))
% 6.34/6.50          | ~ (v1_funct_1 @ X18)
% 6.34/6.50          | ~ (v1_relat_1 @ X18))),
% 6.34/6.50      inference('cnf', [status(esa)], [d9_funct_1])).
% 6.34/6.50  thf('4', plain,
% 6.34/6.50      ((~ (v1_relat_1 @ sk_C)
% 6.34/6.50        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 6.34/6.50        | ~ (v2_funct_1 @ sk_C))),
% 6.34/6.50      inference('sup-', [status(thm)], ['2', '3'])).
% 6.34/6.50  thf('5', plain,
% 6.34/6.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.34/6.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.34/6.50  thf(cc1_relset_1, axiom,
% 6.34/6.50    (![A:$i,B:$i,C:$i]:
% 6.34/6.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.34/6.50       ( v1_relat_1 @ C ) ))).
% 6.34/6.50  thf('6', plain,
% 6.34/6.50      (![X24 : $i, X25 : $i, X26 : $i]:
% 6.34/6.50         ((v1_relat_1 @ X24)
% 6.34/6.50          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 6.34/6.50      inference('cnf', [status(esa)], [cc1_relset_1])).
% 6.34/6.50  thf('7', plain, ((v1_relat_1 @ sk_C)),
% 6.34/6.50      inference('sup-', [status(thm)], ['5', '6'])).
% 6.34/6.50  thf('8', plain, ((v2_funct_1 @ sk_C)),
% 6.34/6.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.34/6.50  thf('9', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 6.34/6.50      inference('demod', [status(thm)], ['4', '7', '8'])).
% 6.34/6.50  thf('10', plain,
% 6.34/6.50      ((~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B_1 @ sk_A))
% 6.34/6.50         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 6.34/6.50      inference('demod', [status(thm)], ['1', '9'])).
% 6.34/6.50  thf('11', plain, ((v1_relat_1 @ sk_C)),
% 6.34/6.50      inference('sup-', [status(thm)], ['5', '6'])).
% 6.34/6.50  thf(dt_k2_funct_1, axiom,
% 6.34/6.50    (![A:$i]:
% 6.34/6.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 6.34/6.50       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 6.34/6.50         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 6.34/6.50  thf('12', plain,
% 6.34/6.50      (![X19 : $i]:
% 6.34/6.50         ((v1_funct_1 @ (k2_funct_1 @ X19))
% 6.34/6.50          | ~ (v1_funct_1 @ X19)
% 6.34/6.50          | ~ (v1_relat_1 @ X19))),
% 6.34/6.50      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.34/6.50  thf('13', plain,
% 6.34/6.50      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 6.34/6.50         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 6.34/6.50      inference('split', [status(esa)], ['0'])).
% 6.34/6.50  thf('14', plain,
% 6.34/6.50      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 6.34/6.50         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 6.34/6.50      inference('sup-', [status(thm)], ['12', '13'])).
% 6.34/6.50  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 6.34/6.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.34/6.50  thf('16', plain,
% 6.34/6.50      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 6.34/6.50      inference('demod', [status(thm)], ['14', '15'])).
% 6.34/6.50  thf('17', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 6.34/6.50      inference('sup-', [status(thm)], ['11', '16'])).
% 6.34/6.50  thf('18', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 6.34/6.50      inference('demod', [status(thm)], ['4', '7', '8'])).
% 6.34/6.50  thf('19', plain,
% 6.34/6.50      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.34/6.50           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))
% 6.34/6.50         <= (~
% 6.34/6.50             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.34/6.50               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 6.34/6.50      inference('split', [status(esa)], ['0'])).
% 6.34/6.50  thf('20', plain,
% 6.34/6.50      ((~ (m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 6.34/6.50           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))
% 6.34/6.50         <= (~
% 6.34/6.50             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.34/6.50               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 6.34/6.50      inference('sup-', [status(thm)], ['18', '19'])).
% 6.34/6.50  thf(d10_xboole_0, axiom,
% 6.34/6.50    (![A:$i,B:$i]:
% 6.34/6.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 6.34/6.50  thf('21', plain,
% 6.34/6.50      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 6.34/6.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.34/6.50  thf('22', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 6.34/6.50      inference('simplify', [status(thm)], ['21'])).
% 6.34/6.50  thf(d1_funct_2, axiom,
% 6.34/6.50    (![A:$i,B:$i,C:$i]:
% 6.34/6.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.34/6.50       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 6.34/6.50           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 6.34/6.50             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 6.34/6.50         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 6.34/6.50           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 6.34/6.50             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 6.34/6.50  thf(zf_stmt_1, axiom,
% 6.34/6.50    (![B:$i,A:$i]:
% 6.34/6.50     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 6.34/6.50       ( zip_tseitin_0 @ B @ A ) ))).
% 6.34/6.50  thf('23', plain,
% 6.34/6.50      (![X33 : $i, X34 : $i]:
% 6.34/6.50         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 6.34/6.50      inference('cnf', [status(esa)], [zf_stmt_1])).
% 6.34/6.50  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 6.34/6.50  thf('24', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 6.34/6.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 6.34/6.50  thf(d1_xboole_0, axiom,
% 6.34/6.50    (![A:$i]:
% 6.34/6.50     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 6.34/6.50  thf('25', plain,
% 6.34/6.50      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 6.34/6.50      inference('cnf', [status(esa)], [d1_xboole_0])).
% 6.34/6.50  thf(t7_ordinal1, axiom,
% 6.34/6.50    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 6.34/6.50  thf('26', plain,
% 6.34/6.50      (![X22 : $i, X23 : $i]:
% 6.34/6.50         (~ (r2_hidden @ X22 @ X23) | ~ (r1_tarski @ X23 @ X22))),
% 6.34/6.50      inference('cnf', [status(esa)], [t7_ordinal1])).
% 6.34/6.50  thf('27', plain,
% 6.34/6.50      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 6.34/6.50      inference('sup-', [status(thm)], ['25', '26'])).
% 6.34/6.50  thf('28', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.34/6.50      inference('sup-', [status(thm)], ['24', '27'])).
% 6.34/6.50  thf('29', plain,
% 6.34/6.50      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 6.34/6.50      inference('sup+', [status(thm)], ['23', '28'])).
% 6.34/6.50  thf(fc14_relat_1, axiom,
% 6.34/6.50    (![A:$i]:
% 6.34/6.50     ( ( v1_xboole_0 @ A ) =>
% 6.34/6.50       ( ( v1_xboole_0 @ ( k4_relat_1 @ A ) ) & 
% 6.34/6.50         ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) ))).
% 6.34/6.50  thf('30', plain,
% 6.34/6.50      (![X15 : $i]:
% 6.34/6.50         ((v1_xboole_0 @ (k4_relat_1 @ X15)) | ~ (v1_xboole_0 @ X15))),
% 6.34/6.50      inference('cnf', [status(esa)], [fc14_relat_1])).
% 6.34/6.50  thf(l13_xboole_0, axiom,
% 6.34/6.50    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 6.34/6.50  thf('31', plain,
% 6.34/6.50      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 6.34/6.50      inference('cnf', [status(esa)], [l13_xboole_0])).
% 6.34/6.50  thf(t60_relat_1, axiom,
% 6.34/6.50    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 6.34/6.50     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 6.34/6.50  thf('32', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 6.34/6.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 6.34/6.50  thf(t4_funct_2, axiom,
% 6.34/6.50    (![A:$i,B:$i]:
% 6.34/6.50     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 6.34/6.50       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 6.34/6.50         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 6.34/6.50           ( m1_subset_1 @
% 6.34/6.50             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 6.34/6.50  thf('33', plain,
% 6.34/6.50      (![X41 : $i, X42 : $i]:
% 6.34/6.50         (~ (r1_tarski @ (k2_relat_1 @ X41) @ X42)
% 6.34/6.50          | (m1_subset_1 @ X41 @ 
% 6.34/6.50             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X41) @ X42)))
% 6.34/6.50          | ~ (v1_funct_1 @ X41)
% 6.34/6.50          | ~ (v1_relat_1 @ X41))),
% 6.34/6.50      inference('cnf', [status(esa)], [t4_funct_2])).
% 6.34/6.50  thf('34', plain,
% 6.34/6.50      (![X0 : $i]:
% 6.34/6.50         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 6.34/6.50          | ~ (v1_relat_1 @ k1_xboole_0)
% 6.34/6.50          | ~ (v1_funct_1 @ k1_xboole_0)
% 6.34/6.50          | (m1_subset_1 @ k1_xboole_0 @ 
% 6.34/6.50             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ k1_xboole_0) @ X0))))),
% 6.34/6.50      inference('sup-', [status(thm)], ['32', '33'])).
% 6.34/6.50  thf('35', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 6.34/6.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 6.34/6.50  thf(t45_ordinal1, axiom,
% 6.34/6.50    (![A:$i]:
% 6.34/6.50     ( ( v5_ordinal1 @ k1_xboole_0 ) & ( v1_funct_1 @ k1_xboole_0 ) & 
% 6.34/6.50       ( v5_relat_1 @ k1_xboole_0 @ A ) & ( v1_relat_1 @ k1_xboole_0 ) ))).
% 6.34/6.50  thf('36', plain, ((v1_relat_1 @ k1_xboole_0)),
% 6.34/6.50      inference('cnf', [status(esa)], [t45_ordinal1])).
% 6.34/6.50  thf('37', plain, ((v1_funct_1 @ k1_xboole_0)),
% 6.34/6.50      inference('cnf', [status(esa)], [t45_ordinal1])).
% 6.34/6.50  thf('38', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 6.34/6.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 6.34/6.50  thf(t113_zfmisc_1, axiom,
% 6.34/6.50    (![A:$i,B:$i]:
% 6.34/6.50     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 6.34/6.50       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 6.34/6.50  thf('39', plain,
% 6.34/6.50      (![X9 : $i, X10 : $i]:
% 6.34/6.50         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 6.34/6.50      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 6.34/6.50  thf('40', plain,
% 6.34/6.50      (![X10 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 6.34/6.50      inference('simplify', [status(thm)], ['39'])).
% 6.34/6.50  thf('41', plain, ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 6.34/6.50      inference('demod', [status(thm)], ['34', '35', '36', '37', '38', '40'])).
% 6.34/6.50  thf('42', plain,
% 6.34/6.50      (![X0 : $i]:
% 6.34/6.50         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 6.34/6.50          | ~ (v1_xboole_0 @ X0))),
% 6.34/6.50      inference('sup+', [status(thm)], ['31', '41'])).
% 6.34/6.50  thf('43', plain,
% 6.34/6.50      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 6.34/6.50      inference('cnf', [status(esa)], [l13_xboole_0])).
% 6.34/6.50  thf('44', plain,
% 6.34/6.50      (![X10 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 6.34/6.50      inference('simplify', [status(thm)], ['39'])).
% 6.34/6.50  thf('45', plain,
% 6.34/6.50      (![X0 : $i, X1 : $i]:
% 6.34/6.50         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.34/6.50      inference('sup+', [status(thm)], ['43', '44'])).
% 6.34/6.50  thf('46', plain,
% 6.34/6.50      ((~ (m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 6.34/6.50           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))
% 6.34/6.50         <= (~
% 6.34/6.50             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.34/6.50               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 6.34/6.50      inference('sup-', [status(thm)], ['18', '19'])).
% 6.34/6.50  thf('47', plain,
% 6.34/6.50      (((~ (m1_subset_1 @ (k4_relat_1 @ sk_C) @ (k1_zfmisc_1 @ k1_xboole_0))
% 6.34/6.50         | ~ (v1_xboole_0 @ sk_B_1)))
% 6.34/6.50         <= (~
% 6.34/6.50             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.34/6.50               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 6.34/6.50      inference('sup-', [status(thm)], ['45', '46'])).
% 6.34/6.50  thf('48', plain,
% 6.34/6.50      (((~ (v1_xboole_0 @ (k4_relat_1 @ sk_C)) | ~ (v1_xboole_0 @ sk_B_1)))
% 6.34/6.50         <= (~
% 6.34/6.50             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.34/6.50               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 6.34/6.50      inference('sup-', [status(thm)], ['42', '47'])).
% 6.34/6.50  thf('49', plain,
% 6.34/6.50      (((~ (v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_B_1)))
% 6.34/6.50         <= (~
% 6.34/6.50             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.34/6.50               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 6.34/6.50      inference('sup-', [status(thm)], ['30', '48'])).
% 6.34/6.50  thf('50', plain,
% 6.34/6.50      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 6.34/6.50      inference('cnf', [status(esa)], [l13_xboole_0])).
% 6.34/6.50  thf('51', plain,
% 6.34/6.50      (![X9 : $i, X10 : $i]:
% 6.34/6.50         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X10) != (k1_xboole_0)))),
% 6.34/6.50      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 6.34/6.50  thf('52', plain,
% 6.34/6.50      (![X9 : $i]: ((k2_zfmisc_1 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 6.34/6.50      inference('simplify', [status(thm)], ['51'])).
% 6.34/6.50  thf('53', plain,
% 6.34/6.50      (![X0 : $i, X1 : $i]:
% 6.34/6.50         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.34/6.50      inference('sup+', [status(thm)], ['50', '52'])).
% 6.34/6.50  thf('54', plain,
% 6.34/6.50      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 6.34/6.50      inference('cnf', [status(esa)], [d1_xboole_0])).
% 6.34/6.50  thf('55', plain,
% 6.34/6.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.34/6.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.34/6.50  thf(l3_subset_1, axiom,
% 6.34/6.50    (![A:$i,B:$i]:
% 6.34/6.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 6.34/6.50       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 6.34/6.50  thf('56', plain,
% 6.34/6.50      (![X11 : $i, X12 : $i, X13 : $i]:
% 6.34/6.50         (~ (r2_hidden @ X11 @ X12)
% 6.34/6.50          | (r2_hidden @ X11 @ X13)
% 6.34/6.50          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 6.34/6.50      inference('cnf', [status(esa)], [l3_subset_1])).
% 6.34/6.50  thf('57', plain,
% 6.34/6.50      (![X0 : $i]:
% 6.34/6.50         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 6.34/6.50          | ~ (r2_hidden @ X0 @ sk_C))),
% 6.34/6.50      inference('sup-', [status(thm)], ['55', '56'])).
% 6.34/6.50  thf('58', plain,
% 6.34/6.50      (((v1_xboole_0 @ sk_C)
% 6.34/6.50        | (r2_hidden @ (sk_B @ sk_C) @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.34/6.50      inference('sup-', [status(thm)], ['54', '57'])).
% 6.34/6.50  thf('59', plain,
% 6.34/6.50      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 6.34/6.50      inference('cnf', [status(esa)], [d1_xboole_0])).
% 6.34/6.50  thf('60', plain,
% 6.34/6.50      (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.34/6.50      inference('sup-', [status(thm)], ['58', '59'])).
% 6.34/6.50  thf('61', plain,
% 6.34/6.50      ((~ (v1_xboole_0 @ k1_xboole_0)
% 6.34/6.50        | ~ (v1_xboole_0 @ sk_B_1)
% 6.34/6.50        | (v1_xboole_0 @ sk_C))),
% 6.34/6.50      inference('sup-', [status(thm)], ['53', '60'])).
% 6.34/6.50  thf('62', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.34/6.50      inference('sup-', [status(thm)], ['24', '27'])).
% 6.34/6.50  thf('63', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_C))),
% 6.34/6.50      inference('demod', [status(thm)], ['61', '62'])).
% 6.34/6.50  thf('64', plain,
% 6.34/6.50      ((~ (v1_xboole_0 @ sk_B_1))
% 6.34/6.50         <= (~
% 6.34/6.50             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.34/6.50               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 6.34/6.50      inference('clc', [status(thm)], ['49', '63'])).
% 6.34/6.50  thf('65', plain,
% 6.34/6.50      ((![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0))
% 6.34/6.50         <= (~
% 6.34/6.50             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.34/6.50               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 6.34/6.50      inference('sup-', [status(thm)], ['29', '64'])).
% 6.34/6.50  thf('66', plain,
% 6.34/6.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.34/6.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.34/6.50  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 6.34/6.50  thf(zf_stmt_3, axiom,
% 6.34/6.50    (![C:$i,B:$i,A:$i]:
% 6.34/6.50     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 6.34/6.50       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 6.34/6.50  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 6.34/6.50  thf(zf_stmt_5, axiom,
% 6.34/6.50    (![A:$i,B:$i,C:$i]:
% 6.34/6.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.34/6.50       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 6.34/6.50         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 6.34/6.50           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 6.34/6.50             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 6.34/6.50  thf('67', plain,
% 6.34/6.50      (![X38 : $i, X39 : $i, X40 : $i]:
% 6.34/6.50         (~ (zip_tseitin_0 @ X38 @ X39)
% 6.34/6.50          | (zip_tseitin_1 @ X40 @ X38 @ X39)
% 6.34/6.50          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 6.34/6.50      inference('cnf', [status(esa)], [zf_stmt_5])).
% 6.34/6.50  thf('68', plain,
% 6.34/6.50      (((zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 6.34/6.50        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 6.34/6.50      inference('sup-', [status(thm)], ['66', '67'])).
% 6.34/6.50  thf('69', plain,
% 6.34/6.50      (((zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A))
% 6.34/6.50         <= (~
% 6.34/6.50             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.34/6.50               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 6.34/6.50      inference('sup-', [status(thm)], ['65', '68'])).
% 6.34/6.50  thf('70', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 6.34/6.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.34/6.50  thf('71', plain,
% 6.34/6.50      (![X35 : $i, X36 : $i, X37 : $i]:
% 6.34/6.50         (~ (v1_funct_2 @ X37 @ X35 @ X36)
% 6.34/6.50          | ((X35) = (k1_relset_1 @ X35 @ X36 @ X37))
% 6.34/6.50          | ~ (zip_tseitin_1 @ X37 @ X36 @ X35))),
% 6.34/6.50      inference('cnf', [status(esa)], [zf_stmt_3])).
% 6.34/6.50  thf('72', plain,
% 6.34/6.50      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 6.34/6.50        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C)))),
% 6.34/6.50      inference('sup-', [status(thm)], ['70', '71'])).
% 6.34/6.50  thf('73', plain,
% 6.34/6.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.34/6.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.34/6.50  thf(redefinition_k1_relset_1, axiom,
% 6.34/6.50    (![A:$i,B:$i,C:$i]:
% 6.34/6.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.34/6.50       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 6.34/6.50  thf('74', plain,
% 6.34/6.50      (![X27 : $i, X28 : $i, X29 : $i]:
% 6.34/6.50         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 6.34/6.50          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 6.34/6.50      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 6.34/6.50  thf('75', plain,
% 6.34/6.50      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (k1_relat_1 @ sk_C))),
% 6.34/6.50      inference('sup-', [status(thm)], ['73', '74'])).
% 6.34/6.50  thf('76', plain,
% 6.34/6.50      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 6.34/6.50        | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 6.34/6.50      inference('demod', [status(thm)], ['72', '75'])).
% 6.34/6.50  thf('77', plain,
% 6.34/6.50      ((((sk_A) = (k1_relat_1 @ sk_C)))
% 6.34/6.50         <= (~
% 6.34/6.50             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.34/6.50               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 6.34/6.50      inference('sup-', [status(thm)], ['69', '76'])).
% 6.34/6.50  thf(t55_funct_1, axiom,
% 6.34/6.50    (![A:$i]:
% 6.34/6.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 6.34/6.50       ( ( v2_funct_1 @ A ) =>
% 6.34/6.50         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 6.34/6.50           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 6.34/6.50  thf('78', plain,
% 6.34/6.50      (![X20 : $i]:
% 6.34/6.50         (~ (v2_funct_1 @ X20)
% 6.34/6.50          | ((k1_relat_1 @ X20) = (k2_relat_1 @ (k2_funct_1 @ X20)))
% 6.34/6.50          | ~ (v1_funct_1 @ X20)
% 6.34/6.50          | ~ (v1_relat_1 @ X20))),
% 6.34/6.50      inference('cnf', [status(esa)], [t55_funct_1])).
% 6.34/6.50  thf('79', plain,
% 6.34/6.50      (![X41 : $i, X42 : $i]:
% 6.34/6.50         (~ (r1_tarski @ (k2_relat_1 @ X41) @ X42)
% 6.34/6.50          | (m1_subset_1 @ X41 @ 
% 6.34/6.50             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X41) @ X42)))
% 6.34/6.50          | ~ (v1_funct_1 @ X41)
% 6.34/6.50          | ~ (v1_relat_1 @ X41))),
% 6.34/6.50      inference('cnf', [status(esa)], [t4_funct_2])).
% 6.34/6.50  thf('80', plain,
% 6.34/6.50      (![X0 : $i, X1 : $i]:
% 6.34/6.50         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 6.34/6.50          | ~ (v1_relat_1 @ X0)
% 6.34/6.50          | ~ (v1_funct_1 @ X0)
% 6.34/6.50          | ~ (v2_funct_1 @ X0)
% 6.34/6.50          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 6.34/6.50          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.34/6.50          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 6.34/6.50             (k1_zfmisc_1 @ 
% 6.34/6.50              (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ X1))))),
% 6.34/6.50      inference('sup-', [status(thm)], ['78', '79'])).
% 6.34/6.50  thf('81', plain,
% 6.34/6.50      ((![X0 : $i]:
% 6.34/6.50          (~ (r1_tarski @ sk_A @ X0)
% 6.34/6.50           | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.34/6.50              (k1_zfmisc_1 @ 
% 6.34/6.50               (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)))
% 6.34/6.50           | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 6.34/6.50           | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 6.34/6.50           | ~ (v2_funct_1 @ sk_C)
% 6.34/6.50           | ~ (v1_funct_1 @ sk_C)
% 6.34/6.50           | ~ (v1_relat_1 @ sk_C)))
% 6.34/6.50         <= (~
% 6.34/6.50             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.34/6.50               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 6.34/6.50      inference('sup-', [status(thm)], ['77', '80'])).
% 6.34/6.50  thf('82', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 6.34/6.50      inference('demod', [status(thm)], ['4', '7', '8'])).
% 6.34/6.50  thf('83', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 6.34/6.50      inference('demod', [status(thm)], ['4', '7', '8'])).
% 6.34/6.50  thf('84', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 6.34/6.50      inference('demod', [status(thm)], ['4', '7', '8'])).
% 6.34/6.50  thf('85', plain,
% 6.34/6.50      (![X20 : $i]:
% 6.34/6.50         (~ (v2_funct_1 @ X20)
% 6.34/6.50          | ((k2_relat_1 @ X20) = (k1_relat_1 @ (k2_funct_1 @ X20)))
% 6.34/6.50          | ~ (v1_funct_1 @ X20)
% 6.34/6.50          | ~ (v1_relat_1 @ X20))),
% 6.34/6.50      inference('cnf', [status(esa)], [t55_funct_1])).
% 6.34/6.50  thf('86', plain,
% 6.34/6.50      ((((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))
% 6.34/6.50        | ~ (v1_relat_1 @ sk_C)
% 6.34/6.50        | ~ (v1_funct_1 @ sk_C)
% 6.34/6.50        | ~ (v2_funct_1 @ sk_C))),
% 6.34/6.50      inference('sup+', [status(thm)], ['84', '85'])).
% 6.34/6.50  thf('87', plain, ((v1_relat_1 @ sk_C)),
% 6.34/6.50      inference('sup-', [status(thm)], ['5', '6'])).
% 6.34/6.50  thf('88', plain, ((v1_funct_1 @ sk_C)),
% 6.34/6.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.34/6.50  thf('89', plain, ((v2_funct_1 @ sk_C)),
% 6.34/6.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.34/6.50  thf('90', plain,
% 6.34/6.50      (((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 6.34/6.50      inference('demod', [status(thm)], ['86', '87', '88', '89'])).
% 6.34/6.50  thf('91', plain,
% 6.34/6.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.34/6.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.34/6.50  thf(redefinition_k2_relset_1, axiom,
% 6.34/6.50    (![A:$i,B:$i,C:$i]:
% 6.34/6.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.34/6.50       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 6.34/6.50  thf('92', plain,
% 6.34/6.50      (![X30 : $i, X31 : $i, X32 : $i]:
% 6.34/6.50         (((k2_relset_1 @ X31 @ X32 @ X30) = (k2_relat_1 @ X30))
% 6.34/6.50          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 6.34/6.50      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 6.34/6.50  thf('93', plain,
% 6.34/6.50      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (k2_relat_1 @ sk_C))),
% 6.34/6.50      inference('sup-', [status(thm)], ['91', '92'])).
% 6.34/6.50  thf('94', plain, (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (sk_B_1))),
% 6.34/6.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.34/6.50  thf('95', plain, (((k2_relat_1 @ sk_C) = (sk_B_1))),
% 6.34/6.50      inference('sup+', [status(thm)], ['93', '94'])).
% 6.34/6.50  thf('96', plain, (((sk_B_1) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 6.34/6.50      inference('demod', [status(thm)], ['90', '95'])).
% 6.34/6.50  thf('97', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 6.34/6.50      inference('demod', [status(thm)], ['4', '7', '8'])).
% 6.34/6.50  thf('98', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 6.34/6.50      inference('demod', [status(thm)], ['4', '7', '8'])).
% 6.34/6.50  thf('99', plain,
% 6.34/6.50      (![X19 : $i]:
% 6.34/6.50         ((v1_funct_1 @ (k2_funct_1 @ X19))
% 6.34/6.50          | ~ (v1_funct_1 @ X19)
% 6.34/6.50          | ~ (v1_relat_1 @ X19))),
% 6.34/6.50      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.34/6.50  thf('100', plain,
% 6.34/6.50      (((v1_funct_1 @ (k4_relat_1 @ sk_C))
% 6.34/6.50        | ~ (v1_relat_1 @ sk_C)
% 6.34/6.50        | ~ (v1_funct_1 @ sk_C))),
% 6.34/6.50      inference('sup+', [status(thm)], ['98', '99'])).
% 6.34/6.50  thf('101', plain, ((v1_relat_1 @ sk_C)),
% 6.34/6.50      inference('sup-', [status(thm)], ['5', '6'])).
% 6.34/6.50  thf('102', plain, ((v1_funct_1 @ sk_C)),
% 6.34/6.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.34/6.50  thf('103', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 6.34/6.50      inference('demod', [status(thm)], ['100', '101', '102'])).
% 6.34/6.50  thf('104', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 6.34/6.50      inference('demod', [status(thm)], ['4', '7', '8'])).
% 6.34/6.50  thf('105', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 6.34/6.50      inference('demod', [status(thm)], ['4', '7', '8'])).
% 6.34/6.50  thf('106', plain,
% 6.34/6.50      (![X19 : $i]:
% 6.34/6.50         ((v1_relat_1 @ (k2_funct_1 @ X19))
% 6.34/6.50          | ~ (v1_funct_1 @ X19)
% 6.34/6.50          | ~ (v1_relat_1 @ X19))),
% 6.34/6.50      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.34/6.50  thf('107', plain,
% 6.34/6.50      (((v1_relat_1 @ (k4_relat_1 @ sk_C))
% 6.34/6.50        | ~ (v1_relat_1 @ sk_C)
% 6.34/6.50        | ~ (v1_funct_1 @ sk_C))),
% 6.34/6.50      inference('sup+', [status(thm)], ['105', '106'])).
% 6.34/6.50  thf('108', plain, ((v1_relat_1 @ sk_C)),
% 6.34/6.50      inference('sup-', [status(thm)], ['5', '6'])).
% 6.34/6.50  thf('109', plain, ((v1_funct_1 @ sk_C)),
% 6.34/6.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.34/6.50  thf('110', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 6.34/6.50      inference('demod', [status(thm)], ['107', '108', '109'])).
% 6.34/6.50  thf('111', plain, ((v2_funct_1 @ sk_C)),
% 6.34/6.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.34/6.50  thf('112', plain, ((v1_funct_1 @ sk_C)),
% 6.34/6.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.34/6.50  thf('113', plain, ((v1_relat_1 @ sk_C)),
% 6.34/6.50      inference('sup-', [status(thm)], ['5', '6'])).
% 6.34/6.50  thf('114', plain,
% 6.34/6.50      ((![X0 : $i]:
% 6.34/6.50          (~ (r1_tarski @ sk_A @ X0)
% 6.34/6.50           | (m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 6.34/6.50              (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ X0)))))
% 6.34/6.50         <= (~
% 6.34/6.50             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.34/6.50               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 6.34/6.50      inference('demod', [status(thm)],
% 6.34/6.50                ['81', '82', '83', '96', '97', '103', '104', '110', '111', 
% 6.34/6.50                 '112', '113'])).
% 6.34/6.50  thf('115', plain,
% 6.34/6.50      (((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 6.34/6.50         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))
% 6.34/6.50         <= (~
% 6.34/6.50             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.34/6.50               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))))),
% 6.34/6.50      inference('sup-', [status(thm)], ['22', '114'])).
% 6.34/6.50  thf('116', plain,
% 6.34/6.50      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.34/6.50         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))),
% 6.34/6.50      inference('demod', [status(thm)], ['20', '115'])).
% 6.34/6.50  thf('117', plain,
% 6.34/6.50      (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)) | 
% 6.34/6.50       ~
% 6.34/6.50       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.34/6.50         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))) | 
% 6.34/6.50       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 6.34/6.50      inference('split', [status(esa)], ['0'])).
% 6.34/6.50  thf('118', plain, (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A))),
% 6.34/6.50      inference('sat_resolution*', [status(thm)], ['17', '116', '117'])).
% 6.34/6.50  thf('119', plain, (~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B_1 @ sk_A)),
% 6.34/6.50      inference('simpl_trail', [status(thm)], ['10', '118'])).
% 6.34/6.50  thf('120', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 6.34/6.50      inference('demod', [status(thm)], ['4', '7', '8'])).
% 6.34/6.50  thf('121', plain,
% 6.34/6.50      (![X20 : $i]:
% 6.34/6.50         (~ (v2_funct_1 @ X20)
% 6.34/6.50          | ((k1_relat_1 @ X20) = (k2_relat_1 @ (k2_funct_1 @ X20)))
% 6.34/6.50          | ~ (v1_funct_1 @ X20)
% 6.34/6.50          | ~ (v1_relat_1 @ X20))),
% 6.34/6.50      inference('cnf', [status(esa)], [t55_funct_1])).
% 6.34/6.50  thf('122', plain,
% 6.34/6.50      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 6.34/6.50        | ~ (v1_relat_1 @ sk_C)
% 6.34/6.50        | ~ (v1_funct_1 @ sk_C)
% 6.34/6.50        | ~ (v2_funct_1 @ sk_C))),
% 6.34/6.50      inference('sup+', [status(thm)], ['120', '121'])).
% 6.34/6.50  thf('123', plain, ((v1_relat_1 @ sk_C)),
% 6.34/6.50      inference('sup-', [status(thm)], ['5', '6'])).
% 6.34/6.50  thf('124', plain, ((v1_funct_1 @ sk_C)),
% 6.34/6.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.34/6.50  thf('125', plain, ((v2_funct_1 @ sk_C)),
% 6.34/6.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.34/6.50  thf('126', plain,
% 6.34/6.50      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 6.34/6.50      inference('demod', [status(thm)], ['122', '123', '124', '125'])).
% 6.34/6.50  thf('127', plain,
% 6.34/6.50      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 6.34/6.50      inference('cnf', [status(esa)], [l13_xboole_0])).
% 6.34/6.50  thf('128', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 6.34/6.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 6.34/6.50  thf('129', plain,
% 6.34/6.50      (![X41 : $i, X42 : $i]:
% 6.34/6.50         (~ (r1_tarski @ (k2_relat_1 @ X41) @ X42)
% 6.34/6.50          | (v1_funct_2 @ X41 @ (k1_relat_1 @ X41) @ X42)
% 6.34/6.50          | ~ (v1_funct_1 @ X41)
% 6.34/6.50          | ~ (v1_relat_1 @ X41))),
% 6.34/6.50      inference('cnf', [status(esa)], [t4_funct_2])).
% 6.34/6.50  thf('130', plain,
% 6.34/6.50      (![X0 : $i]:
% 6.34/6.50         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 6.34/6.50          | ~ (v1_relat_1 @ k1_xboole_0)
% 6.34/6.50          | ~ (v1_funct_1 @ k1_xboole_0)
% 6.34/6.50          | (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 6.34/6.50      inference('sup-', [status(thm)], ['128', '129'])).
% 6.34/6.50  thf('131', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 6.34/6.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 6.34/6.50  thf('132', plain, ((v1_relat_1 @ k1_xboole_0)),
% 6.34/6.50      inference('cnf', [status(esa)], [t45_ordinal1])).
% 6.34/6.50  thf('133', plain, ((v1_funct_1 @ k1_xboole_0)),
% 6.34/6.50      inference('cnf', [status(esa)], [t45_ordinal1])).
% 6.34/6.50  thf('134', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 6.34/6.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 6.34/6.50  thf('135', plain,
% 6.34/6.50      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 6.34/6.50      inference('demod', [status(thm)], ['130', '131', '132', '133', '134'])).
% 6.34/6.50  thf('136', plain,
% 6.34/6.50      (![X0 : $i, X1 : $i]:
% 6.34/6.50         ((v1_funct_2 @ k1_xboole_0 @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 6.34/6.50      inference('sup+', [status(thm)], ['127', '135'])).
% 6.34/6.50  thf('137', plain,
% 6.34/6.50      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 6.34/6.50      inference('sup+', [status(thm)], ['23', '28'])).
% 6.34/6.50  thf('138', plain,
% 6.34/6.50      (((zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 6.34/6.50        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 6.34/6.50      inference('sup-', [status(thm)], ['66', '67'])).
% 6.34/6.50  thf('139', plain,
% 6.34/6.50      (((v1_xboole_0 @ sk_B_1) | (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A))),
% 6.34/6.50      inference('sup-', [status(thm)], ['137', '138'])).
% 6.34/6.50  thf('140', plain,
% 6.34/6.50      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 6.34/6.50        | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 6.34/6.50      inference('demod', [status(thm)], ['72', '75'])).
% 6.34/6.50  thf('141', plain,
% 6.34/6.50      (((v1_xboole_0 @ sk_B_1) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 6.34/6.50      inference('sup-', [status(thm)], ['139', '140'])).
% 6.34/6.50  thf('142', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_C))),
% 6.34/6.50      inference('demod', [status(thm)], ['61', '62'])).
% 6.34/6.50  thf('143', plain, ((((sk_A) = (k1_relat_1 @ sk_C)) | (v1_xboole_0 @ sk_C))),
% 6.34/6.50      inference('sup-', [status(thm)], ['141', '142'])).
% 6.34/6.50  thf('144', plain,
% 6.34/6.50      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 6.34/6.50      inference('cnf', [status(esa)], [l13_xboole_0])).
% 6.34/6.50  thf('145', plain, ((v1_funct_1 @ k1_xboole_0)),
% 6.34/6.50      inference('cnf', [status(esa)], [t45_ordinal1])).
% 6.34/6.50  thf('146', plain,
% 6.34/6.50      (![X18 : $i]:
% 6.34/6.50         (~ (v2_funct_1 @ X18)
% 6.34/6.50          | ((k2_funct_1 @ X18) = (k4_relat_1 @ X18))
% 6.34/6.50          | ~ (v1_funct_1 @ X18)
% 6.34/6.50          | ~ (v1_relat_1 @ X18))),
% 6.34/6.50      inference('cnf', [status(esa)], [d9_funct_1])).
% 6.34/6.50  thf('147', plain,
% 6.34/6.50      ((~ (v1_relat_1 @ k1_xboole_0)
% 6.34/6.50        | ((k2_funct_1 @ k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))
% 6.34/6.50        | ~ (v2_funct_1 @ k1_xboole_0))),
% 6.34/6.50      inference('sup-', [status(thm)], ['145', '146'])).
% 6.34/6.50  thf('148', plain, ((v1_relat_1 @ k1_xboole_0)),
% 6.34/6.50      inference('cnf', [status(esa)], [t45_ordinal1])).
% 6.34/6.50  thf('149', plain,
% 6.34/6.50      ((((k2_funct_1 @ k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))
% 6.34/6.50        | ~ (v2_funct_1 @ k1_xboole_0))),
% 6.34/6.50      inference('demod', [status(thm)], ['147', '148'])).
% 6.34/6.50  thf('150', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.34/6.50      inference('sup-', [status(thm)], ['24', '27'])).
% 6.34/6.50  thf('151', plain,
% 6.34/6.50      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 6.34/6.50      inference('cnf', [status(esa)], [l13_xboole_0])).
% 6.34/6.50  thf('152', plain, ((v1_funct_1 @ k1_xboole_0)),
% 6.34/6.50      inference('cnf', [status(esa)], [t45_ordinal1])).
% 6.34/6.50  thf(cc2_funct_1, axiom,
% 6.34/6.50    (![A:$i]:
% 6.34/6.50     ( ( ( v1_xboole_0 @ A ) & ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 6.34/6.50       ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) ))).
% 6.34/6.50  thf('153', plain,
% 6.34/6.50      (![X17 : $i]:
% 6.34/6.50         ((v2_funct_1 @ X17)
% 6.34/6.50          | ~ (v1_funct_1 @ X17)
% 6.34/6.50          | ~ (v1_relat_1 @ X17)
% 6.34/6.50          | ~ (v1_xboole_0 @ X17))),
% 6.34/6.50      inference('cnf', [status(esa)], [cc2_funct_1])).
% 6.34/6.50  thf('154', plain,
% 6.34/6.50      ((~ (v1_xboole_0 @ k1_xboole_0)
% 6.34/6.50        | ~ (v1_relat_1 @ k1_xboole_0)
% 6.34/6.50        | (v2_funct_1 @ k1_xboole_0))),
% 6.34/6.50      inference('sup-', [status(thm)], ['152', '153'])).
% 6.34/6.50  thf('155', plain, ((v1_relat_1 @ k1_xboole_0)),
% 6.34/6.50      inference('cnf', [status(esa)], [t45_ordinal1])).
% 6.34/6.50  thf('156', plain,
% 6.34/6.50      ((~ (v1_xboole_0 @ k1_xboole_0) | (v2_funct_1 @ k1_xboole_0))),
% 6.34/6.50      inference('demod', [status(thm)], ['154', '155'])).
% 6.34/6.50  thf('157', plain,
% 6.34/6.50      (![X0 : $i]:
% 6.34/6.50         (~ (v1_xboole_0 @ X0)
% 6.34/6.50          | ~ (v1_xboole_0 @ X0)
% 6.34/6.50          | (v2_funct_1 @ k1_xboole_0))),
% 6.34/6.50      inference('sup-', [status(thm)], ['151', '156'])).
% 6.34/6.50  thf('158', plain,
% 6.34/6.50      (![X0 : $i]: ((v2_funct_1 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0))),
% 6.34/6.50      inference('simplify', [status(thm)], ['157'])).
% 6.34/6.50  thf('159', plain, ((v2_funct_1 @ k1_xboole_0)),
% 6.34/6.50      inference('sup-', [status(thm)], ['150', '158'])).
% 6.34/6.50  thf('160', plain,
% 6.34/6.50      (((k2_funct_1 @ k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))),
% 6.34/6.50      inference('demod', [status(thm)], ['149', '159'])).
% 6.34/6.50  thf('161', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.34/6.50      inference('sup-', [status(thm)], ['24', '27'])).
% 6.34/6.50  thf('162', plain,
% 6.34/6.50      (![X15 : $i]:
% 6.34/6.50         ((v1_xboole_0 @ (k4_relat_1 @ X15)) | ~ (v1_xboole_0 @ X15))),
% 6.34/6.50      inference('cnf', [status(esa)], [fc14_relat_1])).
% 6.34/6.50  thf('163', plain,
% 6.34/6.50      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 6.34/6.50      inference('cnf', [status(esa)], [l13_xboole_0])).
% 6.34/6.50  thf('164', plain,
% 6.34/6.50      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k4_relat_1 @ X0) = (k1_xboole_0)))),
% 6.34/6.50      inference('sup-', [status(thm)], ['162', '163'])).
% 6.34/6.50  thf('165', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 6.34/6.50      inference('sup-', [status(thm)], ['161', '164'])).
% 6.34/6.50  thf('166', plain, (((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0))),
% 6.34/6.50      inference('demod', [status(thm)], ['160', '165'])).
% 6.34/6.50  thf('167', plain,
% 6.34/6.50      (![X0 : $i]: (((k2_funct_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.34/6.50      inference('sup+', [status(thm)], ['144', '166'])).
% 6.34/6.50  thf('168', plain,
% 6.34/6.50      ((((sk_A) = (k1_relat_1 @ sk_C)) | ((k2_funct_1 @ sk_C) = (k1_xboole_0)))),
% 6.34/6.50      inference('sup-', [status(thm)], ['143', '167'])).
% 6.34/6.50  thf('169', plain,
% 6.34/6.50      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A))
% 6.34/6.50         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 6.34/6.50      inference('split', [status(esa)], ['0'])).
% 6.34/6.50  thf('170', plain,
% 6.34/6.50      (((~ (v1_funct_2 @ k1_xboole_0 @ sk_B_1 @ sk_A)
% 6.34/6.50         | ((sk_A) = (k1_relat_1 @ sk_C))))
% 6.34/6.50         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 6.34/6.50      inference('sup-', [status(thm)], ['168', '169'])).
% 6.34/6.50  thf('171', plain,
% 6.34/6.50      (((~ (v1_xboole_0 @ sk_B_1) | ((sk_A) = (k1_relat_1 @ sk_C))))
% 6.34/6.50         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 6.34/6.50      inference('sup-', [status(thm)], ['136', '170'])).
% 6.34/6.50  thf('172', plain,
% 6.34/6.50      (((v1_xboole_0 @ sk_B_1) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 6.34/6.50      inference('sup-', [status(thm)], ['139', '140'])).
% 6.34/6.50  thf('173', plain,
% 6.34/6.50      ((((sk_A) = (k1_relat_1 @ sk_C)))
% 6.34/6.50         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 6.34/6.50      inference('clc', [status(thm)], ['171', '172'])).
% 6.34/6.50  thf('174', plain, (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A))),
% 6.34/6.50      inference('sat_resolution*', [status(thm)], ['17', '116', '117'])).
% 6.34/6.50  thf('175', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 6.34/6.50      inference('simpl_trail', [status(thm)], ['173', '174'])).
% 6.34/6.50  thf('176', plain, (((sk_A) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 6.34/6.50      inference('demod', [status(thm)], ['126', '175'])).
% 6.34/6.50  thf('177', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 6.34/6.50      inference('simplify', [status(thm)], ['21'])).
% 6.34/6.50  thf('178', plain,
% 6.34/6.50      (![X41 : $i, X42 : $i]:
% 6.34/6.50         (~ (r1_tarski @ (k2_relat_1 @ X41) @ X42)
% 6.34/6.50          | (m1_subset_1 @ X41 @ 
% 6.34/6.50             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X41) @ X42)))
% 6.34/6.50          | ~ (v1_funct_1 @ X41)
% 6.34/6.50          | ~ (v1_relat_1 @ X41))),
% 6.34/6.50      inference('cnf', [status(esa)], [t4_funct_2])).
% 6.34/6.50  thf('179', plain,
% 6.34/6.50      (![X0 : $i]:
% 6.34/6.50         (~ (v1_relat_1 @ X0)
% 6.34/6.50          | ~ (v1_funct_1 @ X0)
% 6.34/6.50          | (m1_subset_1 @ X0 @ 
% 6.34/6.50             (k1_zfmisc_1 @ 
% 6.34/6.50              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 6.34/6.50      inference('sup-', [status(thm)], ['177', '178'])).
% 6.34/6.50  thf('180', plain,
% 6.34/6.50      (((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 6.34/6.50         (k1_zfmisc_1 @ 
% 6.34/6.50          (k2_zfmisc_1 @ (k1_relat_1 @ (k4_relat_1 @ sk_C)) @ sk_A)))
% 6.34/6.50        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C))
% 6.34/6.50        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 6.34/6.50      inference('sup+', [status(thm)], ['176', '179'])).
% 6.34/6.50  thf('181', plain, (((sk_B_1) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 6.34/6.50      inference('demod', [status(thm)], ['90', '95'])).
% 6.34/6.50  thf('182', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 6.34/6.50      inference('demod', [status(thm)], ['100', '101', '102'])).
% 6.34/6.50  thf('183', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 6.34/6.50      inference('demod', [status(thm)], ['107', '108', '109'])).
% 6.34/6.50  thf('184', plain,
% 6.34/6.50      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 6.34/6.50        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 6.34/6.50      inference('demod', [status(thm)], ['180', '181', '182', '183'])).
% 6.34/6.50  thf('185', plain,
% 6.34/6.50      (![X27 : $i, X28 : $i, X29 : $i]:
% 6.34/6.50         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 6.34/6.50          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 6.34/6.50      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 6.34/6.50  thf('186', plain,
% 6.34/6.50      (((k1_relset_1 @ sk_B_1 @ sk_A @ (k4_relat_1 @ sk_C))
% 6.34/6.50         = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 6.34/6.50      inference('sup-', [status(thm)], ['184', '185'])).
% 6.34/6.50  thf('187', plain, (((sk_B_1) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 6.34/6.50      inference('demod', [status(thm)], ['90', '95'])).
% 6.34/6.50  thf('188', plain,
% 6.34/6.50      (((k1_relset_1 @ sk_B_1 @ sk_A @ (k4_relat_1 @ sk_C)) = (sk_B_1))),
% 6.34/6.50      inference('demod', [status(thm)], ['186', '187'])).
% 6.34/6.50  thf('189', plain,
% 6.34/6.50      (![X35 : $i, X36 : $i, X37 : $i]:
% 6.34/6.50         (((X35) != (k1_relset_1 @ X35 @ X36 @ X37))
% 6.34/6.50          | (v1_funct_2 @ X37 @ X35 @ X36)
% 6.34/6.50          | ~ (zip_tseitin_1 @ X37 @ X36 @ X35))),
% 6.34/6.50      inference('cnf', [status(esa)], [zf_stmt_3])).
% 6.34/6.50  thf('190', plain,
% 6.34/6.50      ((((sk_B_1) != (sk_B_1))
% 6.34/6.50        | ~ (zip_tseitin_1 @ (k4_relat_1 @ sk_C) @ sk_A @ sk_B_1)
% 6.34/6.50        | (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B_1 @ sk_A))),
% 6.34/6.50      inference('sup-', [status(thm)], ['188', '189'])).
% 6.34/6.50  thf('191', plain,
% 6.34/6.50      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 6.34/6.50        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 6.34/6.50      inference('demod', [status(thm)], ['180', '181', '182', '183'])).
% 6.34/6.50  thf('192', plain,
% 6.34/6.50      (![X38 : $i, X39 : $i, X40 : $i]:
% 6.34/6.50         (~ (zip_tseitin_0 @ X38 @ X39)
% 6.34/6.50          | (zip_tseitin_1 @ X40 @ X38 @ X39)
% 6.34/6.50          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 6.34/6.50      inference('cnf', [status(esa)], [zf_stmt_5])).
% 6.34/6.50  thf('193', plain,
% 6.34/6.50      (((zip_tseitin_1 @ (k4_relat_1 @ sk_C) @ sk_A @ sk_B_1)
% 6.34/6.50        | ~ (zip_tseitin_0 @ sk_A @ sk_B_1))),
% 6.34/6.50      inference('sup-', [status(thm)], ['191', '192'])).
% 6.34/6.50  thf('194', plain,
% 6.34/6.50      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 6.34/6.50      inference('sup+', [status(thm)], ['23', '28'])).
% 6.34/6.50  thf('195', plain,
% 6.34/6.50      (![X0 : $i, X1 : $i]:
% 6.34/6.50         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.34/6.50      inference('sup+', [status(thm)], ['43', '44'])).
% 6.34/6.50  thf('196', plain,
% 6.34/6.50      (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 6.34/6.50      inference('sup-', [status(thm)], ['58', '59'])).
% 6.34/6.50  thf('197', plain,
% 6.34/6.50      ((~ (v1_xboole_0 @ k1_xboole_0)
% 6.34/6.50        | ~ (v1_xboole_0 @ sk_A)
% 6.34/6.50        | (v1_xboole_0 @ sk_C))),
% 6.34/6.50      inference('sup-', [status(thm)], ['195', '196'])).
% 6.34/6.50  thf('198', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.34/6.50      inference('sup-', [status(thm)], ['24', '27'])).
% 6.34/6.50  thf('199', plain, ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_C))),
% 6.34/6.50      inference('demod', [status(thm)], ['197', '198'])).
% 6.34/6.50  thf('200', plain,
% 6.34/6.50      (![X0 : $i]: ((zip_tseitin_0 @ sk_A @ X0) | (v1_xboole_0 @ sk_C))),
% 6.34/6.50      inference('sup-', [status(thm)], ['194', '199'])).
% 6.34/6.50  thf('201', plain,
% 6.34/6.50      (![X0 : $i]: (((k2_funct_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.34/6.50      inference('sup+', [status(thm)], ['144', '166'])).
% 6.34/6.50  thf('202', plain,
% 6.34/6.50      (![X0 : $i, X1 : $i]:
% 6.34/6.50         ((v1_funct_2 @ k1_xboole_0 @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 6.34/6.50      inference('sup+', [status(thm)], ['127', '135'])).
% 6.34/6.50  thf('203', plain,
% 6.34/6.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.34/6.50         ((v1_funct_2 @ (k2_funct_1 @ X0) @ X2 @ X1)
% 6.34/6.50          | ~ (v1_xboole_0 @ X0)
% 6.34/6.50          | ~ (v1_xboole_0 @ X2))),
% 6.34/6.50      inference('sup+', [status(thm)], ['201', '202'])).
% 6.34/6.50  thf('204', plain,
% 6.34/6.50      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A))
% 6.34/6.50         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 6.34/6.50      inference('split', [status(esa)], ['0'])).
% 6.34/6.50  thf('205', plain,
% 6.34/6.50      (((~ (v1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ sk_C)))
% 6.34/6.50         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 6.34/6.50      inference('sup-', [status(thm)], ['203', '204'])).
% 6.34/6.50  thf('206', plain, (((k2_relat_1 @ sk_C) = (sk_B_1))),
% 6.34/6.50      inference('sup+', [status(thm)], ['93', '94'])).
% 6.34/6.50  thf('207', plain,
% 6.34/6.50      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 6.34/6.50      inference('cnf', [status(esa)], [l13_xboole_0])).
% 6.34/6.50  thf('208', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 6.34/6.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 6.34/6.50  thf('209', plain,
% 6.34/6.50      (![X0 : $i]: (((k2_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.34/6.50      inference('sup+', [status(thm)], ['207', '208'])).
% 6.34/6.50  thf('210', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.34/6.50      inference('sup-', [status(thm)], ['24', '27'])).
% 6.34/6.50  thf('211', plain,
% 6.34/6.50      (![X0 : $i]: ((v1_xboole_0 @ (k2_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 6.34/6.50      inference('sup+', [status(thm)], ['209', '210'])).
% 6.34/6.50  thf('212', plain, (((v1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ sk_C))),
% 6.34/6.50      inference('sup+', [status(thm)], ['206', '211'])).
% 6.34/6.50  thf('213', plain,
% 6.34/6.50      ((~ (v1_xboole_0 @ sk_C))
% 6.34/6.50         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 6.34/6.50      inference('clc', [status(thm)], ['205', '212'])).
% 6.34/6.50  thf('214', plain,
% 6.34/6.50      ((![X0 : $i]: (zip_tseitin_0 @ sk_A @ X0))
% 6.34/6.50         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A)))),
% 6.34/6.50      inference('sup-', [status(thm)], ['200', '213'])).
% 6.34/6.50  thf('215', plain, (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B_1 @ sk_A))),
% 6.34/6.50      inference('sat_resolution*', [status(thm)], ['17', '116', '117'])).
% 6.34/6.50  thf('216', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_A @ X0)),
% 6.34/6.50      inference('simpl_trail', [status(thm)], ['214', '215'])).
% 6.34/6.50  thf('217', plain, ((zip_tseitin_1 @ (k4_relat_1 @ sk_C) @ sk_A @ sk_B_1)),
% 6.34/6.50      inference('demod', [status(thm)], ['193', '216'])).
% 6.34/6.50  thf('218', plain,
% 6.34/6.50      ((((sk_B_1) != (sk_B_1))
% 6.34/6.50        | (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B_1 @ sk_A))),
% 6.34/6.50      inference('demod', [status(thm)], ['190', '217'])).
% 6.34/6.50  thf('219', plain, ((v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B_1 @ sk_A)),
% 6.34/6.50      inference('simplify', [status(thm)], ['218'])).
% 6.34/6.50  thf('220', plain, ($false), inference('demod', [status(thm)], ['119', '219'])).
% 6.34/6.50  
% 6.34/6.50  % SZS output end Refutation
% 6.34/6.50  
% 6.34/6.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
