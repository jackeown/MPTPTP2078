%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.61cHNu8F3k

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:14 EST 2020

% Result     : Theorem 4.47s
% Output     : Refutation 4.47s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 327 expanded)
%              Number of leaves         :   41 ( 113 expanded)
%              Depth                    :   15
%              Number of atoms          : 1110 (6407 expanded)
%              Number of equality atoms :   33 (  67 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('1',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(fc4_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_xboole_0 @ X5 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('4',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('5',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('6',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf('11',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k6_partfun1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','12'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('14',plain,(
    ! [X12: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('15',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('16',plain,(
    ! [X12: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X12 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','17'])).

thf(t29_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
           => ( ( v2_funct_1 @ C )
              & ( v2_funct_2 @ D @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ A )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
           => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
             => ( ( v2_funct_1 @ C )
                & ( v2_funct_2 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_funct_2])).

thf('19',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,
    ( ~ ( v1_xboole_0 @ sk_C_1 )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( r2_relset_1 @ B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ ( k6_partfun1 @ B ) )
           => ( ( k2_relset_1 @ A @ B @ C )
              = B ) ) ) ) )).

thf('24',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_2 @ X41 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( r2_relset_1 @ X42 @ X42 @ ( k1_partfun1 @ X42 @ X43 @ X43 @ X42 @ X41 @ X44 ) @ ( k6_partfun1 @ X42 ) )
      | ( ( k2_relset_1 @ X43 @ X42 @ X44 )
        = X42 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) )
      | ~ ( v1_funct_2 @ X44 @ X43 @ X42 )
      | ~ ( v1_funct_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B_2 @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2 )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B_2 @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,
    ( ( ( k2_relset_1 @ sk_B_2 @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B_2 @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('31',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X26 @ X24 )
        = ( k2_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('32',plain,
    ( ( k2_relset_1 @ sk_B_2 @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_2 @ sk_D @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['29','32','33','34','35'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('37',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k2_relat_1 @ X33 )
       != X32 )
      | ( v2_funct_2 @ X33 @ X32 )
      | ~ ( v5_relat_1 @ X33 @ X32 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('38',plain,(
    ! [X33: $i] :
      ( ~ ( v1_relat_1 @ X33 )
      | ~ ( v5_relat_1 @ X33 @ ( k2_relat_1 @ X33 ) )
      | ( v2_funct_2 @ X33 @ ( k2_relat_1 @ X33 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('41',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v5_relat_1 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('42',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['29','32','33','34','35'])).

thf('44',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('45',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('46',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['39','42','43','46'])).

thf('48',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['19'])).

thf('49',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['19'])).

thf('51',plain,(
    ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['21','51'])).

thf('53',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('54',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_xboole_0 @ X5 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf('55',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('62',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_2 @ X2 @ X0 @ sk_C_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_2 @ X2 @ X0 @ sk_C_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['60','65'])).

thf('67',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('69',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( X27 = X30 )
      | ~ ( r2_relset_1 @ X28 @ X29 @ X27 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','70'])).

thf('72',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('73',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t26_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
           => ( ( ( C = k1_xboole_0 )
                & ( B != k1_xboole_0 ) )
              | ( v2_funct_1 @ D ) ) ) ) ) )).

thf('75',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_2 @ X45 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X48 @ X46 @ X46 @ X47 @ X49 @ X45 ) )
      | ( v2_funct_1 @ X49 )
      | ( X47 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X46 ) ) )
      | ~ ( v1_funct_2 @ X49 @ X48 @ X46 )
      | ~ ( v1_funct_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_2 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_2 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_2 @ sk_B_2 @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_2 @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_funct_2 @ sk_D @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_2 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_2 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_2 @ sk_B_2 @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C_1 )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['73','79'])).

thf('81',plain,(
    ! [X12: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X12 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('82',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( v2_funct_1 @ sk_C_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','81','82','83','84'])).

thf('86',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['19'])).

thf('87',plain,(
    ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['49','50'])).

thf('88',plain,(
    ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['86','87'])).

thf('89',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['85','88'])).

thf('90',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('91',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['58','89','90'])).

thf('92',plain,(
    v1_xboole_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['53','91'])).

thf('93',plain,(
    $false ),
    inference(demod,[status(thm)],['52','92'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.61cHNu8F3k
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:24:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 4.47/4.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.47/4.71  % Solved by: fo/fo7.sh
% 4.47/4.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.47/4.71  % done 3673 iterations in 4.249s
% 4.47/4.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.47/4.71  % SZS output start Refutation
% 4.47/4.71  thf(sk_C_1_type, type, sk_C_1: $i).
% 4.47/4.71  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 4.47/4.71  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 4.47/4.71  thf(sk_B_type, type, sk_B: $i > $i).
% 4.47/4.71  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 4.47/4.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.47/4.71  thf(sk_A_type, type, sk_A: $i).
% 4.47/4.71  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 4.47/4.71  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 4.47/4.71  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 4.47/4.71  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 4.47/4.71  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 4.47/4.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.47/4.71  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 4.47/4.71  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 4.47/4.71  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.47/4.71  thf(sk_B_2_type, type, sk_B_2: $i).
% 4.47/4.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.47/4.71  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.47/4.71  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.47/4.71  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.47/4.71  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.47/4.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.47/4.71  thf(sk_D_type, type, sk_D: $i).
% 4.47/4.71  thf(l13_xboole_0, axiom,
% 4.47/4.71    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 4.47/4.71  thf('0', plain,
% 4.47/4.71      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 4.47/4.71      inference('cnf', [status(esa)], [l13_xboole_0])).
% 4.47/4.71  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 4.47/4.71  thf('1', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.47/4.71      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.47/4.71  thf(d1_xboole_0, axiom,
% 4.47/4.71    (![A:$i]:
% 4.47/4.71     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 4.47/4.71  thf('2', plain,
% 4.47/4.71      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 4.47/4.71      inference('cnf', [status(esa)], [d1_xboole_0])).
% 4.47/4.71  thf(fc4_zfmisc_1, axiom,
% 4.47/4.71    (![A:$i,B:$i]:
% 4.47/4.71     ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 4.47/4.71  thf('3', plain,
% 4.47/4.71      (![X5 : $i, X6 : $i]:
% 4.47/4.71         (~ (v1_xboole_0 @ X5) | (v1_xboole_0 @ (k2_zfmisc_1 @ X5 @ X6)))),
% 4.47/4.71      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 4.47/4.71  thf(t29_relset_1, axiom,
% 4.47/4.71    (![A:$i]:
% 4.47/4.71     ( m1_subset_1 @
% 4.47/4.71       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 4.47/4.71  thf('4', plain,
% 4.47/4.71      (![X31 : $i]:
% 4.47/4.71         (m1_subset_1 @ (k6_relat_1 @ X31) @ 
% 4.47/4.71          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 4.47/4.71      inference('cnf', [status(esa)], [t29_relset_1])).
% 4.47/4.71  thf(redefinition_k6_partfun1, axiom,
% 4.47/4.71    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 4.47/4.71  thf('5', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 4.47/4.71      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.47/4.71  thf('6', plain,
% 4.47/4.71      (![X31 : $i]:
% 4.47/4.71         (m1_subset_1 @ (k6_partfun1 @ X31) @ 
% 4.47/4.71          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 4.47/4.71      inference('demod', [status(thm)], ['4', '5'])).
% 4.47/4.71  thf(t5_subset, axiom,
% 4.47/4.71    (![A:$i,B:$i,C:$i]:
% 4.47/4.71     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 4.47/4.71          ( v1_xboole_0 @ C ) ) ))).
% 4.47/4.71  thf('7', plain,
% 4.47/4.71      (![X7 : $i, X8 : $i, X9 : $i]:
% 4.47/4.71         (~ (r2_hidden @ X7 @ X8)
% 4.47/4.71          | ~ (v1_xboole_0 @ X9)
% 4.47/4.71          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 4.47/4.71      inference('cnf', [status(esa)], [t5_subset])).
% 4.47/4.71  thf('8', plain,
% 4.47/4.71      (![X0 : $i, X1 : $i]:
% 4.47/4.71         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X0))
% 4.47/4.71          | ~ (r2_hidden @ X1 @ (k6_partfun1 @ X0)))),
% 4.47/4.71      inference('sup-', [status(thm)], ['6', '7'])).
% 4.47/4.71  thf('9', plain,
% 4.47/4.71      (![X0 : $i, X1 : $i]:
% 4.47/4.71         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ (k6_partfun1 @ X0)))),
% 4.47/4.71      inference('sup-', [status(thm)], ['3', '8'])).
% 4.47/4.71  thf('10', plain,
% 4.47/4.71      (![X0 : $i]: ((v1_xboole_0 @ (k6_partfun1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 4.47/4.71      inference('sup-', [status(thm)], ['2', '9'])).
% 4.47/4.71  thf('11', plain,
% 4.47/4.71      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 4.47/4.71      inference('cnf', [status(esa)], [l13_xboole_0])).
% 4.47/4.71  thf('12', plain,
% 4.47/4.71      (![X0 : $i]:
% 4.47/4.71         (~ (v1_xboole_0 @ X0) | ((k6_partfun1 @ X0) = (k1_xboole_0)))),
% 4.47/4.71      inference('sup-', [status(thm)], ['10', '11'])).
% 4.47/4.71  thf('13', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.47/4.71      inference('sup-', [status(thm)], ['1', '12'])).
% 4.47/4.71  thf(fc4_funct_1, axiom,
% 4.47/4.71    (![A:$i]:
% 4.47/4.71     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 4.47/4.71       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 4.47/4.71  thf('14', plain, (![X12 : $i]: (v2_funct_1 @ (k6_relat_1 @ X12))),
% 4.47/4.71      inference('cnf', [status(esa)], [fc4_funct_1])).
% 4.47/4.71  thf('15', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 4.47/4.71      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 4.47/4.71  thf('16', plain, (![X12 : $i]: (v2_funct_1 @ (k6_partfun1 @ X12))),
% 4.47/4.71      inference('demod', [status(thm)], ['14', '15'])).
% 4.47/4.71  thf('17', plain, ((v2_funct_1 @ k1_xboole_0)),
% 4.47/4.71      inference('sup+', [status(thm)], ['13', '16'])).
% 4.47/4.71  thf('18', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 4.47/4.71      inference('sup+', [status(thm)], ['0', '17'])).
% 4.47/4.71  thf(t29_funct_2, conjecture,
% 4.47/4.71    (![A:$i,B:$i,C:$i]:
% 4.47/4.71     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.47/4.71         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.47/4.71       ( ![D:$i]:
% 4.47/4.71         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 4.47/4.71             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 4.47/4.71           ( ( r2_relset_1 @
% 4.47/4.71               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 4.47/4.71               ( k6_partfun1 @ A ) ) =>
% 4.47/4.71             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 4.47/4.71  thf(zf_stmt_0, negated_conjecture,
% 4.47/4.71    (~( ![A:$i,B:$i,C:$i]:
% 4.47/4.71        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.47/4.71            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.47/4.71          ( ![D:$i]:
% 4.47/4.71            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 4.47/4.71                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 4.47/4.71              ( ( r2_relset_1 @
% 4.47/4.71                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 4.47/4.71                  ( k6_partfun1 @ A ) ) =>
% 4.47/4.71                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 4.47/4.71    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 4.47/4.71  thf('19', plain, ((~ (v2_funct_1 @ sk_C_1) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 4.47/4.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.47/4.71  thf('20', plain, ((~ (v2_funct_1 @ sk_C_1)) <= (~ ((v2_funct_1 @ sk_C_1)))),
% 4.47/4.71      inference('split', [status(esa)], ['19'])).
% 4.47/4.71  thf('21', plain, ((~ (v1_xboole_0 @ sk_C_1)) <= (~ ((v2_funct_1 @ sk_C_1)))),
% 4.47/4.71      inference('sup-', [status(thm)], ['18', '20'])).
% 4.47/4.71  thf('22', plain,
% 4.47/4.71      ((r2_relset_1 @ sk_A @ sk_A @ 
% 4.47/4.71        (k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ sk_D) @ 
% 4.47/4.71        (k6_partfun1 @ sk_A))),
% 4.47/4.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.47/4.71  thf('23', plain,
% 4.47/4.71      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 4.47/4.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.47/4.71  thf(t24_funct_2, axiom,
% 4.47/4.71    (![A:$i,B:$i,C:$i]:
% 4.47/4.71     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.47/4.71         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.47/4.71       ( ![D:$i]:
% 4.47/4.71         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 4.47/4.71             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 4.47/4.71           ( ( r2_relset_1 @
% 4.47/4.71               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 4.47/4.71               ( k6_partfun1 @ B ) ) =>
% 4.47/4.71             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 4.47/4.71  thf('24', plain,
% 4.47/4.71      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 4.47/4.71         (~ (v1_funct_1 @ X41)
% 4.47/4.71          | ~ (v1_funct_2 @ X41 @ X42 @ X43)
% 4.47/4.71          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 4.47/4.71          | ~ (r2_relset_1 @ X42 @ X42 @ 
% 4.47/4.71               (k1_partfun1 @ X42 @ X43 @ X43 @ X42 @ X41 @ X44) @ 
% 4.47/4.71               (k6_partfun1 @ X42))
% 4.47/4.71          | ((k2_relset_1 @ X43 @ X42 @ X44) = (X42))
% 4.47/4.71          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42)))
% 4.47/4.71          | ~ (v1_funct_2 @ X44 @ X43 @ X42)
% 4.47/4.71          | ~ (v1_funct_1 @ X44))),
% 4.47/4.71      inference('cnf', [status(esa)], [t24_funct_2])).
% 4.47/4.71  thf('25', plain,
% 4.47/4.71      (![X0 : $i]:
% 4.47/4.71         (~ (v1_funct_1 @ X0)
% 4.47/4.71          | ~ (v1_funct_2 @ X0 @ sk_B_2 @ sk_A)
% 4.47/4.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_A)))
% 4.47/4.71          | ((k2_relset_1 @ sk_B_2 @ sk_A @ X0) = (sk_A))
% 4.47/4.71          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 4.47/4.71               (k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ X0) @ 
% 4.47/4.71               (k6_partfun1 @ sk_A))
% 4.47/4.71          | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2)
% 4.47/4.71          | ~ (v1_funct_1 @ sk_C_1))),
% 4.47/4.71      inference('sup-', [status(thm)], ['23', '24'])).
% 4.47/4.71  thf('26', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2)),
% 4.47/4.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.47/4.71  thf('27', plain, ((v1_funct_1 @ sk_C_1)),
% 4.47/4.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.47/4.71  thf('28', plain,
% 4.47/4.71      (![X0 : $i]:
% 4.47/4.71         (~ (v1_funct_1 @ X0)
% 4.47/4.71          | ~ (v1_funct_2 @ X0 @ sk_B_2 @ sk_A)
% 4.47/4.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_A)))
% 4.47/4.71          | ((k2_relset_1 @ sk_B_2 @ sk_A @ X0) = (sk_A))
% 4.47/4.71          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 4.47/4.71               (k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ X0) @ 
% 4.47/4.71               (k6_partfun1 @ sk_A)))),
% 4.47/4.71      inference('demod', [status(thm)], ['25', '26', '27'])).
% 4.47/4.71  thf('29', plain,
% 4.47/4.71      ((((k2_relset_1 @ sk_B_2 @ sk_A @ sk_D) = (sk_A))
% 4.47/4.71        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_A)))
% 4.47/4.71        | ~ (v1_funct_2 @ sk_D @ sk_B_2 @ sk_A)
% 4.47/4.71        | ~ (v1_funct_1 @ sk_D))),
% 4.47/4.71      inference('sup-', [status(thm)], ['22', '28'])).
% 4.47/4.71  thf('30', plain,
% 4.47/4.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_A)))),
% 4.47/4.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.47/4.71  thf(redefinition_k2_relset_1, axiom,
% 4.47/4.71    (![A:$i,B:$i,C:$i]:
% 4.47/4.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.47/4.71       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 4.47/4.71  thf('31', plain,
% 4.47/4.71      (![X24 : $i, X25 : $i, X26 : $i]:
% 4.47/4.71         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 4.47/4.71          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 4.47/4.71      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 4.47/4.71  thf('32', plain,
% 4.47/4.71      (((k2_relset_1 @ sk_B_2 @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 4.47/4.71      inference('sup-', [status(thm)], ['30', '31'])).
% 4.47/4.71  thf('33', plain,
% 4.47/4.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_A)))),
% 4.47/4.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.47/4.71  thf('34', plain, ((v1_funct_2 @ sk_D @ sk_B_2 @ sk_A)),
% 4.47/4.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.47/4.71  thf('35', plain, ((v1_funct_1 @ sk_D)),
% 4.47/4.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.47/4.71  thf('36', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 4.47/4.71      inference('demod', [status(thm)], ['29', '32', '33', '34', '35'])).
% 4.47/4.71  thf(d3_funct_2, axiom,
% 4.47/4.71    (![A:$i,B:$i]:
% 4.47/4.71     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 4.47/4.71       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 4.47/4.71  thf('37', plain,
% 4.47/4.71      (![X32 : $i, X33 : $i]:
% 4.47/4.71         (((k2_relat_1 @ X33) != (X32))
% 4.47/4.71          | (v2_funct_2 @ X33 @ X32)
% 4.47/4.71          | ~ (v5_relat_1 @ X33 @ X32)
% 4.47/4.71          | ~ (v1_relat_1 @ X33))),
% 4.47/4.71      inference('cnf', [status(esa)], [d3_funct_2])).
% 4.47/4.71  thf('38', plain,
% 4.47/4.71      (![X33 : $i]:
% 4.47/4.71         (~ (v1_relat_1 @ X33)
% 4.47/4.71          | ~ (v5_relat_1 @ X33 @ (k2_relat_1 @ X33))
% 4.47/4.71          | (v2_funct_2 @ X33 @ (k2_relat_1 @ X33)))),
% 4.47/4.71      inference('simplify', [status(thm)], ['37'])).
% 4.47/4.71  thf('39', plain,
% 4.47/4.71      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 4.47/4.71        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 4.47/4.71        | ~ (v1_relat_1 @ sk_D))),
% 4.47/4.71      inference('sup-', [status(thm)], ['36', '38'])).
% 4.47/4.71  thf('40', plain,
% 4.47/4.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_A)))),
% 4.47/4.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.47/4.71  thf(cc2_relset_1, axiom,
% 4.47/4.71    (![A:$i,B:$i,C:$i]:
% 4.47/4.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.47/4.71       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 4.47/4.71  thf('41', plain,
% 4.47/4.71      (![X21 : $i, X22 : $i, X23 : $i]:
% 4.47/4.71         ((v5_relat_1 @ X21 @ X23)
% 4.47/4.71          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 4.47/4.71      inference('cnf', [status(esa)], [cc2_relset_1])).
% 4.47/4.71  thf('42', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 4.47/4.71      inference('sup-', [status(thm)], ['40', '41'])).
% 4.47/4.71  thf('43', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 4.47/4.71      inference('demod', [status(thm)], ['29', '32', '33', '34', '35'])).
% 4.47/4.71  thf('44', plain,
% 4.47/4.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_A)))),
% 4.47/4.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.47/4.71  thf(cc1_relset_1, axiom,
% 4.47/4.71    (![A:$i,B:$i,C:$i]:
% 4.47/4.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.47/4.71       ( v1_relat_1 @ C ) ))).
% 4.47/4.71  thf('45', plain,
% 4.47/4.71      (![X18 : $i, X19 : $i, X20 : $i]:
% 4.47/4.71         ((v1_relat_1 @ X18)
% 4.47/4.71          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 4.47/4.71      inference('cnf', [status(esa)], [cc1_relset_1])).
% 4.47/4.71  thf('46', plain, ((v1_relat_1 @ sk_D)),
% 4.47/4.71      inference('sup-', [status(thm)], ['44', '45'])).
% 4.47/4.71  thf('47', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 4.47/4.71      inference('demod', [status(thm)], ['39', '42', '43', '46'])).
% 4.47/4.71  thf('48', plain,
% 4.47/4.71      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 4.47/4.71      inference('split', [status(esa)], ['19'])).
% 4.47/4.71  thf('49', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 4.47/4.71      inference('sup-', [status(thm)], ['47', '48'])).
% 4.47/4.71  thf('50', plain,
% 4.47/4.71      (~ ((v2_funct_1 @ sk_C_1)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 4.47/4.71      inference('split', [status(esa)], ['19'])).
% 4.47/4.71  thf('51', plain, (~ ((v2_funct_1 @ sk_C_1))),
% 4.47/4.71      inference('sat_resolution*', [status(thm)], ['49', '50'])).
% 4.47/4.71  thf('52', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 4.47/4.71      inference('simpl_trail', [status(thm)], ['21', '51'])).
% 4.47/4.71  thf('53', plain,
% 4.47/4.71      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 4.47/4.71      inference('cnf', [status(esa)], [d1_xboole_0])).
% 4.47/4.71  thf('54', plain,
% 4.47/4.71      (![X5 : $i, X6 : $i]:
% 4.47/4.71         (~ (v1_xboole_0 @ X5) | (v1_xboole_0 @ (k2_zfmisc_1 @ X5 @ X6)))),
% 4.47/4.71      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 4.47/4.71  thf('55', plain,
% 4.47/4.71      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 4.47/4.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.47/4.71  thf('56', plain,
% 4.47/4.71      (![X7 : $i, X8 : $i, X9 : $i]:
% 4.47/4.71         (~ (r2_hidden @ X7 @ X8)
% 4.47/4.71          | ~ (v1_xboole_0 @ X9)
% 4.47/4.71          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 4.47/4.71      inference('cnf', [status(esa)], [t5_subset])).
% 4.47/4.71  thf('57', plain,
% 4.47/4.71      (![X0 : $i]:
% 4.47/4.71         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))
% 4.47/4.71          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 4.47/4.71      inference('sup-', [status(thm)], ['55', '56'])).
% 4.47/4.71  thf('58', plain,
% 4.47/4.71      (![X0 : $i]: (~ (v1_xboole_0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 4.47/4.71      inference('sup-', [status(thm)], ['54', '57'])).
% 4.47/4.71  thf('59', plain,
% 4.47/4.71      ((r2_relset_1 @ sk_A @ sk_A @ 
% 4.47/4.71        (k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ sk_D) @ 
% 4.47/4.71        (k6_partfun1 @ sk_A))),
% 4.47/4.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.47/4.71  thf('60', plain,
% 4.47/4.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_A)))),
% 4.47/4.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.47/4.71  thf('61', plain,
% 4.47/4.71      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 4.47/4.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.47/4.71  thf(dt_k1_partfun1, axiom,
% 4.47/4.71    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 4.47/4.71     ( ( ( v1_funct_1 @ E ) & 
% 4.47/4.71         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.47/4.71         ( v1_funct_1 @ F ) & 
% 4.47/4.71         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 4.47/4.71       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 4.47/4.71         ( m1_subset_1 @
% 4.47/4.71           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 4.47/4.71           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 4.47/4.71  thf('62', plain,
% 4.47/4.71      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 4.47/4.71         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 4.47/4.71          | ~ (v1_funct_1 @ X34)
% 4.47/4.71          | ~ (v1_funct_1 @ X37)
% 4.47/4.71          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 4.47/4.71          | (m1_subset_1 @ (k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37) @ 
% 4.47/4.71             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X39))))),
% 4.47/4.71      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 4.47/4.71  thf('63', plain,
% 4.47/4.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.47/4.71         ((m1_subset_1 @ 
% 4.47/4.71           (k1_partfun1 @ sk_A @ sk_B_2 @ X2 @ X0 @ sk_C_1 @ X1) @ 
% 4.47/4.71           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 4.47/4.71          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 4.47/4.71          | ~ (v1_funct_1 @ X1)
% 4.47/4.71          | ~ (v1_funct_1 @ sk_C_1))),
% 4.47/4.71      inference('sup-', [status(thm)], ['61', '62'])).
% 4.47/4.71  thf('64', plain, ((v1_funct_1 @ sk_C_1)),
% 4.47/4.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.47/4.71  thf('65', plain,
% 4.47/4.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.47/4.71         ((m1_subset_1 @ 
% 4.47/4.71           (k1_partfun1 @ sk_A @ sk_B_2 @ X2 @ X0 @ sk_C_1 @ X1) @ 
% 4.47/4.71           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 4.47/4.71          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 4.47/4.71          | ~ (v1_funct_1 @ X1))),
% 4.47/4.71      inference('demod', [status(thm)], ['63', '64'])).
% 4.47/4.71  thf('66', plain,
% 4.47/4.71      ((~ (v1_funct_1 @ sk_D)
% 4.47/4.71        | (m1_subset_1 @ 
% 4.47/4.71           (k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ sk_D) @ 
% 4.47/4.71           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 4.47/4.71      inference('sup-', [status(thm)], ['60', '65'])).
% 4.47/4.71  thf('67', plain, ((v1_funct_1 @ sk_D)),
% 4.47/4.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.47/4.71  thf('68', plain,
% 4.47/4.71      ((m1_subset_1 @ 
% 4.47/4.71        (k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ sk_D) @ 
% 4.47/4.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.47/4.71      inference('demod', [status(thm)], ['66', '67'])).
% 4.47/4.71  thf(redefinition_r2_relset_1, axiom,
% 4.47/4.71    (![A:$i,B:$i,C:$i,D:$i]:
% 4.47/4.71     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.47/4.71         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.47/4.71       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 4.47/4.71  thf('69', plain,
% 4.47/4.71      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 4.47/4.71         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 4.47/4.71          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 4.47/4.71          | ((X27) = (X30))
% 4.47/4.71          | ~ (r2_relset_1 @ X28 @ X29 @ X27 @ X30))),
% 4.47/4.71      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 4.47/4.71  thf('70', plain,
% 4.47/4.71      (![X0 : $i]:
% 4.47/4.71         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 4.47/4.71             (k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ sk_D) @ X0)
% 4.47/4.71          | ((k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ sk_D)
% 4.47/4.71              = (X0))
% 4.47/4.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 4.47/4.71      inference('sup-', [status(thm)], ['68', '69'])).
% 4.47/4.71  thf('71', plain,
% 4.47/4.71      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 4.47/4.71           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 4.47/4.71        | ((k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ sk_D)
% 4.47/4.71            = (k6_partfun1 @ sk_A)))),
% 4.47/4.71      inference('sup-', [status(thm)], ['59', '70'])).
% 4.47/4.71  thf('72', plain,
% 4.47/4.71      (![X31 : $i]:
% 4.47/4.71         (m1_subset_1 @ (k6_partfun1 @ X31) @ 
% 4.47/4.71          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 4.47/4.71      inference('demod', [status(thm)], ['4', '5'])).
% 4.47/4.71  thf('73', plain,
% 4.47/4.71      (((k1_partfun1 @ sk_A @ sk_B_2 @ sk_B_2 @ sk_A @ sk_C_1 @ sk_D)
% 4.47/4.71         = (k6_partfun1 @ sk_A))),
% 4.47/4.71      inference('demod', [status(thm)], ['71', '72'])).
% 4.47/4.71  thf('74', plain,
% 4.47/4.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_A)))),
% 4.47/4.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.47/4.71  thf(t26_funct_2, axiom,
% 4.47/4.71    (![A:$i,B:$i,C:$i,D:$i]:
% 4.47/4.71     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 4.47/4.71         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.47/4.71       ( ![E:$i]:
% 4.47/4.71         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 4.47/4.71             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 4.47/4.71           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 4.47/4.71             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 4.47/4.71               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 4.47/4.71  thf('75', plain,
% 4.47/4.71      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 4.47/4.71         (~ (v1_funct_1 @ X45)
% 4.47/4.71          | ~ (v1_funct_2 @ X45 @ X46 @ X47)
% 4.47/4.71          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 4.47/4.71          | ~ (v2_funct_1 @ (k1_partfun1 @ X48 @ X46 @ X46 @ X47 @ X49 @ X45))
% 4.47/4.71          | (v2_funct_1 @ X49)
% 4.47/4.71          | ((X47) = (k1_xboole_0))
% 4.47/4.71          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X46)))
% 4.47/4.71          | ~ (v1_funct_2 @ X49 @ X48 @ X46)
% 4.47/4.71          | ~ (v1_funct_1 @ X49))),
% 4.47/4.71      inference('cnf', [status(esa)], [t26_funct_2])).
% 4.47/4.71  thf('76', plain,
% 4.47/4.71      (![X0 : $i, X1 : $i]:
% 4.47/4.71         (~ (v1_funct_1 @ X0)
% 4.47/4.71          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_2)
% 4.47/4.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_2)))
% 4.47/4.71          | ((sk_A) = (k1_xboole_0))
% 4.47/4.71          | (v2_funct_1 @ X0)
% 4.47/4.71          | ~ (v2_funct_1 @ 
% 4.47/4.71               (k1_partfun1 @ X1 @ sk_B_2 @ sk_B_2 @ sk_A @ X0 @ sk_D))
% 4.47/4.71          | ~ (v1_funct_2 @ sk_D @ sk_B_2 @ sk_A)
% 4.47/4.71          | ~ (v1_funct_1 @ sk_D))),
% 4.47/4.71      inference('sup-', [status(thm)], ['74', '75'])).
% 4.47/4.71  thf('77', plain, ((v1_funct_2 @ sk_D @ sk_B_2 @ sk_A)),
% 4.47/4.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.47/4.71  thf('78', plain, ((v1_funct_1 @ sk_D)),
% 4.47/4.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.47/4.71  thf('79', plain,
% 4.47/4.71      (![X0 : $i, X1 : $i]:
% 4.47/4.71         (~ (v1_funct_1 @ X0)
% 4.47/4.71          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_2)
% 4.47/4.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_2)))
% 4.47/4.71          | ((sk_A) = (k1_xboole_0))
% 4.47/4.71          | (v2_funct_1 @ X0)
% 4.47/4.71          | ~ (v2_funct_1 @ 
% 4.47/4.71               (k1_partfun1 @ X1 @ sk_B_2 @ sk_B_2 @ sk_A @ X0 @ sk_D)))),
% 4.47/4.71      inference('demod', [status(thm)], ['76', '77', '78'])).
% 4.47/4.71  thf('80', plain,
% 4.47/4.71      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 4.47/4.71        | (v2_funct_1 @ sk_C_1)
% 4.47/4.71        | ((sk_A) = (k1_xboole_0))
% 4.47/4.71        | ~ (m1_subset_1 @ sk_C_1 @ 
% 4.47/4.71             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))
% 4.47/4.71        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2)
% 4.47/4.71        | ~ (v1_funct_1 @ sk_C_1))),
% 4.47/4.71      inference('sup-', [status(thm)], ['73', '79'])).
% 4.47/4.71  thf('81', plain, (![X12 : $i]: (v2_funct_1 @ (k6_partfun1 @ X12))),
% 4.47/4.71      inference('demod', [status(thm)], ['14', '15'])).
% 4.47/4.71  thf('82', plain,
% 4.47/4.71      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 4.47/4.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.47/4.71  thf('83', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2)),
% 4.47/4.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.47/4.71  thf('84', plain, ((v1_funct_1 @ sk_C_1)),
% 4.47/4.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.47/4.71  thf('85', plain, (((v2_funct_1 @ sk_C_1) | ((sk_A) = (k1_xboole_0)))),
% 4.47/4.71      inference('demod', [status(thm)], ['80', '81', '82', '83', '84'])).
% 4.47/4.71  thf('86', plain, ((~ (v2_funct_1 @ sk_C_1)) <= (~ ((v2_funct_1 @ sk_C_1)))),
% 4.47/4.71      inference('split', [status(esa)], ['19'])).
% 4.47/4.71  thf('87', plain, (~ ((v2_funct_1 @ sk_C_1))),
% 4.47/4.71      inference('sat_resolution*', [status(thm)], ['49', '50'])).
% 4.47/4.71  thf('88', plain, (~ (v2_funct_1 @ sk_C_1)),
% 4.47/4.71      inference('simpl_trail', [status(thm)], ['86', '87'])).
% 4.47/4.71  thf('89', plain, (((sk_A) = (k1_xboole_0))),
% 4.47/4.71      inference('clc', [status(thm)], ['85', '88'])).
% 4.47/4.71  thf('90', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.47/4.71      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.47/4.71  thf('91', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C_1)),
% 4.47/4.71      inference('demod', [status(thm)], ['58', '89', '90'])).
% 4.47/4.71  thf('92', plain, ((v1_xboole_0 @ sk_C_1)),
% 4.47/4.71      inference('sup-', [status(thm)], ['53', '91'])).
% 4.47/4.71  thf('93', plain, ($false), inference('demod', [status(thm)], ['52', '92'])).
% 4.47/4.71  
% 4.47/4.71  % SZS output end Refutation
% 4.47/4.71  
% 4.47/4.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
