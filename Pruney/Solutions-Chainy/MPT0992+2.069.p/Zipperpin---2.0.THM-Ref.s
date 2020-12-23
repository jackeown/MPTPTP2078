%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NnjcmLj4fd

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:44 EST 2020

% Result     : Theorem 22.76s
% Output     : Refutation 22.76s
% Verified   : 
% Statistics : Number of formulae       :  208 (1470 expanded)
%              Number of leaves         :   42 ( 450 expanded)
%              Depth                    :   25
%              Number of atoms          : 1579 (18378 expanded)
%              Number of equality atoms :  124 (1324 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(t38_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ C @ A )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) )
            & ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B )
            & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ D @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( r1_tarski @ C @ A )
         => ( ( ( B = k1_xboole_0 )
              & ( A != k1_xboole_0 ) )
            | ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) )
              & ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B )
              & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ D @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) )
        & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('2',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X37 @ X38 @ X36 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('8',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( v1_funct_1 @ X40 )
      | ( ( k2_partfun1 @ X41 @ X42 @ X40 @ X43 )
        = ( k7_relat_1 @ X40 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('13',plain,
    ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['6','11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ( m1_subset_1 @ ( k2_partfun1 @ X37 @ X38 @ X36 @ X39 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('20',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('21',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v5_relat_1 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('23',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v5_relat_1 @ X9 @ X10 )
      | ( r1_tarski @ ( k2_relat_1 @ X9 ) @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('26',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('28',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['24','29'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('31',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('32',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X25 ) @ X26 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X25 ) @ X27 )
      | ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('40',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['34','35','40'])).

thf('42',plain,(
    ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['13','41'])).

thf('43',plain,(
    r1_tarski @ sk_C @ sk_A ),
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
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('44',plain,(
    ! [X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 )
      | ( X28 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('45',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X15 @ X16 ) @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('46',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('48',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('49',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('51',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','51'])).

thf('53',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['49','50'])).

thf('56',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','51'])).

thf('58',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['57','60'])).

thf('62',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['49','50'])).

thf('63',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['56','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['44','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( zip_tseitin_0 @ X33 @ X34 )
      | ( zip_tseitin_1 @ X35 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('68',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_2 @ X32 @ X30 @ X31 )
      | ( X30
        = ( k1_relset_1 @ X30 @ X31 @ X32 ) )
      | ~ ( zip_tseitin_1 @ X32 @ X31 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('72',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('74',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_relset_1 @ X23 @ X24 @ X22 )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('75',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['72','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['69','76'])).

thf('78',plain,(
    ! [X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 )
      | ( X28 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( sk_B = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('82',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['82'])).

thf('84',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['82'])).

thf('85',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('86',plain,
    ( ( ~ ( m1_subset_1 @ ( k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
      | ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['82'])).

thf('88',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('91',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['89','90'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('92',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('93',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('95',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['82'])).

thf('97',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('100',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('102',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['56','63'])).

thf('105',plain,(
    ! [X4: $i,X6: $i] :
      ( ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('106',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( v1_funct_1 @ X40 )
      | ( ( k2_partfun1 @ X41 @ X42 @ X40 @ X43 )
        = ( k7_relat_1 @ X40 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
        = ( k7_relat_1 @ k1_xboole_0 @ X2 ) )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','51'])).

thf('110',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['103','110'])).

thf('112',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('113',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('114',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('115',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['82'])).

thf('116',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('117',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('118',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['103','110'])).

thf('119',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('120',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('121',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_relset_1 @ X23 @ X24 @ X22 )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['61','62'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( X30
       != ( k1_relset_1 @ X30 @ X31 @ X32 ) )
      | ( v1_funct_2 @ X32 @ X30 @ X31 )
      | ~ ( zip_tseitin_1 @ X32 @ X31 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,(
    ! [X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 )
      | ( X29 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('129',plain,(
    ! [X28: $i] :
      ( zip_tseitin_0 @ X28 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('131',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( zip_tseitin_0 @ X33 @ X34 )
      | ( zip_tseitin_1 @ X35 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['129','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['127','133'])).

thf('135',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['86','95','100','111','112','113','114','115','116','117','118','119','134'])).

thf('136',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['82'])).

thf('137',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['135','136'])).

thf('138',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['83','137'])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['81','138'])).

thf('140',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('141',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['72','75'])).

thf('143',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['141','142'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('144',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X17 @ ( k1_relat_1 @ X18 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X18 @ X17 ) )
        = X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('145',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_D )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['38','39'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['43','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['34','35','40'])).

thf('150',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_relset_1 @ X23 @ X24 @ X22 )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ X0 @ sk_B @ ( k7_relat_1 @ sk_D @ X0 ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( X30
       != ( k1_relset_1 @ X30 @ X31 @ X32 ) )
      | ( v1_funct_2 @ X32 @ X30 @ X31 )
      | ~ ( zip_tseitin_1 @ X32 @ X31 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( X0
       != ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) )
      | ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B @ X0 )
      | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 )
      | ( X28 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('155',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['34','35','40'])).

thf('156',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( zip_tseitin_0 @ X33 @ X34 )
      | ( zip_tseitin_1 @ X35 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B @ X0 )
      | ~ ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['154','157'])).

thf('159',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['83','137'])).

thf('160',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B @ X0 ) ),
    inference('simplify_reflect-',[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( X0
       != ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) )
      | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['153','160'])).

thf('162',plain,
    ( ( sk_C != sk_C )
    | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['148','161'])).

thf('163',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,(
    $false ),
    inference(demod,[status(thm)],['42','163'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NnjcmLj4fd
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:10:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 22.76/22.98  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 22.76/22.98  % Solved by: fo/fo7.sh
% 22.76/22.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 22.76/22.98  % done 12961 iterations in 22.511s
% 22.76/22.98  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 22.76/22.98  % SZS output start Refutation
% 22.76/22.98  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 22.76/22.98  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 22.76/22.98  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 22.76/22.98  thf(sk_C_type, type, sk_C: $i).
% 22.76/22.98  thf(sk_B_type, type, sk_B: $i).
% 22.76/22.98  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 22.76/22.98  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 22.76/22.98  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 22.76/22.98  thf(sk_A_type, type, sk_A: $i).
% 22.76/22.98  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 22.76/22.98  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 22.76/22.98  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 22.76/22.98  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 22.76/22.98  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 22.76/22.98  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 22.76/22.98  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 22.76/22.98  thf(sk_D_type, type, sk_D: $i).
% 22.76/22.98  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 22.76/22.98  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 22.76/22.98  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 22.76/22.98  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 22.76/22.98  thf(t38_funct_2, conjecture,
% 22.76/22.98    (![A:$i,B:$i,C:$i,D:$i]:
% 22.76/22.98     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 22.76/22.98         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 22.76/22.98       ( ( r1_tarski @ C @ A ) =>
% 22.76/22.98         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 22.76/22.98           ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 22.76/22.98             ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 22.76/22.98             ( m1_subset_1 @
% 22.76/22.98               ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 22.76/22.98               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ))).
% 22.76/22.98  thf(zf_stmt_0, negated_conjecture,
% 22.76/22.98    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 22.76/22.98        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 22.76/22.98            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 22.76/22.98          ( ( r1_tarski @ C @ A ) =>
% 22.76/22.98            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 22.76/22.98              ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 22.76/22.98                ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 22.76/22.98                ( m1_subset_1 @
% 22.76/22.98                  ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 22.76/22.98                  ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) )),
% 22.76/22.98    inference('cnf.neg', [status(esa)], [t38_funct_2])).
% 22.76/22.98  thf('0', plain,
% 22.76/22.98      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C))
% 22.76/22.98        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 22.76/22.98             sk_B)
% 22.76/22.98        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 22.76/22.98             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 22.76/22.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.76/22.98  thf('1', plain,
% 22.76/22.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 22.76/22.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.76/22.98  thf(dt_k2_partfun1, axiom,
% 22.76/22.98    (![A:$i,B:$i,C:$i,D:$i]:
% 22.76/22.98     ( ( ( v1_funct_1 @ C ) & 
% 22.76/22.98         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 22.76/22.98       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 22.76/22.98         ( m1_subset_1 @
% 22.76/22.98           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 22.76/22.98           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 22.76/22.98  thf('2', plain,
% 22.76/22.98      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 22.76/22.98         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 22.76/22.98          | ~ (v1_funct_1 @ X36)
% 22.76/22.98          | (v1_funct_1 @ (k2_partfun1 @ X37 @ X38 @ X36 @ X39)))),
% 22.76/22.98      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 22.76/22.98  thf('3', plain,
% 22.76/22.98      (![X0 : $i]:
% 22.76/22.98         ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))
% 22.76/22.98          | ~ (v1_funct_1 @ sk_D))),
% 22.76/22.98      inference('sup-', [status(thm)], ['1', '2'])).
% 22.76/22.98  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 22.76/22.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.76/22.98  thf('5', plain,
% 22.76/22.98      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0))),
% 22.76/22.98      inference('demod', [status(thm)], ['3', '4'])).
% 22.76/22.98  thf('6', plain,
% 22.76/22.98      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)
% 22.76/22.98        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 22.76/22.98             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 22.76/22.98      inference('demod', [status(thm)], ['0', '5'])).
% 22.76/22.98  thf('7', plain,
% 22.76/22.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 22.76/22.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.76/22.98  thf(redefinition_k2_partfun1, axiom,
% 22.76/22.98    (![A:$i,B:$i,C:$i,D:$i]:
% 22.76/22.98     ( ( ( v1_funct_1 @ C ) & 
% 22.76/22.98         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 22.76/22.98       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 22.76/22.98  thf('8', plain,
% 22.76/22.98      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 22.76/22.98         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 22.76/22.98          | ~ (v1_funct_1 @ X40)
% 22.76/22.98          | ((k2_partfun1 @ X41 @ X42 @ X40 @ X43) = (k7_relat_1 @ X40 @ X43)))),
% 22.76/22.98      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 22.76/22.98  thf('9', plain,
% 22.76/22.98      (![X0 : $i]:
% 22.76/22.98         (((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))
% 22.76/22.98          | ~ (v1_funct_1 @ sk_D))),
% 22.76/22.98      inference('sup-', [status(thm)], ['7', '8'])).
% 22.76/22.98  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 22.76/22.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.76/22.98  thf('11', plain,
% 22.76/22.98      (![X0 : $i]:
% 22.76/22.98         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 22.76/22.98      inference('demod', [status(thm)], ['9', '10'])).
% 22.76/22.98  thf('12', plain,
% 22.76/22.98      (![X0 : $i]:
% 22.76/22.98         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 22.76/22.98      inference('demod', [status(thm)], ['9', '10'])).
% 22.76/22.98  thf('13', plain,
% 22.76/22.98      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)
% 22.76/22.98        | ~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 22.76/22.98             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 22.76/22.98      inference('demod', [status(thm)], ['6', '11', '12'])).
% 22.76/22.98  thf('14', plain,
% 22.76/22.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 22.76/22.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.76/22.98  thf('15', plain,
% 22.76/22.98      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 22.76/22.98         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 22.76/22.98          | ~ (v1_funct_1 @ X36)
% 22.76/22.98          | (m1_subset_1 @ (k2_partfun1 @ X37 @ X38 @ X36 @ X39) @ 
% 22.76/22.98             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 22.76/22.98      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 22.76/22.98  thf('16', plain,
% 22.76/22.98      (![X0 : $i]:
% 22.76/22.98         ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 22.76/22.98           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 22.76/22.98          | ~ (v1_funct_1 @ sk_D))),
% 22.76/22.98      inference('sup-', [status(thm)], ['14', '15'])).
% 22.76/22.98  thf('17', plain, ((v1_funct_1 @ sk_D)),
% 22.76/22.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.76/22.98  thf('18', plain,
% 22.76/22.98      (![X0 : $i]:
% 22.76/22.98         (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) @ 
% 22.76/22.98          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 22.76/22.98      inference('demod', [status(thm)], ['16', '17'])).
% 22.76/22.98  thf('19', plain,
% 22.76/22.98      (![X0 : $i]:
% 22.76/22.98         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 22.76/22.98      inference('demod', [status(thm)], ['9', '10'])).
% 22.76/22.98  thf('20', plain,
% 22.76/22.98      (![X0 : $i]:
% 22.76/22.98         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 22.76/22.98          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 22.76/22.98      inference('demod', [status(thm)], ['18', '19'])).
% 22.76/22.98  thf(cc2_relset_1, axiom,
% 22.76/22.98    (![A:$i,B:$i,C:$i]:
% 22.76/22.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 22.76/22.98       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 22.76/22.98  thf('21', plain,
% 22.76/22.98      (![X19 : $i, X20 : $i, X21 : $i]:
% 22.76/22.98         ((v5_relat_1 @ X19 @ X21)
% 22.76/22.98          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 22.76/22.98      inference('cnf', [status(esa)], [cc2_relset_1])).
% 22.76/22.98  thf('22', plain,
% 22.76/22.98      (![X0 : $i]: (v5_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B)),
% 22.76/22.98      inference('sup-', [status(thm)], ['20', '21'])).
% 22.76/22.98  thf(d19_relat_1, axiom,
% 22.76/22.98    (![A:$i,B:$i]:
% 22.76/22.98     ( ( v1_relat_1 @ B ) =>
% 22.76/22.98       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 22.76/22.98  thf('23', plain,
% 22.76/22.98      (![X9 : $i, X10 : $i]:
% 22.76/22.98         (~ (v5_relat_1 @ X9 @ X10)
% 22.76/22.98          | (r1_tarski @ (k2_relat_1 @ X9) @ X10)
% 22.76/22.98          | ~ (v1_relat_1 @ X9))),
% 22.76/22.98      inference('cnf', [status(esa)], [d19_relat_1])).
% 22.76/22.98  thf('24', plain,
% 22.76/22.98      (![X0 : $i]:
% 22.76/22.98         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 22.76/22.98          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 22.76/22.98      inference('sup-', [status(thm)], ['22', '23'])).
% 22.76/22.98  thf('25', plain,
% 22.76/22.98      (![X0 : $i]:
% 22.76/22.98         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 22.76/22.98          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 22.76/22.98      inference('demod', [status(thm)], ['18', '19'])).
% 22.76/22.98  thf(cc2_relat_1, axiom,
% 22.76/22.98    (![A:$i]:
% 22.76/22.98     ( ( v1_relat_1 @ A ) =>
% 22.76/22.98       ( ![B:$i]:
% 22.76/22.98         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 22.76/22.98  thf('26', plain,
% 22.76/22.98      (![X7 : $i, X8 : $i]:
% 22.76/22.98         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 22.76/22.98          | (v1_relat_1 @ X7)
% 22.76/22.98          | ~ (v1_relat_1 @ X8))),
% 22.76/22.98      inference('cnf', [status(esa)], [cc2_relat_1])).
% 22.76/22.98  thf('27', plain,
% 22.76/22.98      (![X0 : $i]:
% 22.76/22.98         (~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 22.76/22.98          | (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))),
% 22.76/22.98      inference('sup-', [status(thm)], ['25', '26'])).
% 22.76/22.98  thf(fc6_relat_1, axiom,
% 22.76/22.98    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 22.76/22.98  thf('28', plain,
% 22.76/22.98      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 22.76/22.98      inference('cnf', [status(esa)], [fc6_relat_1])).
% 22.76/22.98  thf('29', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 22.76/22.98      inference('demod', [status(thm)], ['27', '28'])).
% 22.76/22.98  thf('30', plain,
% 22.76/22.98      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 22.76/22.98      inference('demod', [status(thm)], ['24', '29'])).
% 22.76/22.98  thf(t87_relat_1, axiom,
% 22.76/22.98    (![A:$i,B:$i]:
% 22.76/22.98     ( ( v1_relat_1 @ B ) =>
% 22.76/22.98       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 22.76/22.98  thf('31', plain,
% 22.76/22.98      (![X13 : $i, X14 : $i]:
% 22.76/22.98         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X13 @ X14)) @ X14)
% 22.76/22.98          | ~ (v1_relat_1 @ X13))),
% 22.76/22.98      inference('cnf', [status(esa)], [t87_relat_1])).
% 22.76/22.98  thf(t11_relset_1, axiom,
% 22.76/22.98    (![A:$i,B:$i,C:$i]:
% 22.76/22.98     ( ( v1_relat_1 @ C ) =>
% 22.76/22.98       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 22.76/22.98           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 22.76/22.98         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 22.76/22.98  thf('32', plain,
% 22.76/22.98      (![X25 : $i, X26 : $i, X27 : $i]:
% 22.76/22.98         (~ (r1_tarski @ (k1_relat_1 @ X25) @ X26)
% 22.76/22.98          | ~ (r1_tarski @ (k2_relat_1 @ X25) @ X27)
% 22.76/22.98          | (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 22.76/22.98          | ~ (v1_relat_1 @ X25))),
% 22.76/22.98      inference('cnf', [status(esa)], [t11_relset_1])).
% 22.76/22.98  thf('33', plain,
% 22.76/22.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 22.76/22.98         (~ (v1_relat_1 @ X1)
% 22.76/22.98          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 22.76/22.98          | (m1_subset_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 22.76/22.98             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))
% 22.76/22.98          | ~ (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2))),
% 22.76/22.98      inference('sup-', [status(thm)], ['31', '32'])).
% 22.76/22.98  thf('34', plain,
% 22.76/22.98      (![X0 : $i]:
% 22.76/22.98         ((m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 22.76/22.98           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 22.76/22.98          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 22.76/22.98          | ~ (v1_relat_1 @ sk_D))),
% 22.76/22.98      inference('sup-', [status(thm)], ['30', '33'])).
% 22.76/22.98  thf('35', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 22.76/22.98      inference('demod', [status(thm)], ['27', '28'])).
% 22.76/22.98  thf('36', plain,
% 22.76/22.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 22.76/22.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.76/22.98  thf('37', plain,
% 22.76/22.98      (![X7 : $i, X8 : $i]:
% 22.76/22.98         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 22.76/22.98          | (v1_relat_1 @ X7)
% 22.76/22.98          | ~ (v1_relat_1 @ X8))),
% 22.76/22.98      inference('cnf', [status(esa)], [cc2_relat_1])).
% 22.76/22.98  thf('38', plain,
% 22.76/22.98      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 22.76/22.98      inference('sup-', [status(thm)], ['36', '37'])).
% 22.76/22.98  thf('39', plain,
% 22.76/22.98      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 22.76/22.98      inference('cnf', [status(esa)], [fc6_relat_1])).
% 22.76/22.98  thf('40', plain, ((v1_relat_1 @ sk_D)),
% 22.76/22.98      inference('demod', [status(thm)], ['38', '39'])).
% 22.76/22.98  thf('41', plain,
% 22.76/22.98      (![X0 : $i]:
% 22.76/22.98         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 22.76/22.98          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))),
% 22.76/22.98      inference('demod', [status(thm)], ['34', '35', '40'])).
% 22.76/22.98  thf('42', plain, (~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)),
% 22.76/22.98      inference('demod', [status(thm)], ['13', '41'])).
% 22.76/22.98  thf('43', plain, ((r1_tarski @ sk_C @ sk_A)),
% 22.76/22.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.76/22.98  thf(d1_funct_2, axiom,
% 22.76/22.98    (![A:$i,B:$i,C:$i]:
% 22.76/22.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 22.76/22.98       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 22.76/22.98           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 22.76/22.98             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 22.76/22.98         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 22.76/22.98           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 22.76/22.98             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 22.76/22.98  thf(zf_stmt_1, axiom,
% 22.76/22.98    (![B:$i,A:$i]:
% 22.76/22.98     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 22.76/22.98       ( zip_tseitin_0 @ B @ A ) ))).
% 22.76/22.98  thf('44', plain,
% 22.76/22.98      (![X28 : $i, X29 : $i]:
% 22.76/22.98         ((zip_tseitin_0 @ X28 @ X29) | ((X28) = (k1_xboole_0)))),
% 22.76/22.98      inference('cnf', [status(esa)], [zf_stmt_1])).
% 22.76/22.98  thf(t88_relat_1, axiom,
% 22.76/22.98    (![A:$i,B:$i]:
% 22.76/22.98     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 22.76/22.98  thf('45', plain,
% 22.76/22.98      (![X15 : $i, X16 : $i]:
% 22.76/22.98         ((r1_tarski @ (k7_relat_1 @ X15 @ X16) @ X15) | ~ (v1_relat_1 @ X15))),
% 22.76/22.98      inference('cnf', [status(esa)], [t88_relat_1])).
% 22.76/22.98  thf(t3_xboole_1, axiom,
% 22.76/22.98    (![A:$i]:
% 22.76/22.98     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 22.76/22.98  thf('46', plain,
% 22.76/22.98      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 22.76/22.98      inference('cnf', [status(esa)], [t3_xboole_1])).
% 22.76/22.98  thf('47', plain,
% 22.76/22.98      (![X0 : $i]:
% 22.76/22.98         (~ (v1_relat_1 @ k1_xboole_0)
% 22.76/22.98          | ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 22.76/22.98      inference('sup-', [status(thm)], ['45', '46'])).
% 22.76/22.98  thf(t113_zfmisc_1, axiom,
% 22.76/22.98    (![A:$i,B:$i]:
% 22.76/22.98     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 22.76/22.98       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 22.76/22.98  thf('48', plain,
% 22.76/22.98      (![X2 : $i, X3 : $i]:
% 22.76/22.98         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 22.76/22.98      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 22.76/22.98  thf('49', plain,
% 22.76/22.98      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 22.76/22.98      inference('simplify', [status(thm)], ['48'])).
% 22.76/22.98  thf('50', plain,
% 22.76/22.98      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 22.76/22.98      inference('cnf', [status(esa)], [fc6_relat_1])).
% 22.76/22.98  thf('51', plain, ((v1_relat_1 @ k1_xboole_0)),
% 22.76/22.98      inference('sup+', [status(thm)], ['49', '50'])).
% 22.76/22.98  thf('52', plain,
% 22.76/22.98      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 22.76/22.98      inference('demod', [status(thm)], ['47', '51'])).
% 22.76/22.98  thf('53', plain,
% 22.76/22.98      (![X13 : $i, X14 : $i]:
% 22.76/22.98         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X13 @ X14)) @ X14)
% 22.76/22.98          | ~ (v1_relat_1 @ X13))),
% 22.76/22.98      inference('cnf', [status(esa)], [t87_relat_1])).
% 22.76/22.98  thf('54', plain,
% 22.76/22.98      (![X0 : $i]:
% 22.76/22.98         ((r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)
% 22.76/22.98          | ~ (v1_relat_1 @ k1_xboole_0))),
% 22.76/22.98      inference('sup+', [status(thm)], ['52', '53'])).
% 22.76/22.98  thf('55', plain, ((v1_relat_1 @ k1_xboole_0)),
% 22.76/22.98      inference('sup+', [status(thm)], ['49', '50'])).
% 22.76/22.98  thf('56', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 22.76/22.98      inference('demod', [status(thm)], ['54', '55'])).
% 22.76/22.98  thf('57', plain,
% 22.76/22.98      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 22.76/22.98      inference('demod', [status(thm)], ['47', '51'])).
% 22.76/22.98  thf('58', plain,
% 22.76/22.98      (![X13 : $i, X14 : $i]:
% 22.76/22.98         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X13 @ X14)) @ X14)
% 22.76/22.98          | ~ (v1_relat_1 @ X13))),
% 22.76/22.98      inference('cnf', [status(esa)], [t87_relat_1])).
% 22.76/22.98  thf('59', plain,
% 22.76/22.98      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 22.76/22.98      inference('cnf', [status(esa)], [t3_xboole_1])).
% 22.76/22.98  thf('60', plain,
% 22.76/22.98      (![X0 : $i]:
% 22.76/22.98         (~ (v1_relat_1 @ X0)
% 22.76/22.98          | ((k1_relat_1 @ (k7_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 22.76/22.98      inference('sup-', [status(thm)], ['58', '59'])).
% 22.76/22.98  thf('61', plain,
% 22.76/22.98      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 22.76/22.98        | ~ (v1_relat_1 @ k1_xboole_0))),
% 22.76/22.98      inference('sup+', [status(thm)], ['57', '60'])).
% 22.76/22.98  thf('62', plain, ((v1_relat_1 @ k1_xboole_0)),
% 22.76/22.98      inference('sup+', [status(thm)], ['49', '50'])).
% 22.76/22.98  thf('63', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 22.76/22.98      inference('demod', [status(thm)], ['61', '62'])).
% 22.76/22.98  thf('64', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 22.76/22.98      inference('demod', [status(thm)], ['56', '63'])).
% 22.76/22.98  thf('65', plain,
% 22.76/22.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 22.76/22.98         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 22.76/22.98      inference('sup+', [status(thm)], ['44', '64'])).
% 22.76/22.98  thf('66', plain,
% 22.76/22.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 22.76/22.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.76/22.98  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 22.76/22.98  thf(zf_stmt_3, axiom,
% 22.76/22.98    (![C:$i,B:$i,A:$i]:
% 22.76/22.98     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 22.76/22.98       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 22.76/22.98  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 22.76/22.98  thf(zf_stmt_5, axiom,
% 22.76/22.98    (![A:$i,B:$i,C:$i]:
% 22.76/22.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 22.76/22.98       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 22.76/22.98         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 22.76/22.98           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 22.76/22.98             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 22.76/22.98  thf('67', plain,
% 22.76/22.98      (![X33 : $i, X34 : $i, X35 : $i]:
% 22.76/22.98         (~ (zip_tseitin_0 @ X33 @ X34)
% 22.76/22.98          | (zip_tseitin_1 @ X35 @ X33 @ X34)
% 22.76/22.98          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33))))),
% 22.76/22.98      inference('cnf', [status(esa)], [zf_stmt_5])).
% 22.76/22.98  thf('68', plain,
% 22.76/22.98      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 22.76/22.98      inference('sup-', [status(thm)], ['66', '67'])).
% 22.76/22.98  thf('69', plain,
% 22.76/22.98      (![X0 : $i]:
% 22.76/22.98         ((r1_tarski @ sk_B @ X0) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 22.76/22.98      inference('sup-', [status(thm)], ['65', '68'])).
% 22.76/22.98  thf('70', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 22.76/22.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.76/22.98  thf('71', plain,
% 22.76/22.98      (![X30 : $i, X31 : $i, X32 : $i]:
% 22.76/22.98         (~ (v1_funct_2 @ X32 @ X30 @ X31)
% 22.76/22.98          | ((X30) = (k1_relset_1 @ X30 @ X31 @ X32))
% 22.76/22.98          | ~ (zip_tseitin_1 @ X32 @ X31 @ X30))),
% 22.76/22.98      inference('cnf', [status(esa)], [zf_stmt_3])).
% 22.76/22.98  thf('72', plain,
% 22.76/22.98      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 22.76/22.98        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 22.76/22.98      inference('sup-', [status(thm)], ['70', '71'])).
% 22.76/22.98  thf('73', plain,
% 22.76/22.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 22.76/22.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.76/22.98  thf(redefinition_k1_relset_1, axiom,
% 22.76/22.98    (![A:$i,B:$i,C:$i]:
% 22.76/22.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 22.76/22.98       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 22.76/22.98  thf('74', plain,
% 22.76/22.98      (![X22 : $i, X23 : $i, X24 : $i]:
% 22.76/22.98         (((k1_relset_1 @ X23 @ X24 @ X22) = (k1_relat_1 @ X22))
% 22.76/22.98          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 22.76/22.98      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 22.76/22.98  thf('75', plain,
% 22.76/22.98      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 22.76/22.98      inference('sup-', [status(thm)], ['73', '74'])).
% 22.76/22.98  thf('76', plain,
% 22.76/22.98      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 22.76/22.98      inference('demod', [status(thm)], ['72', '75'])).
% 22.76/22.98  thf('77', plain,
% 22.76/22.98      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 22.76/22.98      inference('sup-', [status(thm)], ['69', '76'])).
% 22.76/22.98  thf('78', plain,
% 22.76/22.98      (![X28 : $i, X29 : $i]:
% 22.76/22.98         ((zip_tseitin_0 @ X28 @ X29) | ((X28) = (k1_xboole_0)))),
% 22.76/22.98      inference('cnf', [status(esa)], [zf_stmt_1])).
% 22.76/22.98  thf('79', plain,
% 22.76/22.98      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 22.76/22.98      inference('cnf', [status(esa)], [t3_xboole_1])).
% 22.76/22.98  thf('80', plain,
% 22.76/22.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 22.76/22.98         (~ (r1_tarski @ X1 @ X0)
% 22.76/22.98          | (zip_tseitin_0 @ X0 @ X2)
% 22.76/22.98          | ((X1) = (k1_xboole_0)))),
% 22.76/22.98      inference('sup-', [status(thm)], ['78', '79'])).
% 22.76/22.98  thf('81', plain,
% 22.76/22.98      (![X0 : $i, X1 : $i]:
% 22.76/22.98         (((sk_A) = (k1_relat_1 @ sk_D))
% 22.76/22.98          | ((sk_B) = (k1_xboole_0))
% 22.76/22.98          | (zip_tseitin_0 @ X0 @ X1))),
% 22.76/22.98      inference('sup-', [status(thm)], ['77', '80'])).
% 22.76/22.98  thf('82', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 22.76/22.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.76/22.98  thf('83', plain,
% 22.76/22.98      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 22.76/22.98      inference('split', [status(esa)], ['82'])).
% 22.76/22.98  thf('84', plain,
% 22.76/22.98      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 22.76/22.98      inference('split', [status(esa)], ['82'])).
% 22.76/22.98  thf('85', plain,
% 22.76/22.98      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)
% 22.76/22.98        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 22.76/22.98             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 22.76/22.98      inference('demod', [status(thm)], ['0', '5'])).
% 22.76/22.98  thf('86', plain,
% 22.76/22.98      (((~ (m1_subset_1 @ (k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C) @ 
% 22.76/22.98            (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 22.76/22.98         | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 22.76/22.98              sk_B)))
% 22.76/22.98         <= ((((sk_A) = (k1_xboole_0))))),
% 22.76/22.98      inference('sup-', [status(thm)], ['84', '85'])).
% 22.76/22.98  thf('87', plain,
% 22.76/22.98      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 22.76/22.98      inference('split', [status(esa)], ['82'])).
% 22.76/22.98  thf('88', plain,
% 22.76/22.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 22.76/22.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.76/22.98  thf('89', plain,
% 22.76/22.98      (((m1_subset_1 @ sk_D @ 
% 22.76/22.98         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 22.76/22.98         <= ((((sk_A) = (k1_xboole_0))))),
% 22.76/22.98      inference('sup+', [status(thm)], ['87', '88'])).
% 22.76/22.98  thf('90', plain,
% 22.76/22.98      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 22.76/22.98      inference('simplify', [status(thm)], ['48'])).
% 22.76/22.98  thf('91', plain,
% 22.76/22.98      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 22.76/22.98         <= ((((sk_A) = (k1_xboole_0))))),
% 22.76/22.98      inference('demod', [status(thm)], ['89', '90'])).
% 22.76/22.98  thf(t3_subset, axiom,
% 22.76/22.98    (![A:$i,B:$i]:
% 22.76/22.98     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 22.76/22.98  thf('92', plain,
% 22.76/22.98      (![X4 : $i, X5 : $i]:
% 22.76/22.98         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 22.76/22.98      inference('cnf', [status(esa)], [t3_subset])).
% 22.76/22.98  thf('93', plain,
% 22.76/22.98      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 22.76/22.98      inference('sup-', [status(thm)], ['91', '92'])).
% 22.76/22.98  thf('94', plain,
% 22.76/22.98      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 22.76/22.98      inference('cnf', [status(esa)], [t3_xboole_1])).
% 22.76/22.98  thf('95', plain,
% 22.76/22.98      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 22.76/22.98      inference('sup-', [status(thm)], ['93', '94'])).
% 22.76/22.98  thf('96', plain,
% 22.76/22.98      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 22.76/22.98      inference('split', [status(esa)], ['82'])).
% 22.76/22.98  thf('97', plain, ((r1_tarski @ sk_C @ sk_A)),
% 22.76/22.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.76/22.98  thf('98', plain,
% 22.76/22.98      (((r1_tarski @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 22.76/22.98      inference('sup+', [status(thm)], ['96', '97'])).
% 22.76/22.98  thf('99', plain,
% 22.76/22.98      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 22.76/22.98      inference('cnf', [status(esa)], [t3_xboole_1])).
% 22.76/22.98  thf('100', plain,
% 22.76/22.98      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 22.76/22.98      inference('sup-', [status(thm)], ['98', '99'])).
% 22.76/22.98  thf('101', plain,
% 22.76/22.98      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 22.76/22.98      inference('sup-', [status(thm)], ['93', '94'])).
% 22.76/22.98  thf('102', plain, ((v1_funct_1 @ sk_D)),
% 22.76/22.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 22.76/22.98  thf('103', plain,
% 22.76/22.98      (((v1_funct_1 @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 22.76/22.98      inference('sup+', [status(thm)], ['101', '102'])).
% 22.76/22.98  thf('104', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 22.76/22.98      inference('demod', [status(thm)], ['56', '63'])).
% 22.76/22.98  thf('105', plain,
% 22.76/22.98      (![X4 : $i, X6 : $i]:
% 22.76/22.98         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X4 @ X6))),
% 22.76/22.98      inference('cnf', [status(esa)], [t3_subset])).
% 22.76/22.98  thf('106', plain,
% 22.76/22.98      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 22.76/22.98      inference('sup-', [status(thm)], ['104', '105'])).
% 22.76/22.98  thf('107', plain,
% 22.76/22.98      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 22.76/22.98         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 22.76/22.98          | ~ (v1_funct_1 @ X40)
% 22.76/22.98          | ((k2_partfun1 @ X41 @ X42 @ X40 @ X43) = (k7_relat_1 @ X40 @ X43)))),
% 22.76/22.98      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 22.76/22.98  thf('108', plain,
% 22.76/22.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 22.76/22.98         (((k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 22.76/22.98            = (k7_relat_1 @ k1_xboole_0 @ X2))
% 22.76/22.98          | ~ (v1_funct_1 @ k1_xboole_0))),
% 22.76/22.98      inference('sup-', [status(thm)], ['106', '107'])).
% 22.76/22.98  thf('109', plain,
% 22.76/22.98      (![X0 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 22.76/22.98      inference('demod', [status(thm)], ['47', '51'])).
% 22.76/22.98  thf('110', plain,
% 22.76/22.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 22.76/22.98         (((k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2) = (k1_xboole_0))
% 22.76/22.98          | ~ (v1_funct_1 @ k1_xboole_0))),
% 22.76/22.98      inference('demod', [status(thm)], ['108', '109'])).
% 22.76/22.98  thf('111', plain,
% 22.76/22.98      ((![X0 : $i, X1 : $i, X2 : $i]:
% 22.76/22.98          ((k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))
% 22.76/22.98         <= ((((sk_A) = (k1_xboole_0))))),
% 22.76/22.98      inference('sup-', [status(thm)], ['103', '110'])).
% 22.76/22.98  thf('112', plain,
% 22.76/22.98      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 22.76/22.98      inference('sup-', [status(thm)], ['98', '99'])).
% 22.76/22.98  thf('113', plain,
% 22.76/22.98      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 22.76/22.98      inference('simplify', [status(thm)], ['48'])).
% 22.76/22.98  thf('114', plain,
% 22.76/22.98      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 22.76/22.98      inference('sup-', [status(thm)], ['104', '105'])).
% 22.76/22.98  thf('115', plain,
% 22.76/22.98      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 22.76/22.98      inference('split', [status(esa)], ['82'])).
% 22.76/22.98  thf('116', plain,
% 22.76/22.98      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 22.76/22.98      inference('sup-', [status(thm)], ['93', '94'])).
% 22.76/22.98  thf('117', plain,
% 22.76/22.98      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 22.76/22.98      inference('sup-', [status(thm)], ['98', '99'])).
% 22.76/22.98  thf('118', plain,
% 22.76/22.98      ((![X0 : $i, X1 : $i, X2 : $i]:
% 22.76/22.98          ((k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))
% 22.76/22.98         <= ((((sk_A) = (k1_xboole_0))))),
% 22.76/22.98      inference('sup-', [status(thm)], ['103', '110'])).
% 22.76/22.98  thf('119', plain,
% 22.76/22.98      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 22.76/22.98      inference('sup-', [status(thm)], ['98', '99'])).
% 22.76/22.98  thf('120', plain,
% 22.76/22.98      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 22.76/22.98      inference('sup-', [status(thm)], ['104', '105'])).
% 22.76/22.98  thf('121', plain,
% 22.76/22.98      (![X22 : $i, X23 : $i, X24 : $i]:
% 22.76/22.98         (((k1_relset_1 @ X23 @ X24 @ X22) = (k1_relat_1 @ X22))
% 22.76/22.98          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 22.76/22.98      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 22.76/22.98  thf('122', plain,
% 22.76/22.98      (![X0 : $i, X1 : $i]:
% 22.76/22.98         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 22.76/22.98      inference('sup-', [status(thm)], ['120', '121'])).
% 22.76/22.98  thf('123', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 22.76/22.98      inference('demod', [status(thm)], ['61', '62'])).
% 22.76/22.98  thf('124', plain,
% 22.76/22.98      (![X0 : $i, X1 : $i]:
% 22.76/22.98         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 22.76/22.98      inference('demod', [status(thm)], ['122', '123'])).
% 22.76/22.98  thf('125', plain,
% 22.76/22.98      (![X30 : $i, X31 : $i, X32 : $i]:
% 22.76/22.98         (((X30) != (k1_relset_1 @ X30 @ X31 @ X32))
% 22.76/22.98          | (v1_funct_2 @ X32 @ X30 @ X31)
% 22.76/22.98          | ~ (zip_tseitin_1 @ X32 @ X31 @ X30))),
% 22.76/22.98      inference('cnf', [status(esa)], [zf_stmt_3])).
% 22.76/22.98  thf('126', plain,
% 22.76/22.98      (![X0 : $i, X1 : $i]:
% 22.76/22.98         (((X1) != (k1_xboole_0))
% 22.76/22.98          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 22.76/22.98          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 22.76/22.98      inference('sup-', [status(thm)], ['124', '125'])).
% 22.76/22.98  thf('127', plain,
% 22.76/22.98      (![X0 : $i]:
% 22.76/22.98         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 22.76/22.98          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 22.76/22.98      inference('simplify', [status(thm)], ['126'])).
% 22.76/22.98  thf('128', plain,
% 22.76/22.98      (![X28 : $i, X29 : $i]:
% 22.76/22.98         ((zip_tseitin_0 @ X28 @ X29) | ((X29) != (k1_xboole_0)))),
% 22.76/22.98      inference('cnf', [status(esa)], [zf_stmt_1])).
% 22.76/22.98  thf('129', plain, (![X28 : $i]: (zip_tseitin_0 @ X28 @ k1_xboole_0)),
% 22.76/22.98      inference('simplify', [status(thm)], ['128'])).
% 22.76/22.98  thf('130', plain,
% 22.76/22.98      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 22.76/22.98      inference('sup-', [status(thm)], ['104', '105'])).
% 22.76/22.98  thf('131', plain,
% 22.76/22.98      (![X33 : $i, X34 : $i, X35 : $i]:
% 22.76/22.98         (~ (zip_tseitin_0 @ X33 @ X34)
% 22.76/22.98          | (zip_tseitin_1 @ X35 @ X33 @ X34)
% 22.76/22.98          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33))))),
% 22.76/22.98      inference('cnf', [status(esa)], [zf_stmt_5])).
% 22.76/22.98  thf('132', plain,
% 22.76/22.98      (![X0 : $i, X1 : $i]:
% 22.76/22.98         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 22.76/22.98      inference('sup-', [status(thm)], ['130', '131'])).
% 22.76/22.98  thf('133', plain,
% 22.76/22.98      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 22.76/22.98      inference('sup-', [status(thm)], ['129', '132'])).
% 22.76/22.98  thf('134', plain,
% 22.76/22.98      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 22.76/22.98      inference('demod', [status(thm)], ['127', '133'])).
% 22.76/22.98  thf('135', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 22.76/22.98      inference('demod', [status(thm)],
% 22.76/22.98                ['86', '95', '100', '111', '112', '113', '114', '115', '116', 
% 22.76/22.98                 '117', '118', '119', '134'])).
% 22.76/22.98  thf('136', plain,
% 22.76/22.98      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 22.76/22.98      inference('split', [status(esa)], ['82'])).
% 22.76/22.98  thf('137', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 22.76/22.98      inference('sat_resolution*', [status(thm)], ['135', '136'])).
% 22.76/22.98  thf('138', plain, (((sk_B) != (k1_xboole_0))),
% 22.76/22.98      inference('simpl_trail', [status(thm)], ['83', '137'])).
% 22.76/22.98  thf('139', plain,
% 22.76/22.98      (![X0 : $i, X1 : $i]:
% 22.76/22.98         (((sk_A) = (k1_relat_1 @ sk_D)) | (zip_tseitin_0 @ X0 @ X1))),
% 22.76/22.98      inference('simplify_reflect-', [status(thm)], ['81', '138'])).
% 22.76/22.98  thf('140', plain,
% 22.76/22.98      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 22.76/22.98      inference('sup-', [status(thm)], ['66', '67'])).
% 22.76/22.98  thf('141', plain,
% 22.76/22.98      ((((sk_A) = (k1_relat_1 @ sk_D)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 22.76/22.98      inference('sup-', [status(thm)], ['139', '140'])).
% 22.76/22.98  thf('142', plain,
% 22.76/22.98      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 22.76/22.98      inference('demod', [status(thm)], ['72', '75'])).
% 22.76/22.98  thf('143', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 22.76/22.98      inference('clc', [status(thm)], ['141', '142'])).
% 22.76/22.98  thf(t91_relat_1, axiom,
% 22.76/22.98    (![A:$i,B:$i]:
% 22.76/22.98     ( ( v1_relat_1 @ B ) =>
% 22.76/22.98       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 22.76/22.98         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 22.76/22.98  thf('144', plain,
% 22.76/22.98      (![X17 : $i, X18 : $i]:
% 22.76/22.98         (~ (r1_tarski @ X17 @ (k1_relat_1 @ X18))
% 22.76/22.98          | ((k1_relat_1 @ (k7_relat_1 @ X18 @ X17)) = (X17))
% 22.76/22.98          | ~ (v1_relat_1 @ X18))),
% 22.76/22.98      inference('cnf', [status(esa)], [t91_relat_1])).
% 22.76/22.98  thf('145', plain,
% 22.76/22.98      (![X0 : $i]:
% 22.76/22.98         (~ (r1_tarski @ X0 @ sk_A)
% 22.76/22.98          | ~ (v1_relat_1 @ sk_D)
% 22.76/22.98          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 22.76/22.98      inference('sup-', [status(thm)], ['143', '144'])).
% 22.76/22.98  thf('146', plain, ((v1_relat_1 @ sk_D)),
% 22.76/22.98      inference('demod', [status(thm)], ['38', '39'])).
% 22.76/22.98  thf('147', plain,
% 22.76/22.98      (![X0 : $i]:
% 22.76/22.98         (~ (r1_tarski @ X0 @ sk_A)
% 22.76/22.98          | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) = (X0)))),
% 22.76/22.98      inference('demod', [status(thm)], ['145', '146'])).
% 22.76/22.98  thf('148', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 22.76/22.98      inference('sup-', [status(thm)], ['43', '147'])).
% 22.76/22.98  thf('149', plain,
% 22.76/22.98      (![X0 : $i]:
% 22.76/22.98         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 22.76/22.98          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))),
% 22.76/22.98      inference('demod', [status(thm)], ['34', '35', '40'])).
% 22.76/22.98  thf('150', plain,
% 22.76/22.98      (![X22 : $i, X23 : $i, X24 : $i]:
% 22.76/22.98         (((k1_relset_1 @ X23 @ X24 @ X22) = (k1_relat_1 @ X22))
% 22.76/22.98          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 22.76/22.98      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 22.76/22.98  thf('151', plain,
% 22.76/22.98      (![X0 : $i]:
% 22.76/22.98         ((k1_relset_1 @ X0 @ sk_B @ (k7_relat_1 @ sk_D @ X0))
% 22.76/22.98           = (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))),
% 22.76/22.98      inference('sup-', [status(thm)], ['149', '150'])).
% 22.76/22.98  thf('152', plain,
% 22.76/22.98      (![X30 : $i, X31 : $i, X32 : $i]:
% 22.76/22.98         (((X30) != (k1_relset_1 @ X30 @ X31 @ X32))
% 22.76/22.98          | (v1_funct_2 @ X32 @ X30 @ X31)
% 22.76/22.98          | ~ (zip_tseitin_1 @ X32 @ X31 @ X30))),
% 22.76/22.98      inference('cnf', [status(esa)], [zf_stmt_3])).
% 22.76/22.98  thf('153', plain,
% 22.76/22.98      (![X0 : $i]:
% 22.76/22.98         (((X0) != (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))
% 22.76/22.98          | ~ (zip_tseitin_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B @ X0)
% 22.76/22.98          | (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ X0 @ sk_B))),
% 22.76/22.98      inference('sup-', [status(thm)], ['151', '152'])).
% 22.76/22.98  thf('154', plain,
% 22.76/22.98      (![X28 : $i, X29 : $i]:
% 22.76/22.98         ((zip_tseitin_0 @ X28 @ X29) | ((X28) = (k1_xboole_0)))),
% 22.76/22.98      inference('cnf', [status(esa)], [zf_stmt_1])).
% 22.76/22.98  thf('155', plain,
% 22.76/22.98      (![X0 : $i]:
% 22.76/22.98         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 22.76/22.98          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))),
% 22.76/22.98      inference('demod', [status(thm)], ['34', '35', '40'])).
% 22.76/22.98  thf('156', plain,
% 22.76/22.98      (![X33 : $i, X34 : $i, X35 : $i]:
% 22.76/22.98         (~ (zip_tseitin_0 @ X33 @ X34)
% 22.76/22.98          | (zip_tseitin_1 @ X35 @ X33 @ X34)
% 22.76/22.98          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33))))),
% 22.76/22.98      inference('cnf', [status(esa)], [zf_stmt_5])).
% 22.76/22.98  thf('157', plain,
% 22.76/22.98      (![X0 : $i]:
% 22.76/22.98         ((zip_tseitin_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B @ X0)
% 22.76/22.98          | ~ (zip_tseitin_0 @ sk_B @ X0))),
% 22.76/22.98      inference('sup-', [status(thm)], ['155', '156'])).
% 22.76/22.98  thf('158', plain,
% 22.76/22.98      (![X0 : $i]:
% 22.76/22.98         (((sk_B) = (k1_xboole_0))
% 22.76/22.98          | (zip_tseitin_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B @ X0))),
% 22.76/22.98      inference('sup-', [status(thm)], ['154', '157'])).
% 22.76/22.98  thf('159', plain, (((sk_B) != (k1_xboole_0))),
% 22.76/22.98      inference('simpl_trail', [status(thm)], ['83', '137'])).
% 22.76/22.98  thf('160', plain,
% 22.76/22.98      (![X0 : $i]: (zip_tseitin_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B @ X0)),
% 22.76/22.98      inference('simplify_reflect-', [status(thm)], ['158', '159'])).
% 22.76/22.98  thf('161', plain,
% 22.76/22.98      (![X0 : $i]:
% 22.76/22.98         (((X0) != (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))
% 22.76/22.98          | (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ X0 @ sk_B))),
% 22.76/22.98      inference('demod', [status(thm)], ['153', '160'])).
% 22.76/22.98  thf('162', plain,
% 22.76/22.98      ((((sk_C) != (sk_C))
% 22.76/22.98        | (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B))),
% 22.76/22.98      inference('sup-', [status(thm)], ['148', '161'])).
% 22.76/22.98  thf('163', plain, ((v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)),
% 22.76/22.98      inference('simplify', [status(thm)], ['162'])).
% 22.76/22.98  thf('164', plain, ($false), inference('demod', [status(thm)], ['42', '163'])).
% 22.76/22.98  
% 22.76/22.98  % SZS output end Refutation
% 22.76/22.98  
% 22.76/22.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
