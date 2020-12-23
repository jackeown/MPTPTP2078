%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2HBd5SZ2jJ

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:07 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 183 expanded)
%              Number of leaves         :   27 (  62 expanded)
%              Depth                    :   16
%              Number of atoms          :  790 (2561 expanded)
%              Number of equality atoms :   62 ( 163 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t142_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ( r1_partfun1 @ C @ D )
           => ( ( ( B = k1_xboole_0 )
                & ( A != k1_xboole_0 ) )
              | ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ B )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
           => ( ( r1_partfun1 @ C @ D )
             => ( ( ( B = k1_xboole_0 )
                  & ( A != k1_xboole_0 ) )
                | ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t142_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( v1_partfun1 @ X23 @ X24 )
      | ~ ( v1_funct_2 @ X23 @ X24 @ X25 )
      | ~ ( v1_funct_1 @ X23 )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('4',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t148_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ( ( v1_partfun1 @ C @ A )
              & ( v1_partfun1 @ D @ A )
              & ( r1_partfun1 @ C @ D ) )
           => ( C = D ) ) ) ) )).

thf('9',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( X29 = X26 )
      | ~ ( r1_partfun1 @ X29 @ X26 )
      | ~ ( v1_partfun1 @ X26 @ X27 )
      | ~ ( v1_partfun1 @ X29 @ X27 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t148_partfun1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( X0 = sk_D )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( X0 = sk_D ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ( X0 = sk_D )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_partfun1 @ sk_C_1 @ sk_A )
    | ~ ( r1_partfun1 @ sk_C_1 @ sk_D )
    | ( sk_C_1 = sk_D )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    r1_partfun1 @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( v1_partfun1 @ sk_C_1 @ sk_A )
    | ( sk_C_1 = sk_D )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( v1_partfun1 @ X23 @ X24 )
      | ~ ( v1_funct_2 @ X23 @ X24 @ X25 )
      | ~ ( v1_funct_1 @ X23 )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('20',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B )
    | ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_C_1 = sk_D ) ),
    inference(clc,[status(thm)],['17','23'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('25',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('26',plain,
    ( ( sk_C_1 = sk_D )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['27'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('29',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('30',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( r2_relset_1 @ X19 @ X20 @ X21 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['27'])).

thf('34',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C_1 @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('36',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_zfmisc_1 @ X10 @ X11 )
        = k1_xboole_0 )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('37',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X11 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['27'])).

thf('39',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['37','40'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('42',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r2_hidden @ X14 @ X15 )
      | ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('43',plain,
    ( ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('44',plain,(
    ! [X12: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('45',plain,
    ( ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['43','44'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('46',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( r1_tarski @ X7 @ X5 )
      | ( X6
       != ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('47',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( r1_tarski @ sk_C_1 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('50',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r2_hidden @ X14 @ X15 )
      | ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X12: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('55',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('56',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','57'])).

thf('59',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','58'])).

thf('60',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X11 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('61',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['27'])).

thf('62',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r2_hidden @ X14 @ X15 )
      | ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('66',plain,
    ( ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X12: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('68',plain,
    ( ( r2_hidden @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('70',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('72',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['59','72'])).

thf('74',plain,(
    sk_A != k1_xboole_0 ),
    inference('sup-',[status(thm)],['32','73'])).

thf('75',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['27'])).

thf('76',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['74','75'])).

thf('77',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['28','76'])).

thf('78',plain,(
    sk_C_1 = sk_D ),
    inference('simplify_reflect-',[status(thm)],['26','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['30'])).

thf('81',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    $false ),
    inference(demod,[status(thm)],['0','78','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2HBd5SZ2jJ
% 0.14/0.37  % Computer   : n007.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 11:38:06 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.38  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.23/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.60  % Solved by: fo/fo7.sh
% 0.23/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.60  % done 363 iterations in 0.151s
% 0.23/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.60  % SZS output start Refutation
% 0.23/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.60  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.23/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.23/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.23/0.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.23/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.60  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.23/0.60  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.23/0.60  thf(sk_D_type, type, sk_D: $i).
% 0.23/0.60  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.23/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.23/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.60  thf(t142_funct_2, conjecture,
% 0.23/0.60    (![A:$i,B:$i,C:$i]:
% 0.23/0.60     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.23/0.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.23/0.60       ( ![D:$i]:
% 0.23/0.60         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.23/0.60             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.23/0.60           ( ( r1_partfun1 @ C @ D ) =>
% 0.23/0.60             ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.23/0.60               ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ))).
% 0.23/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.60    (~( ![A:$i,B:$i,C:$i]:
% 0.23/0.60        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.23/0.60            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.23/0.60          ( ![D:$i]:
% 0.23/0.60            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.23/0.60                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.23/0.60              ( ( r1_partfun1 @ C @ D ) =>
% 0.23/0.60                ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.23/0.60                  ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ) )),
% 0.23/0.60    inference('cnf.neg', [status(esa)], [t142_funct_2])).
% 0.23/0.60  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D)),
% 0.23/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.60  thf('1', plain,
% 0.23/0.60      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.23/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.60  thf('2', plain,
% 0.23/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.23/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.60  thf(cc5_funct_2, axiom,
% 0.23/0.60    (![A:$i,B:$i]:
% 0.23/0.60     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.23/0.60       ( ![C:$i]:
% 0.23/0.60         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.60           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.23/0.60             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.23/0.60  thf('3', plain,
% 0.23/0.60      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.23/0.60         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.23/0.60          | (v1_partfun1 @ X23 @ X24)
% 0.23/0.60          | ~ (v1_funct_2 @ X23 @ X24 @ X25)
% 0.23/0.60          | ~ (v1_funct_1 @ X23)
% 0.23/0.60          | (v1_xboole_0 @ X25))),
% 0.23/0.60      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.23/0.60  thf('4', plain,
% 0.23/0.60      (((v1_xboole_0 @ sk_B)
% 0.23/0.60        | ~ (v1_funct_1 @ sk_D)
% 0.23/0.60        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B)
% 0.23/0.60        | (v1_partfun1 @ sk_D @ sk_A))),
% 0.23/0.60      inference('sup-', [status(thm)], ['2', '3'])).
% 0.23/0.60  thf('5', plain, ((v1_funct_1 @ sk_D)),
% 0.23/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.60  thf('6', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.23/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.60  thf('7', plain, (((v1_xboole_0 @ sk_B) | (v1_partfun1 @ sk_D @ sk_A))),
% 0.23/0.60      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.23/0.60  thf('8', plain,
% 0.23/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.23/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.60  thf(t148_partfun1, axiom,
% 0.23/0.60    (![A:$i,B:$i,C:$i]:
% 0.23/0.60     ( ( ( v1_funct_1 @ C ) & 
% 0.23/0.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.23/0.60       ( ![D:$i]:
% 0.23/0.60         ( ( ( v1_funct_1 @ D ) & 
% 0.23/0.60             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.23/0.60           ( ( ( v1_partfun1 @ C @ A ) & ( v1_partfun1 @ D @ A ) & 
% 0.23/0.60               ( r1_partfun1 @ C @ D ) ) =>
% 0.23/0.60             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.23/0.60  thf('9', plain,
% 0.23/0.60      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.23/0.60         (~ (v1_funct_1 @ X26)
% 0.23/0.60          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.23/0.60          | ((X29) = (X26))
% 0.23/0.60          | ~ (r1_partfun1 @ X29 @ X26)
% 0.23/0.60          | ~ (v1_partfun1 @ X26 @ X27)
% 0.23/0.60          | ~ (v1_partfun1 @ X29 @ X27)
% 0.23/0.60          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.23/0.60          | ~ (v1_funct_1 @ X29))),
% 0.23/0.60      inference('cnf', [status(esa)], [t148_partfun1])).
% 0.23/0.60  thf('10', plain,
% 0.23/0.60      (![X0 : $i]:
% 0.23/0.60         (~ (v1_funct_1 @ X0)
% 0.23/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.23/0.60          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.23/0.60          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.23/0.60          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.23/0.60          | ((X0) = (sk_D))
% 0.23/0.60          | ~ (v1_funct_1 @ sk_D))),
% 0.23/0.60      inference('sup-', [status(thm)], ['8', '9'])).
% 0.23/0.60  thf('11', plain, ((v1_funct_1 @ sk_D)),
% 0.23/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.60  thf('12', plain,
% 0.23/0.60      (![X0 : $i]:
% 0.23/0.60         (~ (v1_funct_1 @ X0)
% 0.23/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.23/0.60          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.23/0.60          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.23/0.60          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.23/0.60          | ((X0) = (sk_D)))),
% 0.23/0.60      inference('demod', [status(thm)], ['10', '11'])).
% 0.23/0.60  thf('13', plain,
% 0.23/0.60      (![X0 : $i]:
% 0.23/0.60         ((v1_xboole_0 @ sk_B)
% 0.23/0.60          | ((X0) = (sk_D))
% 0.23/0.60          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.23/0.60          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.23/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.23/0.60          | ~ (v1_funct_1 @ X0))),
% 0.23/0.60      inference('sup-', [status(thm)], ['7', '12'])).
% 0.23/0.60  thf('14', plain,
% 0.23/0.60      ((~ (v1_funct_1 @ sk_C_1)
% 0.23/0.60        | ~ (v1_partfun1 @ sk_C_1 @ sk_A)
% 0.23/0.60        | ~ (r1_partfun1 @ sk_C_1 @ sk_D)
% 0.23/0.60        | ((sk_C_1) = (sk_D))
% 0.23/0.60        | (v1_xboole_0 @ sk_B))),
% 0.23/0.60      inference('sup-', [status(thm)], ['1', '13'])).
% 0.23/0.60  thf('15', plain, ((v1_funct_1 @ sk_C_1)),
% 0.23/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.60  thf('16', plain, ((r1_partfun1 @ sk_C_1 @ sk_D)),
% 0.23/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.60  thf('17', plain,
% 0.23/0.60      ((~ (v1_partfun1 @ sk_C_1 @ sk_A)
% 0.23/0.60        | ((sk_C_1) = (sk_D))
% 0.23/0.60        | (v1_xboole_0 @ sk_B))),
% 0.23/0.60      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.23/0.60  thf('18', plain,
% 0.23/0.60      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.23/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.60  thf('19', plain,
% 0.23/0.60      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.23/0.60         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.23/0.60          | (v1_partfun1 @ X23 @ X24)
% 0.23/0.60          | ~ (v1_funct_2 @ X23 @ X24 @ X25)
% 0.23/0.60          | ~ (v1_funct_1 @ X23)
% 0.23/0.60          | (v1_xboole_0 @ X25))),
% 0.23/0.60      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.23/0.60  thf('20', plain,
% 0.23/0.60      (((v1_xboole_0 @ sk_B)
% 0.23/0.60        | ~ (v1_funct_1 @ sk_C_1)
% 0.23/0.60        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.23/0.60        | (v1_partfun1 @ sk_C_1 @ sk_A))),
% 0.23/0.60      inference('sup-', [status(thm)], ['18', '19'])).
% 0.23/0.60  thf('21', plain, ((v1_funct_1 @ sk_C_1)),
% 0.23/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.60  thf('22', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.23/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.60  thf('23', plain, (((v1_xboole_0 @ sk_B) | (v1_partfun1 @ sk_C_1 @ sk_A))),
% 0.23/0.60      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.23/0.60  thf('24', plain, (((v1_xboole_0 @ sk_B) | ((sk_C_1) = (sk_D)))),
% 0.23/0.60      inference('clc', [status(thm)], ['17', '23'])).
% 0.23/0.60  thf(l13_xboole_0, axiom,
% 0.23/0.60    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.23/0.60  thf('25', plain,
% 0.23/0.60      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.23/0.60      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.23/0.60  thf('26', plain, ((((sk_C_1) = (sk_D)) | ((sk_B) = (k1_xboole_0)))),
% 0.23/0.60      inference('sup-', [status(thm)], ['24', '25'])).
% 0.23/0.60  thf('27', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.23/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.60  thf('28', plain,
% 0.23/0.60      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.23/0.60      inference('split', [status(esa)], ['27'])).
% 0.23/0.60  thf(t4_subset_1, axiom,
% 0.23/0.60    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.23/0.60  thf('29', plain,
% 0.23/0.60      (![X13 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 0.23/0.60      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.23/0.60  thf(reflexivity_r2_relset_1, axiom,
% 0.23/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.60     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.23/0.60         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.23/0.60       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 0.23/0.60  thf('30', plain,
% 0.23/0.60      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.23/0.60         ((r2_relset_1 @ X19 @ X20 @ X21 @ X21)
% 0.23/0.60          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.23/0.60          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.23/0.60      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 0.23/0.60  thf('31', plain,
% 0.23/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.60         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.23/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.23/0.60      inference('condensation', [status(thm)], ['30'])).
% 0.23/0.60  thf('32', plain,
% 0.23/0.60      (![X0 : $i, X1 : $i]: (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.23/0.60      inference('sup-', [status(thm)], ['29', '31'])).
% 0.23/0.60  thf('33', plain,
% 0.23/0.60      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.23/0.60      inference('split', [status(esa)], ['27'])).
% 0.23/0.60  thf('34', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D)),
% 0.23/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.60  thf('35', plain,
% 0.23/0.60      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B @ sk_C_1 @ sk_D))
% 0.23/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.23/0.60      inference('sup-', [status(thm)], ['33', '34'])).
% 0.23/0.60  thf(t113_zfmisc_1, axiom,
% 0.23/0.60    (![A:$i,B:$i]:
% 0.23/0.60     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.23/0.60       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.23/0.60  thf('36', plain,
% 0.23/0.60      (![X10 : $i, X11 : $i]:
% 0.23/0.60         (((k2_zfmisc_1 @ X10 @ X11) = (k1_xboole_0))
% 0.23/0.60          | ((X10) != (k1_xboole_0)))),
% 0.23/0.60      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.23/0.60  thf('37', plain,
% 0.23/0.60      (![X11 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X11) = (k1_xboole_0))),
% 0.23/0.60      inference('simplify', [status(thm)], ['36'])).
% 0.23/0.60  thf('38', plain,
% 0.23/0.60      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.23/0.60      inference('split', [status(esa)], ['27'])).
% 0.23/0.60  thf('39', plain,
% 0.23/0.60      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.23/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.60  thf('40', plain,
% 0.23/0.60      (((m1_subset_1 @ sk_C_1 @ 
% 0.23/0.60         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.23/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.23/0.60      inference('sup+', [status(thm)], ['38', '39'])).
% 0.23/0.60  thf('41', plain,
% 0.23/0.60      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.23/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.23/0.60      inference('sup+', [status(thm)], ['37', '40'])).
% 0.23/0.60  thf(t2_subset, axiom,
% 0.23/0.60    (![A:$i,B:$i]:
% 0.23/0.60     ( ( m1_subset_1 @ A @ B ) =>
% 0.23/0.60       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.23/0.60  thf('42', plain,
% 0.23/0.60      (![X14 : $i, X15 : $i]:
% 0.23/0.60         ((r2_hidden @ X14 @ X15)
% 0.23/0.60          | (v1_xboole_0 @ X15)
% 0.23/0.60          | ~ (m1_subset_1 @ X14 @ X15))),
% 0.23/0.60      inference('cnf', [status(esa)], [t2_subset])).
% 0.23/0.60  thf('43', plain,
% 0.23/0.60      ((((v1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.23/0.60         | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ k1_xboole_0))))
% 0.23/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.23/0.60      inference('sup-', [status(thm)], ['41', '42'])).
% 0.23/0.60  thf(fc1_subset_1, axiom,
% 0.23/0.60    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.23/0.60  thf('44', plain, (![X12 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.23/0.60      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.23/0.60  thf('45', plain,
% 0.23/0.60      (((r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.23/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.23/0.60      inference('clc', [status(thm)], ['43', '44'])).
% 0.23/0.60  thf(d1_zfmisc_1, axiom,
% 0.23/0.60    (![A:$i,B:$i]:
% 0.23/0.60     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.23/0.60       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.23/0.60  thf('46', plain,
% 0.23/0.60      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.23/0.60         (~ (r2_hidden @ X7 @ X6)
% 0.23/0.60          | (r1_tarski @ X7 @ X5)
% 0.23/0.60          | ((X6) != (k1_zfmisc_1 @ X5)))),
% 0.23/0.60      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.23/0.60  thf('47', plain,
% 0.23/0.60      (![X5 : $i, X7 : $i]:
% 0.23/0.60         ((r1_tarski @ X7 @ X5) | ~ (r2_hidden @ X7 @ (k1_zfmisc_1 @ X5)))),
% 0.23/0.60      inference('simplify', [status(thm)], ['46'])).
% 0.23/0.60  thf('48', plain,
% 0.23/0.60      (((r1_tarski @ sk_C_1 @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.23/0.60      inference('sup-', [status(thm)], ['45', '47'])).
% 0.23/0.60  thf('49', plain,
% 0.23/0.60      (![X13 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 0.23/0.60      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.23/0.60  thf('50', plain,
% 0.23/0.60      (![X14 : $i, X15 : $i]:
% 0.23/0.60         ((r2_hidden @ X14 @ X15)
% 0.23/0.60          | (v1_xboole_0 @ X15)
% 0.23/0.60          | ~ (m1_subset_1 @ X14 @ X15))),
% 0.23/0.60      inference('cnf', [status(esa)], [t2_subset])).
% 0.23/0.60  thf('51', plain,
% 0.23/0.60      (![X0 : $i]:
% 0.23/0.60         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.23/0.60          | (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0)))),
% 0.23/0.60      inference('sup-', [status(thm)], ['49', '50'])).
% 0.23/0.60  thf('52', plain, (![X12 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.23/0.60      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.23/0.60  thf('53', plain,
% 0.23/0.60      (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.23/0.60      inference('clc', [status(thm)], ['51', '52'])).
% 0.23/0.60  thf('54', plain,
% 0.23/0.60      (![X5 : $i, X7 : $i]:
% 0.23/0.60         ((r1_tarski @ X7 @ X5) | ~ (r2_hidden @ X7 @ (k1_zfmisc_1 @ X5)))),
% 0.23/0.60      inference('simplify', [status(thm)], ['46'])).
% 0.23/0.60  thf('55', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.23/0.60      inference('sup-', [status(thm)], ['53', '54'])).
% 0.23/0.60  thf(d10_xboole_0, axiom,
% 0.23/0.60    (![A:$i,B:$i]:
% 0.23/0.60     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.23/0.60  thf('56', plain,
% 0.23/0.60      (![X1 : $i, X3 : $i]:
% 0.23/0.60         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.23/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.23/0.60  thf('57', plain,
% 0.23/0.60      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.23/0.60      inference('sup-', [status(thm)], ['55', '56'])).
% 0.23/0.60  thf('58', plain,
% 0.23/0.60      ((((sk_C_1) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.23/0.60      inference('sup-', [status(thm)], ['48', '57'])).
% 0.23/0.60  thf('59', plain,
% 0.23/0.60      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ sk_D))
% 0.23/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.23/0.60      inference('demod', [status(thm)], ['35', '58'])).
% 0.23/0.60  thf('60', plain,
% 0.23/0.60      (![X11 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X11) = (k1_xboole_0))),
% 0.23/0.60      inference('simplify', [status(thm)], ['36'])).
% 0.23/0.60  thf('61', plain,
% 0.23/0.60      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.23/0.60      inference('split', [status(esa)], ['27'])).
% 0.23/0.60  thf('62', plain,
% 0.23/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.23/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.60  thf('63', plain,
% 0.23/0.60      (((m1_subset_1 @ sk_D @ 
% 0.23/0.60         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.23/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.23/0.60      inference('sup+', [status(thm)], ['61', '62'])).
% 0.23/0.60  thf('64', plain,
% 0.23/0.60      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.23/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.23/0.60      inference('sup+', [status(thm)], ['60', '63'])).
% 0.23/0.60  thf('65', plain,
% 0.23/0.60      (![X14 : $i, X15 : $i]:
% 0.23/0.60         ((r2_hidden @ X14 @ X15)
% 0.23/0.60          | (v1_xboole_0 @ X15)
% 0.23/0.60          | ~ (m1_subset_1 @ X14 @ X15))),
% 0.23/0.60      inference('cnf', [status(esa)], [t2_subset])).
% 0.23/0.60  thf('66', plain,
% 0.23/0.60      ((((v1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.23/0.60         | (r2_hidden @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0))))
% 0.23/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.23/0.60      inference('sup-', [status(thm)], ['64', '65'])).
% 0.23/0.60  thf('67', plain, (![X12 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.23/0.60      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.23/0.60  thf('68', plain,
% 0.23/0.60      (((r2_hidden @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.23/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.23/0.60      inference('clc', [status(thm)], ['66', '67'])).
% 0.23/0.60  thf('69', plain,
% 0.23/0.60      (![X5 : $i, X7 : $i]:
% 0.23/0.60         ((r1_tarski @ X7 @ X5) | ~ (r2_hidden @ X7 @ (k1_zfmisc_1 @ X5)))),
% 0.23/0.60      inference('simplify', [status(thm)], ['46'])).
% 0.23/0.60  thf('70', plain,
% 0.23/0.60      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.23/0.60      inference('sup-', [status(thm)], ['68', '69'])).
% 0.23/0.60  thf('71', plain,
% 0.23/0.60      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.23/0.60      inference('sup-', [status(thm)], ['55', '56'])).
% 0.23/0.60  thf('72', plain,
% 0.23/0.60      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.23/0.60      inference('sup-', [status(thm)], ['70', '71'])).
% 0.23/0.60  thf('73', plain,
% 0.23/0.60      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ k1_xboole_0))
% 0.23/0.60         <= ((((sk_A) = (k1_xboole_0))))),
% 0.23/0.60      inference('demod', [status(thm)], ['59', '72'])).
% 0.23/0.60  thf('74', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.23/0.60      inference('sup-', [status(thm)], ['32', '73'])).
% 0.23/0.60  thf('75', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.23/0.60      inference('split', [status(esa)], ['27'])).
% 0.23/0.60  thf('76', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.23/0.60      inference('sat_resolution*', [status(thm)], ['74', '75'])).
% 0.23/0.60  thf('77', plain, (((sk_B) != (k1_xboole_0))),
% 0.23/0.60      inference('simpl_trail', [status(thm)], ['28', '76'])).
% 0.23/0.60  thf('78', plain, (((sk_C_1) = (sk_D))),
% 0.23/0.60      inference('simplify_reflect-', [status(thm)], ['26', '77'])).
% 0.23/0.60  thf('79', plain,
% 0.23/0.60      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.23/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.60  thf('80', plain,
% 0.23/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.60         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.23/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.23/0.60      inference('condensation', [status(thm)], ['30'])).
% 0.23/0.60  thf('81', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_C_1 @ sk_C_1)),
% 0.23/0.60      inference('sup-', [status(thm)], ['79', '80'])).
% 0.23/0.60  thf('82', plain, ($false),
% 0.23/0.60      inference('demod', [status(thm)], ['0', '78', '81'])).
% 0.23/0.60  
% 0.23/0.60  % SZS output end Refutation
% 0.23/0.60  
% 0.23/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
