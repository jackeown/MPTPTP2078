%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SeuG0aN0BK

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:08 EST 2020

% Result     : Theorem 4.60s
% Output     : Refutation 4.60s
% Verified   : 
% Statistics : Number of formulae       :  191 (1594 expanded)
%              Number of leaves         :   44 ( 488 expanded)
%              Depth                    :   16
%              Number of atoms          : 1515 (37901 expanded)
%              Number of equality atoms :   83 ( 588 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('0',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X5 )
      | ( X4 = X5 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('4',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('11',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('12',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['4','14'])).

thf('16',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('17',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('18',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( r2_relset_1 @ X29 @ X30 @ X28 @ X31 )
      | ( X28 != X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('19',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( r2_relset_1 @ X29 @ X30 @ X31 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_relset_1 @ X3 @ X2 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','21'])).

thf(t87_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ! [C: $i] :
          ( ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ A )
            & ( v3_funct_2 @ C @ A @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ ( k6_partfun1 @ A ) )
           => ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( v3_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ! [C: $i] :
            ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ A )
              & ( v3_funct_2 @ C @ A @ A )
              & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
           => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ ( k6_partfun1 @ A ) )
             => ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t87_funct_2])).

thf('23',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k2_funct_2 @ A @ B )
        = ( k2_funct_1 @ B ) ) ) )).

thf('25',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k2_funct_2 @ X40 @ X39 )
        = ( k2_funct_1 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X40 ) ) )
      | ~ ( v3_funct_2 @ X39 @ X40 @ X40 )
      | ~ ( v1_funct_2 @ X39 @ X40 @ X40 )
      | ~ ( v1_funct_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('26',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_B )
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('31',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','30'])).

thf('32',plain,
    ( ~ ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_xboole_0 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('34',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X24 ) ) )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('35',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C_1 ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( ( ( k2_relset_1 @ A @ B @ C )
                = B )
              & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
              & ( v2_funct_1 @ C ) )
           => ( ( A = k1_xboole_0 )
              | ( B = k1_xboole_0 )
              | ( D
                = ( k2_funct_1 @ C ) ) ) ) ) ) )).

thf('38',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_2 @ X45 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ( X45
        = ( k2_funct_1 @ X48 ) )
      | ~ ( r2_relset_1 @ X47 @ X47 @ ( k1_partfun1 @ X47 @ X46 @ X46 @ X47 @ X48 @ X45 ) @ ( k6_partfun1 @ X47 ) )
      | ( X46 = k1_xboole_0 )
      | ( X47 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X48 )
      | ( ( k2_relset_1 @ X47 @ X46 @ X48 )
       != X46 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X46 ) ) )
      | ~ ( v1_funct_2 @ X48 @ X47 @ X46 )
      | ~ ( v1_funct_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t36_funct_2])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( v2_funct_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C_1 ) @ ( k6_partfun1 @ sk_A ) )
      | ( sk_C_1
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( v2_funct_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C_1 ) @ ( k6_partfun1 @ sk_A ) )
      | ( sk_C_1
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( sk_C_1
        = ( k2_funct_1 @ X0 ) )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C_1 ) @ ( k6_partfun1 @ sk_A ) )
      | ( sk_A = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_B )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C_1
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','43'])).

thf('45',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('49',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k2_relset_1 @ X26 @ X27 @ X25 )
        = ( k2_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('50',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v3_funct_2 @ C @ A @ B ) )
       => ( ( v1_funct_1 @ C )
          & ( v2_funct_1 @ C )
          & ( v2_funct_2 @ C @ B ) ) ) ) )).

thf('52',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_1 @ X32 )
      | ~ ( v3_funct_2 @ X32 @ X33 @ X34 )
      | ( v2_funct_2 @ X32 @ X34 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('53',plain,
    ( ( v2_funct_2 @ sk_B @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v2_funct_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['53','54','55'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('57',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( v2_funct_2 @ X36 @ X35 )
      | ( ( k2_relat_1 @ X36 )
        = X35 )
      | ~ ( v5_relat_1 @ X36 @ X35 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('58',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v5_relat_1 @ sk_B @ sk_A )
    | ( ( k2_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('60',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('61',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('62',plain,(
    ! [X17: $i,X18: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('63',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('65',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v5_relat_1 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('66',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['58','63','66'])).

thf('68',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['50','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_1 @ X32 )
      | ~ ( v3_funct_2 @ X32 @ X33 @ X34 )
      | ( v2_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('71',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,
    ( ( sk_A != sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C_1
      = ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['44','45','46','47','68','74'])).

thf('76',plain,
    ( ( sk_C_1
      = ( k2_funct_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','30'])).

thf('78',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_C_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( r2_relset_1 @ X29 @ X30 @ X31 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('81',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['78','81'])).

thf('83',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('84',plain,(
    v1_xboole_0 @ sk_C_1 ),
    inference(demod,[status(thm)],['35','82','83'])).

thf('85',plain,(
    ~ ( v1_xboole_0 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','20'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('88',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_zfmisc_1 @ X7 @ X8 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('89',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X8 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['87','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('92',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( X28 = X31 )
      | ~ ( r2_relset_1 @ X29 @ X30 @ X28 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ X0 )
      | ( sk_B = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( sk_B
      = ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['91','94'])).

thf('96',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_A )
    | ( sk_B
      = ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['90','95'])).

thf('97',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ( sk_B
      = ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['86','96'])).

thf('98',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X24 ) ) )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('100',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( sk_B
      = ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(clc,[status(thm)],['97','100'])).

thf('102',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['78','81'])).

thf('103',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('104',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['78','81'])).

thf('105',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['78','81'])).

thf('106',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X8 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['88'])).

thf('107',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['101','102','103','104','105','106'])).

thf('108',plain,(
    ~ ( v1_xboole_0 @ ( k2_funct_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['85','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_relset_1 @ X3 @ X2 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','21'])).

thf('110',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) )
        & ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A )
        & ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A )
        & ( m1_subset_1 @ ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ) )).

thf('111',plain,(
    ! [X37: $i,X38: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X37 @ X38 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) )
      | ~ ( v3_funct_2 @ X38 @ X37 @ X37 )
      | ~ ( v1_funct_2 @ X38 @ X37 @ X37 )
      | ~ ( v1_funct_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('112',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['112','113','114','115'])).

thf('117',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('118',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('120',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( X28 = X31 )
      | ~ ( r2_relset_1 @ X29 @ X30 @ X28 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('121',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_relset_1 @ X1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X2 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = ( k2_funct_1 @ sk_B ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['118','121'])).

thf('123',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ~ ( v1_xboole_0 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['109','122'])).

thf('124',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('126',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X8 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['88'])).

thf('127',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X24 ) ) )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('128',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('130',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['125','130'])).

thf('132',plain,
    ( ( v1_xboole_0 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['124','131'])).

thf('133',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(clc,[status(thm)],['123','132'])).

thf('134',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['78','81'])).

thf('135',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['78','81'])).

thf('136',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X8 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['88'])).

thf('137',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['78','81'])).

thf('138',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['78','81'])).

thf('139',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X8 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['88'])).

thf('140',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('141',plain,
    ( k1_xboole_0
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['133','134','135','136','137','138','139','140'])).

thf('142',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['101','102','103','104','105','106'])).

thf('143',plain,
    ( k1_xboole_0
    = ( k2_funct_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('145',plain,(
    $false ),
    inference(demod,[status(thm)],['108','143','144'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SeuG0aN0BK
% 0.13/0.33  % Computer   : n025.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:28:06 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 4.60/4.84  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.60/4.84  % Solved by: fo/fo7.sh
% 4.60/4.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.60/4.84  % done 9336 iterations in 4.388s
% 4.60/4.84  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.60/4.84  % SZS output start Refutation
% 4.60/4.84  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 4.60/4.84  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.60/4.84  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 4.60/4.84  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 4.60/4.84  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.60/4.84  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 4.60/4.84  thf(sk_B_type, type, sk_B: $i).
% 4.60/4.84  thf(sk_A_type, type, sk_A: $i).
% 4.60/4.84  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.60/4.84  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 4.60/4.84  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.60/4.84  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 4.60/4.84  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.60/4.84  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.60/4.84  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 4.60/4.84  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 4.60/4.84  thf(sk_C_1_type, type, sk_C_1: $i).
% 4.60/4.84  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.60/4.84  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 4.60/4.84  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.60/4.84  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 4.60/4.84  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.60/4.84  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 4.60/4.84  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 4.60/4.84  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.60/4.84  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 4.60/4.84  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 4.60/4.84  thf('0', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.60/4.84      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.60/4.84  thf(t8_boole, axiom,
% 4.60/4.84    (![A:$i,B:$i]:
% 4.60/4.84     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 4.60/4.84  thf('1', plain,
% 4.60/4.84      (![X4 : $i, X5 : $i]:
% 4.60/4.84         (~ (v1_xboole_0 @ X4) | ~ (v1_xboole_0 @ X5) | ((X4) = (X5)))),
% 4.60/4.84      inference('cnf', [status(esa)], [t8_boole])).
% 4.60/4.84  thf('2', plain,
% 4.60/4.84      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 4.60/4.84      inference('sup-', [status(thm)], ['0', '1'])).
% 4.60/4.84  thf('3', plain,
% 4.60/4.84      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 4.60/4.84      inference('sup-', [status(thm)], ['0', '1'])).
% 4.60/4.84  thf('4', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.60/4.84      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.60/4.84  thf(d3_tarski, axiom,
% 4.60/4.84    (![A:$i,B:$i]:
% 4.60/4.84     ( ( r1_tarski @ A @ B ) <=>
% 4.60/4.84       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 4.60/4.84  thf('5', plain,
% 4.60/4.84      (![X1 : $i, X3 : $i]:
% 4.60/4.84         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 4.60/4.84      inference('cnf', [status(esa)], [d3_tarski])).
% 4.60/4.84  thf('6', plain,
% 4.60/4.84      (![X1 : $i, X3 : $i]:
% 4.60/4.84         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 4.60/4.84      inference('cnf', [status(esa)], [d3_tarski])).
% 4.60/4.84  thf('7', plain,
% 4.60/4.84      (![X1 : $i, X3 : $i]:
% 4.60/4.84         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 4.60/4.84      inference('cnf', [status(esa)], [d3_tarski])).
% 4.60/4.84  thf('8', plain,
% 4.60/4.84      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 4.60/4.84      inference('sup-', [status(thm)], ['6', '7'])).
% 4.60/4.84  thf('9', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 4.60/4.84      inference('simplify', [status(thm)], ['8'])).
% 4.60/4.84  thf(t3_subset, axiom,
% 4.60/4.84    (![A:$i,B:$i]:
% 4.60/4.84     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 4.60/4.84  thf('10', plain,
% 4.60/4.84      (![X9 : $i, X11 : $i]:
% 4.60/4.84         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 4.60/4.84      inference('cnf', [status(esa)], [t3_subset])).
% 4.60/4.84  thf('11', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 4.60/4.84      inference('sup-', [status(thm)], ['9', '10'])).
% 4.60/4.84  thf(t5_subset, axiom,
% 4.60/4.84    (![A:$i,B:$i,C:$i]:
% 4.60/4.84     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 4.60/4.84          ( v1_xboole_0 @ C ) ) ))).
% 4.60/4.84  thf('12', plain,
% 4.60/4.84      (![X12 : $i, X13 : $i, X14 : $i]:
% 4.60/4.84         (~ (r2_hidden @ X12 @ X13)
% 4.60/4.84          | ~ (v1_xboole_0 @ X14)
% 4.60/4.84          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 4.60/4.84      inference('cnf', [status(esa)], [t5_subset])).
% 4.60/4.84  thf('13', plain,
% 4.60/4.84      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 4.60/4.84      inference('sup-', [status(thm)], ['11', '12'])).
% 4.60/4.84  thf('14', plain,
% 4.60/4.84      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 4.60/4.84      inference('sup-', [status(thm)], ['5', '13'])).
% 4.60/4.84  thf('15', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 4.60/4.84      inference('sup-', [status(thm)], ['4', '14'])).
% 4.60/4.84  thf('16', plain,
% 4.60/4.84      (![X9 : $i, X11 : $i]:
% 4.60/4.84         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 4.60/4.84      inference('cnf', [status(esa)], [t3_subset])).
% 4.60/4.84  thf('17', plain,
% 4.60/4.84      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 4.60/4.84      inference('sup-', [status(thm)], ['15', '16'])).
% 4.60/4.84  thf(redefinition_r2_relset_1, axiom,
% 4.60/4.84    (![A:$i,B:$i,C:$i,D:$i]:
% 4.60/4.84     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 4.60/4.84         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.60/4.84       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 4.60/4.84  thf('18', plain,
% 4.60/4.84      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 4.60/4.84         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 4.60/4.84          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 4.60/4.84          | (r2_relset_1 @ X29 @ X30 @ X28 @ X31)
% 4.60/4.84          | ((X28) != (X31)))),
% 4.60/4.84      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 4.60/4.84  thf('19', plain,
% 4.60/4.84      (![X29 : $i, X30 : $i, X31 : $i]:
% 4.60/4.84         ((r2_relset_1 @ X29 @ X30 @ X31 @ X31)
% 4.60/4.84          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 4.60/4.84      inference('simplify', [status(thm)], ['18'])).
% 4.60/4.84  thf('20', plain,
% 4.60/4.84      (![X0 : $i, X1 : $i]: (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 4.60/4.84      inference('sup-', [status(thm)], ['17', '19'])).
% 4.60/4.84  thf('21', plain,
% 4.60/4.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.60/4.84         ((r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0))),
% 4.60/4.84      inference('sup+', [status(thm)], ['3', '20'])).
% 4.60/4.84  thf('22', plain,
% 4.60/4.84      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.60/4.84         ((r2_relset_1 @ X3 @ X2 @ X1 @ X0)
% 4.60/4.84          | ~ (v1_xboole_0 @ X0)
% 4.60/4.84          | ~ (v1_xboole_0 @ X1))),
% 4.60/4.84      inference('sup+', [status(thm)], ['2', '21'])).
% 4.60/4.84  thf(t87_funct_2, conjecture,
% 4.60/4.84    (![A:$i,B:$i]:
% 4.60/4.84     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 4.60/4.84         ( v3_funct_2 @ B @ A @ A ) & 
% 4.60/4.84         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 4.60/4.84       ( ![C:$i]:
% 4.60/4.84         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 4.60/4.84             ( v3_funct_2 @ C @ A @ A ) & 
% 4.60/4.84             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 4.60/4.84           ( ( r2_relset_1 @
% 4.60/4.84               A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 4.60/4.84               ( k6_partfun1 @ A ) ) =>
% 4.60/4.84             ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ))).
% 4.60/4.84  thf(zf_stmt_0, negated_conjecture,
% 4.60/4.84    (~( ![A:$i,B:$i]:
% 4.60/4.84        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 4.60/4.84            ( v3_funct_2 @ B @ A @ A ) & 
% 4.60/4.84            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 4.60/4.84          ( ![C:$i]:
% 4.60/4.84            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 4.60/4.84                ( v3_funct_2 @ C @ A @ A ) & 
% 4.60/4.84                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 4.60/4.84              ( ( r2_relset_1 @
% 4.60/4.84                  A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 4.60/4.84                  ( k6_partfun1 @ A ) ) =>
% 4.60/4.84                ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ) )),
% 4.60/4.84    inference('cnf.neg', [status(esa)], [t87_funct_2])).
% 4.60/4.84  thf('23', plain,
% 4.60/4.84      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 4.60/4.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.60/4.84  thf('24', plain,
% 4.60/4.84      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.60/4.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.60/4.84  thf(redefinition_k2_funct_2, axiom,
% 4.60/4.84    (![A:$i,B:$i]:
% 4.60/4.84     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 4.60/4.84         ( v3_funct_2 @ B @ A @ A ) & 
% 4.60/4.84         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 4.60/4.84       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 4.60/4.84  thf('25', plain,
% 4.60/4.84      (![X39 : $i, X40 : $i]:
% 4.60/4.84         (((k2_funct_2 @ X40 @ X39) = (k2_funct_1 @ X39))
% 4.60/4.84          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X40)))
% 4.60/4.84          | ~ (v3_funct_2 @ X39 @ X40 @ X40)
% 4.60/4.84          | ~ (v1_funct_2 @ X39 @ X40 @ X40)
% 4.60/4.84          | ~ (v1_funct_1 @ X39))),
% 4.60/4.84      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 4.60/4.84  thf('26', plain,
% 4.60/4.84      ((~ (v1_funct_1 @ sk_B)
% 4.60/4.84        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 4.60/4.84        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 4.60/4.84        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 4.60/4.84      inference('sup-', [status(thm)], ['24', '25'])).
% 4.60/4.84  thf('27', plain, ((v1_funct_1 @ sk_B)),
% 4.60/4.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.60/4.84  thf('28', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 4.60/4.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.60/4.84  thf('29', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 4.60/4.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.60/4.84  thf('30', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 4.60/4.84      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 4.60/4.84  thf('31', plain,
% 4.60/4.84      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ (k2_funct_1 @ sk_B))),
% 4.60/4.84      inference('demod', [status(thm)], ['23', '30'])).
% 4.60/4.84  thf('32', plain,
% 4.60/4.84      ((~ (v1_xboole_0 @ sk_C_1) | ~ (v1_xboole_0 @ (k2_funct_1 @ sk_B)))),
% 4.60/4.84      inference('sup-', [status(thm)], ['22', '31'])).
% 4.60/4.84  thf('33', plain,
% 4.60/4.84      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.60/4.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.60/4.84  thf(cc3_relset_1, axiom,
% 4.60/4.84    (![A:$i,B:$i]:
% 4.60/4.84     ( ( v1_xboole_0 @ A ) =>
% 4.60/4.84       ( ![C:$i]:
% 4.60/4.84         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.60/4.84           ( v1_xboole_0 @ C ) ) ) ))).
% 4.60/4.84  thf('34', plain,
% 4.60/4.84      (![X22 : $i, X23 : $i, X24 : $i]:
% 4.60/4.84         (~ (v1_xboole_0 @ X22)
% 4.60/4.84          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X24)))
% 4.60/4.84          | (v1_xboole_0 @ X23))),
% 4.60/4.84      inference('cnf', [status(esa)], [cc3_relset_1])).
% 4.60/4.84  thf('35', plain, (((v1_xboole_0 @ sk_C_1) | ~ (v1_xboole_0 @ sk_A))),
% 4.60/4.84      inference('sup-', [status(thm)], ['33', '34'])).
% 4.60/4.84  thf('36', plain,
% 4.60/4.84      ((r2_relset_1 @ sk_A @ sk_A @ 
% 4.60/4.84        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C_1) @ 
% 4.60/4.84        (k6_partfun1 @ sk_A))),
% 4.60/4.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.60/4.84  thf('37', plain,
% 4.60/4.84      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.60/4.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.60/4.84  thf(t36_funct_2, axiom,
% 4.60/4.84    (![A:$i,B:$i,C:$i]:
% 4.60/4.84     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.60/4.84         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.60/4.84       ( ![D:$i]:
% 4.60/4.84         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 4.60/4.84             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 4.60/4.84           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 4.60/4.84               ( r2_relset_1 @
% 4.60/4.84                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 4.60/4.84                 ( k6_partfun1 @ A ) ) & 
% 4.60/4.84               ( v2_funct_1 @ C ) ) =>
% 4.60/4.84             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 4.60/4.84               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 4.60/4.84  thf('38', plain,
% 4.60/4.84      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 4.60/4.84         (~ (v1_funct_1 @ X45)
% 4.60/4.84          | ~ (v1_funct_2 @ X45 @ X46 @ X47)
% 4.60/4.84          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 4.60/4.84          | ((X45) = (k2_funct_1 @ X48))
% 4.60/4.84          | ~ (r2_relset_1 @ X47 @ X47 @ 
% 4.60/4.84               (k1_partfun1 @ X47 @ X46 @ X46 @ X47 @ X48 @ X45) @ 
% 4.60/4.84               (k6_partfun1 @ X47))
% 4.60/4.84          | ((X46) = (k1_xboole_0))
% 4.60/4.84          | ((X47) = (k1_xboole_0))
% 4.60/4.84          | ~ (v2_funct_1 @ X48)
% 4.60/4.84          | ((k2_relset_1 @ X47 @ X46 @ X48) != (X46))
% 4.60/4.84          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X46)))
% 4.60/4.84          | ~ (v1_funct_2 @ X48 @ X47 @ X46)
% 4.60/4.84          | ~ (v1_funct_1 @ X48))),
% 4.60/4.84      inference('cnf', [status(esa)], [t36_funct_2])).
% 4.60/4.84  thf('39', plain,
% 4.60/4.84      (![X0 : $i]:
% 4.60/4.84         (~ (v1_funct_1 @ X0)
% 4.60/4.84          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 4.60/4.84          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 4.60/4.84          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 4.60/4.84          | ~ (v2_funct_1 @ X0)
% 4.60/4.84          | ((sk_A) = (k1_xboole_0))
% 4.60/4.84          | ((sk_A) = (k1_xboole_0))
% 4.60/4.84          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 4.60/4.84               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C_1) @ 
% 4.60/4.84               (k6_partfun1 @ sk_A))
% 4.60/4.84          | ((sk_C_1) = (k2_funct_1 @ X0))
% 4.60/4.84          | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_A)
% 4.60/4.84          | ~ (v1_funct_1 @ sk_C_1))),
% 4.60/4.84      inference('sup-', [status(thm)], ['37', '38'])).
% 4.60/4.84  thf('40', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_A)),
% 4.60/4.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.60/4.84  thf('41', plain, ((v1_funct_1 @ sk_C_1)),
% 4.60/4.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.60/4.84  thf('42', plain,
% 4.60/4.84      (![X0 : $i]:
% 4.60/4.84         (~ (v1_funct_1 @ X0)
% 4.60/4.84          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 4.60/4.84          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 4.60/4.84          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 4.60/4.84          | ~ (v2_funct_1 @ X0)
% 4.60/4.84          | ((sk_A) = (k1_xboole_0))
% 4.60/4.84          | ((sk_A) = (k1_xboole_0))
% 4.60/4.84          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 4.60/4.84               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C_1) @ 
% 4.60/4.84               (k6_partfun1 @ sk_A))
% 4.60/4.84          | ((sk_C_1) = (k2_funct_1 @ X0)))),
% 4.60/4.84      inference('demod', [status(thm)], ['39', '40', '41'])).
% 4.60/4.84  thf('43', plain,
% 4.60/4.84      (![X0 : $i]:
% 4.60/4.84         (((sk_C_1) = (k2_funct_1 @ X0))
% 4.60/4.84          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 4.60/4.84               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C_1) @ 
% 4.60/4.84               (k6_partfun1 @ sk_A))
% 4.60/4.84          | ((sk_A) = (k1_xboole_0))
% 4.60/4.84          | ~ (v2_funct_1 @ X0)
% 4.60/4.84          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 4.60/4.84          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 4.60/4.84          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 4.60/4.84          | ~ (v1_funct_1 @ X0))),
% 4.60/4.84      inference('simplify', [status(thm)], ['42'])).
% 4.60/4.84  thf('44', plain,
% 4.60/4.84      ((~ (v1_funct_1 @ sk_B)
% 4.60/4.84        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 4.60/4.84        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 4.60/4.84        | ((k2_relset_1 @ sk_A @ sk_A @ sk_B) != (sk_A))
% 4.60/4.84        | ~ (v2_funct_1 @ sk_B)
% 4.60/4.84        | ((sk_A) = (k1_xboole_0))
% 4.60/4.84        | ((sk_C_1) = (k2_funct_1 @ sk_B)))),
% 4.60/4.84      inference('sup-', [status(thm)], ['36', '43'])).
% 4.60/4.84  thf('45', plain, ((v1_funct_1 @ sk_B)),
% 4.60/4.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.60/4.84  thf('46', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 4.60/4.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.60/4.84  thf('47', plain,
% 4.60/4.84      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.60/4.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.60/4.84  thf('48', plain,
% 4.60/4.84      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.60/4.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.60/4.84  thf(redefinition_k2_relset_1, axiom,
% 4.60/4.84    (![A:$i,B:$i,C:$i]:
% 4.60/4.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.60/4.84       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 4.60/4.84  thf('49', plain,
% 4.60/4.84      (![X25 : $i, X26 : $i, X27 : $i]:
% 4.60/4.84         (((k2_relset_1 @ X26 @ X27 @ X25) = (k2_relat_1 @ X25))
% 4.60/4.84          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 4.60/4.84      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 4.60/4.84  thf('50', plain,
% 4.60/4.84      (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (k2_relat_1 @ sk_B))),
% 4.60/4.84      inference('sup-', [status(thm)], ['48', '49'])).
% 4.60/4.84  thf('51', plain,
% 4.60/4.84      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.60/4.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.60/4.84  thf(cc2_funct_2, axiom,
% 4.60/4.84    (![A:$i,B:$i,C:$i]:
% 4.60/4.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.60/4.84       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 4.60/4.84         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 4.60/4.84  thf('52', plain,
% 4.60/4.84      (![X32 : $i, X33 : $i, X34 : $i]:
% 4.60/4.84         (~ (v1_funct_1 @ X32)
% 4.60/4.84          | ~ (v3_funct_2 @ X32 @ X33 @ X34)
% 4.60/4.84          | (v2_funct_2 @ X32 @ X34)
% 4.60/4.84          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 4.60/4.84      inference('cnf', [status(esa)], [cc2_funct_2])).
% 4.60/4.84  thf('53', plain,
% 4.60/4.84      (((v2_funct_2 @ sk_B @ sk_A)
% 4.60/4.84        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 4.60/4.84        | ~ (v1_funct_1 @ sk_B))),
% 4.60/4.84      inference('sup-', [status(thm)], ['51', '52'])).
% 4.60/4.84  thf('54', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 4.60/4.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.60/4.84  thf('55', plain, ((v1_funct_1 @ sk_B)),
% 4.60/4.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.60/4.84  thf('56', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 4.60/4.84      inference('demod', [status(thm)], ['53', '54', '55'])).
% 4.60/4.84  thf(d3_funct_2, axiom,
% 4.60/4.84    (![A:$i,B:$i]:
% 4.60/4.84     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 4.60/4.84       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 4.60/4.84  thf('57', plain,
% 4.60/4.84      (![X35 : $i, X36 : $i]:
% 4.60/4.84         (~ (v2_funct_2 @ X36 @ X35)
% 4.60/4.84          | ((k2_relat_1 @ X36) = (X35))
% 4.60/4.84          | ~ (v5_relat_1 @ X36 @ X35)
% 4.60/4.84          | ~ (v1_relat_1 @ X36))),
% 4.60/4.84      inference('cnf', [status(esa)], [d3_funct_2])).
% 4.60/4.84  thf('58', plain,
% 4.60/4.84      ((~ (v1_relat_1 @ sk_B)
% 4.60/4.84        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 4.60/4.84        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 4.60/4.84      inference('sup-', [status(thm)], ['56', '57'])).
% 4.60/4.84  thf('59', plain,
% 4.60/4.84      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.60/4.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.60/4.84  thf(cc2_relat_1, axiom,
% 4.60/4.84    (![A:$i]:
% 4.60/4.84     ( ( v1_relat_1 @ A ) =>
% 4.60/4.84       ( ![B:$i]:
% 4.60/4.84         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 4.60/4.84  thf('60', plain,
% 4.60/4.84      (![X15 : $i, X16 : $i]:
% 4.60/4.84         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 4.60/4.84          | (v1_relat_1 @ X15)
% 4.60/4.84          | ~ (v1_relat_1 @ X16))),
% 4.60/4.84      inference('cnf', [status(esa)], [cc2_relat_1])).
% 4.60/4.84  thf('61', plain,
% 4.60/4.84      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 4.60/4.84      inference('sup-', [status(thm)], ['59', '60'])).
% 4.60/4.84  thf(fc6_relat_1, axiom,
% 4.60/4.84    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 4.60/4.84  thf('62', plain,
% 4.60/4.84      (![X17 : $i, X18 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X17 @ X18))),
% 4.60/4.84      inference('cnf', [status(esa)], [fc6_relat_1])).
% 4.60/4.84  thf('63', plain, ((v1_relat_1 @ sk_B)),
% 4.60/4.84      inference('demod', [status(thm)], ['61', '62'])).
% 4.60/4.84  thf('64', plain,
% 4.60/4.84      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.60/4.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.60/4.84  thf(cc2_relset_1, axiom,
% 4.60/4.84    (![A:$i,B:$i,C:$i]:
% 4.60/4.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.60/4.84       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 4.60/4.84  thf('65', plain,
% 4.60/4.84      (![X19 : $i, X20 : $i, X21 : $i]:
% 4.60/4.84         ((v5_relat_1 @ X19 @ X21)
% 4.60/4.84          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 4.60/4.84      inference('cnf', [status(esa)], [cc2_relset_1])).
% 4.60/4.84  thf('66', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 4.60/4.84      inference('sup-', [status(thm)], ['64', '65'])).
% 4.60/4.84  thf('67', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 4.60/4.84      inference('demod', [status(thm)], ['58', '63', '66'])).
% 4.60/4.84  thf('68', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 4.60/4.84      inference('demod', [status(thm)], ['50', '67'])).
% 4.60/4.84  thf('69', plain,
% 4.60/4.84      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.60/4.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.60/4.84  thf('70', plain,
% 4.60/4.84      (![X32 : $i, X33 : $i, X34 : $i]:
% 4.60/4.84         (~ (v1_funct_1 @ X32)
% 4.60/4.84          | ~ (v3_funct_2 @ X32 @ X33 @ X34)
% 4.60/4.84          | (v2_funct_1 @ X32)
% 4.60/4.84          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 4.60/4.84      inference('cnf', [status(esa)], [cc2_funct_2])).
% 4.60/4.84  thf('71', plain,
% 4.60/4.84      (((v2_funct_1 @ sk_B)
% 4.60/4.84        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 4.60/4.84        | ~ (v1_funct_1 @ sk_B))),
% 4.60/4.84      inference('sup-', [status(thm)], ['69', '70'])).
% 4.60/4.84  thf('72', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 4.60/4.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.60/4.84  thf('73', plain, ((v1_funct_1 @ sk_B)),
% 4.60/4.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.60/4.84  thf('74', plain, ((v2_funct_1 @ sk_B)),
% 4.60/4.84      inference('demod', [status(thm)], ['71', '72', '73'])).
% 4.60/4.84  thf('75', plain,
% 4.60/4.84      ((((sk_A) != (sk_A))
% 4.60/4.84        | ((sk_A) = (k1_xboole_0))
% 4.60/4.84        | ((sk_C_1) = (k2_funct_1 @ sk_B)))),
% 4.60/4.84      inference('demod', [status(thm)], ['44', '45', '46', '47', '68', '74'])).
% 4.60/4.84  thf('76', plain,
% 4.60/4.84      ((((sk_C_1) = (k2_funct_1 @ sk_B)) | ((sk_A) = (k1_xboole_0)))),
% 4.60/4.84      inference('simplify', [status(thm)], ['75'])).
% 4.60/4.84  thf('77', plain,
% 4.60/4.84      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ (k2_funct_1 @ sk_B))),
% 4.60/4.84      inference('demod', [status(thm)], ['23', '30'])).
% 4.60/4.84  thf('78', plain,
% 4.60/4.84      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_C_1)
% 4.60/4.84        | ((sk_A) = (k1_xboole_0)))),
% 4.60/4.84      inference('sup-', [status(thm)], ['76', '77'])).
% 4.60/4.84  thf('79', plain,
% 4.60/4.84      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.60/4.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.60/4.84  thf('80', plain,
% 4.60/4.84      (![X29 : $i, X30 : $i, X31 : $i]:
% 4.60/4.84         ((r2_relset_1 @ X29 @ X30 @ X31 @ X31)
% 4.60/4.84          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 4.60/4.84      inference('simplify', [status(thm)], ['18'])).
% 4.60/4.84  thf('81', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_C_1)),
% 4.60/4.84      inference('sup-', [status(thm)], ['79', '80'])).
% 4.60/4.84  thf('82', plain, (((sk_A) = (k1_xboole_0))),
% 4.60/4.84      inference('demod', [status(thm)], ['78', '81'])).
% 4.60/4.84  thf('83', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.60/4.84      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.60/4.84  thf('84', plain, ((v1_xboole_0 @ sk_C_1)),
% 4.60/4.84      inference('demod', [status(thm)], ['35', '82', '83'])).
% 4.60/4.84  thf('85', plain, (~ (v1_xboole_0 @ (k2_funct_1 @ sk_B))),
% 4.60/4.84      inference('demod', [status(thm)], ['32', '84'])).
% 4.60/4.84  thf('86', plain,
% 4.60/4.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.60/4.84         ((r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0))),
% 4.60/4.84      inference('sup+', [status(thm)], ['3', '20'])).
% 4.60/4.84  thf('87', plain,
% 4.60/4.84      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 4.60/4.84      inference('sup-', [status(thm)], ['0', '1'])).
% 4.60/4.84  thf(t113_zfmisc_1, axiom,
% 4.60/4.84    (![A:$i,B:$i]:
% 4.60/4.84     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 4.60/4.84       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 4.60/4.84  thf('88', plain,
% 4.60/4.84      (![X7 : $i, X8 : $i]:
% 4.60/4.84         (((k2_zfmisc_1 @ X7 @ X8) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 4.60/4.84      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 4.60/4.84  thf('89', plain,
% 4.60/4.84      (![X8 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X8) = (k1_xboole_0))),
% 4.60/4.84      inference('simplify', [status(thm)], ['88'])).
% 4.60/4.84  thf('90', plain,
% 4.60/4.84      (![X0 : $i, X1 : $i]:
% 4.60/4.84         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 4.60/4.84      inference('sup+', [status(thm)], ['87', '89'])).
% 4.60/4.84  thf('91', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 4.60/4.84      inference('sup-', [status(thm)], ['9', '10'])).
% 4.60/4.84  thf('92', plain,
% 4.60/4.84      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.60/4.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.60/4.84  thf('93', plain,
% 4.60/4.84      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 4.60/4.84         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 4.60/4.84          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 4.60/4.84          | ((X28) = (X31))
% 4.60/4.84          | ~ (r2_relset_1 @ X29 @ X30 @ X28 @ X31))),
% 4.60/4.84      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 4.60/4.84  thf('94', plain,
% 4.60/4.84      (![X0 : $i]:
% 4.60/4.84         (~ (r2_relset_1 @ sk_A @ sk_A @ sk_B @ X0)
% 4.60/4.84          | ((sk_B) = (X0))
% 4.60/4.84          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 4.60/4.84      inference('sup-', [status(thm)], ['92', '93'])).
% 4.60/4.84  thf('95', plain,
% 4.60/4.84      ((((sk_B) = (k2_zfmisc_1 @ sk_A @ sk_A))
% 4.60/4.84        | ~ (r2_relset_1 @ sk_A @ sk_A @ sk_B @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.60/4.84      inference('sup-', [status(thm)], ['91', '94'])).
% 4.60/4.84  thf('96', plain,
% 4.60/4.84      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_B @ k1_xboole_0)
% 4.60/4.84        | ~ (v1_xboole_0 @ sk_A)
% 4.60/4.84        | ((sk_B) = (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.60/4.84      inference('sup-', [status(thm)], ['90', '95'])).
% 4.60/4.84  thf('97', plain,
% 4.60/4.84      ((~ (v1_xboole_0 @ sk_B)
% 4.60/4.84        | ((sk_B) = (k2_zfmisc_1 @ sk_A @ sk_A))
% 4.60/4.84        | ~ (v1_xboole_0 @ sk_A))),
% 4.60/4.84      inference('sup-', [status(thm)], ['86', '96'])).
% 4.60/4.84  thf('98', plain,
% 4.60/4.84      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.60/4.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.60/4.84  thf('99', plain,
% 4.60/4.84      (![X22 : $i, X23 : $i, X24 : $i]:
% 4.60/4.84         (~ (v1_xboole_0 @ X22)
% 4.60/4.84          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X24)))
% 4.60/4.84          | (v1_xboole_0 @ X23))),
% 4.60/4.84      inference('cnf', [status(esa)], [cc3_relset_1])).
% 4.60/4.84  thf('100', plain, (((v1_xboole_0 @ sk_B) | ~ (v1_xboole_0 @ sk_A))),
% 4.60/4.84      inference('sup-', [status(thm)], ['98', '99'])).
% 4.60/4.84  thf('101', plain,
% 4.60/4.84      ((~ (v1_xboole_0 @ sk_A) | ((sk_B) = (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.60/4.84      inference('clc', [status(thm)], ['97', '100'])).
% 4.60/4.84  thf('102', plain, (((sk_A) = (k1_xboole_0))),
% 4.60/4.84      inference('demod', [status(thm)], ['78', '81'])).
% 4.60/4.84  thf('103', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.60/4.84      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.60/4.84  thf('104', plain, (((sk_A) = (k1_xboole_0))),
% 4.60/4.84      inference('demod', [status(thm)], ['78', '81'])).
% 4.60/4.84  thf('105', plain, (((sk_A) = (k1_xboole_0))),
% 4.60/4.84      inference('demod', [status(thm)], ['78', '81'])).
% 4.60/4.84  thf('106', plain,
% 4.60/4.84      (![X8 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X8) = (k1_xboole_0))),
% 4.60/4.84      inference('simplify', [status(thm)], ['88'])).
% 4.60/4.84  thf('107', plain, (((sk_B) = (k1_xboole_0))),
% 4.60/4.84      inference('demod', [status(thm)],
% 4.60/4.84                ['101', '102', '103', '104', '105', '106'])).
% 4.60/4.84  thf('108', plain, (~ (v1_xboole_0 @ (k2_funct_1 @ k1_xboole_0))),
% 4.60/4.84      inference('demod', [status(thm)], ['85', '107'])).
% 4.60/4.84  thf('109', plain,
% 4.60/4.84      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 4.60/4.84         ((r2_relset_1 @ X3 @ X2 @ X1 @ X0)
% 4.60/4.84          | ~ (v1_xboole_0 @ X0)
% 4.60/4.84          | ~ (v1_xboole_0 @ X1))),
% 4.60/4.84      inference('sup+', [status(thm)], ['2', '21'])).
% 4.60/4.84  thf('110', plain,
% 4.60/4.84      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.60/4.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.60/4.84  thf(dt_k2_funct_2, axiom,
% 4.60/4.84    (![A:$i,B:$i]:
% 4.60/4.84     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 4.60/4.84         ( v3_funct_2 @ B @ A @ A ) & 
% 4.60/4.84         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 4.60/4.84       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 4.60/4.84         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 4.60/4.84         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 4.60/4.84         ( m1_subset_1 @
% 4.60/4.84           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 4.60/4.84  thf('111', plain,
% 4.60/4.84      (![X37 : $i, X38 : $i]:
% 4.60/4.84         ((m1_subset_1 @ (k2_funct_2 @ X37 @ X38) @ 
% 4.60/4.84           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))
% 4.60/4.84          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))
% 4.60/4.84          | ~ (v3_funct_2 @ X38 @ X37 @ X37)
% 4.60/4.84          | ~ (v1_funct_2 @ X38 @ X37 @ X37)
% 4.60/4.84          | ~ (v1_funct_1 @ X38))),
% 4.60/4.84      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 4.60/4.84  thf('112', plain,
% 4.60/4.84      ((~ (v1_funct_1 @ sk_B)
% 4.60/4.84        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 4.60/4.84        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 4.60/4.84        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 4.60/4.84           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 4.60/4.84      inference('sup-', [status(thm)], ['110', '111'])).
% 4.60/4.84  thf('113', plain, ((v1_funct_1 @ sk_B)),
% 4.60/4.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.60/4.84  thf('114', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 4.60/4.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.60/4.84  thf('115', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 4.60/4.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.60/4.84  thf('116', plain,
% 4.60/4.84      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 4.60/4.84        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.60/4.84      inference('demod', [status(thm)], ['112', '113', '114', '115'])).
% 4.60/4.84  thf('117', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 4.60/4.84      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 4.60/4.84  thf('118', plain,
% 4.60/4.84      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 4.60/4.84        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.60/4.84      inference('demod', [status(thm)], ['116', '117'])).
% 4.60/4.84  thf('119', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 4.60/4.84      inference('sup-', [status(thm)], ['9', '10'])).
% 4.60/4.84  thf('120', plain,
% 4.60/4.84      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 4.60/4.84         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 4.60/4.84          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 4.60/4.84          | ((X28) = (X31))
% 4.60/4.84          | ~ (r2_relset_1 @ X29 @ X30 @ X28 @ X31))),
% 4.60/4.84      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 4.60/4.84  thf('121', plain,
% 4.60/4.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.60/4.84         (~ (r2_relset_1 @ X1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0) @ X2)
% 4.60/4.84          | ((k2_zfmisc_1 @ X1 @ X0) = (X2))
% 4.60/4.84          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 4.60/4.84      inference('sup-', [status(thm)], ['119', '120'])).
% 4.60/4.84  thf('122', plain,
% 4.60/4.84      ((((k2_zfmisc_1 @ sk_A @ sk_A) = (k2_funct_1 @ sk_B))
% 4.60/4.84        | ~ (r2_relset_1 @ sk_A @ sk_A @ (k2_zfmisc_1 @ sk_A @ sk_A) @ 
% 4.60/4.84             (k2_funct_1 @ sk_B)))),
% 4.60/4.84      inference('sup-', [status(thm)], ['118', '121'])).
% 4.60/4.84  thf('123', plain,
% 4.60/4.84      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 4.60/4.84        | ~ (v1_xboole_0 @ (k2_funct_1 @ sk_B))
% 4.60/4.84        | ((k2_zfmisc_1 @ sk_A @ sk_A) = (k2_funct_1 @ sk_B)))),
% 4.60/4.84      inference('sup-', [status(thm)], ['109', '122'])).
% 4.60/4.84  thf('124', plain,
% 4.60/4.84      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 4.60/4.84        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.60/4.84      inference('demod', [status(thm)], ['116', '117'])).
% 4.60/4.84  thf('125', plain,
% 4.60/4.84      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 4.60/4.84      inference('sup-', [status(thm)], ['0', '1'])).
% 4.60/4.84  thf('126', plain,
% 4.60/4.84      (![X8 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X8) = (k1_xboole_0))),
% 4.60/4.84      inference('simplify', [status(thm)], ['88'])).
% 4.60/4.84  thf('127', plain,
% 4.60/4.84      (![X22 : $i, X23 : $i, X24 : $i]:
% 4.60/4.84         (~ (v1_xboole_0 @ X22)
% 4.60/4.84          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X24)))
% 4.60/4.84          | (v1_xboole_0 @ X23))),
% 4.60/4.84      inference('cnf', [status(esa)], [cc3_relset_1])).
% 4.60/4.84  thf('128', plain,
% 4.60/4.84      (![X1 : $i]:
% 4.60/4.84         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 4.60/4.84          | (v1_xboole_0 @ X1)
% 4.60/4.84          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 4.60/4.84      inference('sup-', [status(thm)], ['126', '127'])).
% 4.60/4.84  thf('129', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.60/4.84      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.60/4.84  thf('130', plain,
% 4.60/4.84      (![X1 : $i]:
% 4.60/4.84         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 4.60/4.84          | (v1_xboole_0 @ X1))),
% 4.60/4.84      inference('demod', [status(thm)], ['128', '129'])).
% 4.60/4.84  thf('131', plain,
% 4.60/4.84      (![X0 : $i, X1 : $i]:
% 4.60/4.84         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 4.60/4.84          | ~ (v1_xboole_0 @ X0)
% 4.60/4.84          | (v1_xboole_0 @ X1))),
% 4.60/4.84      inference('sup-', [status(thm)], ['125', '130'])).
% 4.60/4.84  thf('132', plain,
% 4.60/4.84      (((v1_xboole_0 @ (k2_funct_1 @ sk_B))
% 4.60/4.84        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.60/4.84      inference('sup-', [status(thm)], ['124', '131'])).
% 4.60/4.84  thf('133', plain,
% 4.60/4.84      ((((k2_zfmisc_1 @ sk_A @ sk_A) = (k2_funct_1 @ sk_B))
% 4.60/4.84        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 4.60/4.84      inference('clc', [status(thm)], ['123', '132'])).
% 4.60/4.84  thf('134', plain, (((sk_A) = (k1_xboole_0))),
% 4.60/4.84      inference('demod', [status(thm)], ['78', '81'])).
% 4.60/4.84  thf('135', plain, (((sk_A) = (k1_xboole_0))),
% 4.60/4.84      inference('demod', [status(thm)], ['78', '81'])).
% 4.60/4.84  thf('136', plain,
% 4.60/4.84      (![X8 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X8) = (k1_xboole_0))),
% 4.60/4.84      inference('simplify', [status(thm)], ['88'])).
% 4.60/4.84  thf('137', plain, (((sk_A) = (k1_xboole_0))),
% 4.60/4.84      inference('demod', [status(thm)], ['78', '81'])).
% 4.60/4.84  thf('138', plain, (((sk_A) = (k1_xboole_0))),
% 4.60/4.84      inference('demod', [status(thm)], ['78', '81'])).
% 4.60/4.84  thf('139', plain,
% 4.60/4.84      (![X8 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X8) = (k1_xboole_0))),
% 4.60/4.84      inference('simplify', [status(thm)], ['88'])).
% 4.60/4.84  thf('140', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.60/4.84      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.60/4.84  thf('141', plain, (((k1_xboole_0) = (k2_funct_1 @ sk_B))),
% 4.60/4.84      inference('demod', [status(thm)],
% 4.60/4.84                ['133', '134', '135', '136', '137', '138', '139', '140'])).
% 4.60/4.84  thf('142', plain, (((sk_B) = (k1_xboole_0))),
% 4.60/4.84      inference('demod', [status(thm)],
% 4.60/4.84                ['101', '102', '103', '104', '105', '106'])).
% 4.60/4.84  thf('143', plain, (((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0))),
% 4.60/4.84      inference('demod', [status(thm)], ['141', '142'])).
% 4.60/4.84  thf('144', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.60/4.84      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.60/4.84  thf('145', plain, ($false),
% 4.60/4.84      inference('demod', [status(thm)], ['108', '143', '144'])).
% 4.60/4.84  
% 4.60/4.84  % SZS output end Refutation
% 4.60/4.84  
% 4.60/4.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
