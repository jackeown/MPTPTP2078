%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EWUHyu0wDJ

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:23 EST 2020

% Result     : Theorem 3.05s
% Output     : Refutation 3.05s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 445 expanded)
%              Number of leaves         :   45 ( 150 expanded)
%              Depth                    :   19
%              Number of atoms          : 1400 (6181 expanded)
%              Number of equality atoms :   67 ( 186 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf('0',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('4',plain,(
    ! [X53: $i] :
      ( ( k6_partfun1 @ X53 )
      = ( k6_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('5',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('8',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('15',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( X33 = X36 )
      | ~ ( r2_relset_1 @ X34 @ X35 @ X33 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','16'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('18',plain,(
    ! [X46: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X46 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('19',plain,(
    ! [X53: $i] :
      ( ( k6_partfun1 @ X53 )
      = ( k6_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('20',plain,(
    ! [X46: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X46 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X46 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
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

thf('23',plain,(
    ! [X54: $i,X55: $i,X56: $i,X57: $i,X58: $i] :
      ( ~ ( v1_funct_1 @ X54 )
      | ~ ( v1_funct_2 @ X54 @ X55 @ X56 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X56 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X57 @ X55 @ X55 @ X56 @ X58 @ X54 ) )
      | ( v2_funct_1 @ X58 )
      | ( X56 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X57 @ X55 ) ) )
      | ~ ( v1_funct_2 @ X58 @ X57 @ X55 )
      | ~ ( v1_funct_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C_1 )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['21','27'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('29',plain,(
    ! [X23: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('30',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v2_funct_1 @ sk_C_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','29','30','31','32'])).

thf('34',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('35',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('37',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('39',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('40',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X46: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X46 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X46 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('42',plain,(
    m1_subset_1 @ ( k6_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('44',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('45',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X29 ) ) )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('46',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('47',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('48',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    v1_xboole_0 @ ( k6_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('51',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X46: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X46 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X46 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('53',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( r2_relset_1 @ X34 @ X35 @ X33 @ X36 )
      | ( X33 != X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('54',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( r2_relset_1 @ X34 @ X35 @ X36 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','54'])).

thf('56',plain,(
    r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ ( k6_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['51','55'])).

thf('57',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['49','50'])).

thf('58',plain,(
    r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','58'])).

thf('60',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('61',plain,(
    ! [X46: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X46 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X46 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('62',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( X33 = X36 )
      | ~ ( r2_relset_1 @ X34 @ X35 @ X33 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ X1 )
      | ( ( k6_relat_1 @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( k6_relat_1 @ k1_xboole_0 )
        = X0 )
      | ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ ( k6_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['49','50'])).

thf('66',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['49','50'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( k1_xboole_0 = X0 )
      | ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['59','67'])).

thf('69',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( k1_xboole_0 = X0 ) ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X1 ) ) ),
    inference('sup-',[status(thm)],['37','70'])).

thf('72',plain,
    ( ( k1_xboole_0 = sk_C_1 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['36','71'])).

thf('73',plain,
    ( ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) )
      | ( k1_xboole_0 = sk_C_1 ) )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['35','72'])).

thf('74',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('75',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('76',plain,
    ( ( k1_xboole_0 = sk_C_1 )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['49','50'])).

thf('78',plain,(
    ! [X23: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('79',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['2','76','79'])).

thf('81',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('82',plain,(
    ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['80','81'])).

thf('83',plain,(
    ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('86',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) )
      | ( ( k1_partfun1 @ X48 @ X49 @ X51 @ X52 @ X47 @ X50 )
        = ( k5_relat_1 @ X47 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C_1 @ X0 )
        = ( k5_relat_1 @ sk_C_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C_1 @ X0 )
        = ( k5_relat_1 @ sk_C_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D )
      = ( k5_relat_1 @ sk_C_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['84','89'])).

thf('91',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('93',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k5_relat_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('94',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X17 @ X16 ) ) @ ( k2_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('95',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k2_relat_1 @ ( k6_relat_1 @ sk_A ) ) )
    | ( ( k2_relat_1 @ sk_D )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['93','96'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('98',plain,(
    ! [X19: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('99',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('100',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v5_relat_1 @ X24 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('101',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['99','100'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('102',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v5_relat_1 @ X11 @ X12 )
      | ( r1_tarski @ ( k2_relat_1 @ X11 ) @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('103',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('105',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('106',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('107',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('108',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['103','108'])).

thf('110',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k5_relat_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('111',plain,(
    ! [X19: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('112',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['106','107'])).

thf('113',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('115',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('117',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['97','98','109','110','111','112','117'])).

thf('119',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('120',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X11 ) @ X12 )
      | ( v5_relat_1 @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('123',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k2_relat_1 @ X38 )
       != X37 )
      | ( v2_funct_2 @ X38 @ X37 )
      | ~ ( v5_relat_1 @ X38 @ X37 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('124',plain,(
    ! [X38: $i] :
      ( ~ ( v1_relat_1 @ X38 )
      | ~ ( v5_relat_1 @ X38 @ ( k2_relat_1 @ X38 ) )
      | ( v2_funct_2 @ X38 @ ( k2_relat_1 @ X38 ) ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_2 @ X0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['122','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( v2_funct_2 @ X0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,
    ( ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['118','126'])).

thf('128',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['106','107'])).

thf('129',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    $false ),
    inference(demod,[status(thm)],['83','129'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EWUHyu0wDJ
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:41:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 3.05/3.27  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.05/3.27  % Solved by: fo/fo7.sh
% 3.05/3.27  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.05/3.27  % done 4944 iterations in 2.796s
% 3.05/3.27  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.05/3.27  % SZS output start Refutation
% 3.05/3.27  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 3.05/3.27  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.05/3.27  thf(sk_B_1_type, type, sk_B_1: $i).
% 3.05/3.27  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.05/3.27  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.05/3.27  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.05/3.27  thf(sk_D_type, type, sk_D: $i).
% 3.05/3.27  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.05/3.27  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.05/3.27  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 3.05/3.27  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.05/3.27  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.05/3.27  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.05/3.27  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.05/3.27  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 3.05/3.27  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 3.05/3.27  thf(sk_C_1_type, type, sk_C_1: $i).
% 3.05/3.27  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.05/3.27  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.05/3.27  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 3.05/3.27  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 3.05/3.27  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.05/3.27  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.05/3.27  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.05/3.27  thf(sk_A_type, type, sk_A: $i).
% 3.05/3.27  thf(t29_funct_2, conjecture,
% 3.05/3.27    (![A:$i,B:$i,C:$i]:
% 3.05/3.27     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.05/3.27         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.05/3.27       ( ![D:$i]:
% 3.05/3.27         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.05/3.27             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.05/3.27           ( ( r2_relset_1 @
% 3.05/3.27               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.05/3.27               ( k6_partfun1 @ A ) ) =>
% 3.05/3.27             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 3.05/3.27  thf(zf_stmt_0, negated_conjecture,
% 3.05/3.27    (~( ![A:$i,B:$i,C:$i]:
% 3.05/3.27        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.05/3.27            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.05/3.27          ( ![D:$i]:
% 3.05/3.27            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.05/3.27                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.05/3.27              ( ( r2_relset_1 @
% 3.05/3.27                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.05/3.27                  ( k6_partfun1 @ A ) ) =>
% 3.05/3.27                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 3.05/3.27    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 3.05/3.27  thf('0', plain, ((~ (v2_funct_1 @ sk_C_1) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 3.05/3.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.27  thf('1', plain,
% 3.05/3.27      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 3.05/3.27      inference('split', [status(esa)], ['0'])).
% 3.05/3.27  thf('2', plain, ((~ (v2_funct_1 @ sk_C_1)) <= (~ ((v2_funct_1 @ sk_C_1)))),
% 3.05/3.27      inference('split', [status(esa)], ['0'])).
% 3.05/3.27  thf('3', plain,
% 3.05/3.27      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.05/3.27        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D) @ 
% 3.05/3.27        (k6_partfun1 @ sk_A))),
% 3.05/3.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.27  thf(redefinition_k6_partfun1, axiom,
% 3.05/3.27    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 3.05/3.27  thf('4', plain, (![X53 : $i]: ((k6_partfun1 @ X53) = (k6_relat_1 @ X53))),
% 3.05/3.27      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.05/3.27  thf('5', plain,
% 3.05/3.27      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.05/3.27        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D) @ 
% 3.05/3.27        (k6_relat_1 @ sk_A))),
% 3.05/3.27      inference('demod', [status(thm)], ['3', '4'])).
% 3.05/3.27  thf('6', plain,
% 3.05/3.27      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 3.05/3.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.27  thf('7', plain,
% 3.05/3.27      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.05/3.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.27  thf(dt_k1_partfun1, axiom,
% 3.05/3.27    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.05/3.27     ( ( ( v1_funct_1 @ E ) & 
% 3.05/3.27         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.05/3.27         ( v1_funct_1 @ F ) & 
% 3.05/3.27         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.05/3.27       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 3.05/3.27         ( m1_subset_1 @
% 3.05/3.27           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 3.05/3.27           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 3.05/3.27  thf('8', plain,
% 3.05/3.27      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 3.05/3.27         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 3.05/3.27          | ~ (v1_funct_1 @ X39)
% 3.05/3.27          | ~ (v1_funct_1 @ X42)
% 3.05/3.27          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 3.05/3.27          | (m1_subset_1 @ (k1_partfun1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42) @ 
% 3.05/3.27             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X44))))),
% 3.05/3.27      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 3.05/3.27  thf('9', plain,
% 3.05/3.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.05/3.27         ((m1_subset_1 @ 
% 3.05/3.27           (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C_1 @ X1) @ 
% 3.05/3.27           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.05/3.27          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.05/3.27          | ~ (v1_funct_1 @ X1)
% 3.05/3.27          | ~ (v1_funct_1 @ sk_C_1))),
% 3.05/3.27      inference('sup-', [status(thm)], ['7', '8'])).
% 3.05/3.27  thf('10', plain, ((v1_funct_1 @ sk_C_1)),
% 3.05/3.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.27  thf('11', plain,
% 3.05/3.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.05/3.27         ((m1_subset_1 @ 
% 3.05/3.27           (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C_1 @ X1) @ 
% 3.05/3.27           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.05/3.27          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.05/3.27          | ~ (v1_funct_1 @ X1))),
% 3.05/3.27      inference('demod', [status(thm)], ['9', '10'])).
% 3.05/3.27  thf('12', plain,
% 3.05/3.27      ((~ (v1_funct_1 @ sk_D)
% 3.05/3.27        | (m1_subset_1 @ 
% 3.05/3.27           (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D) @ 
% 3.05/3.27           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.05/3.27      inference('sup-', [status(thm)], ['6', '11'])).
% 3.05/3.27  thf('13', plain, ((v1_funct_1 @ sk_D)),
% 3.05/3.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.27  thf('14', plain,
% 3.05/3.27      ((m1_subset_1 @ 
% 3.05/3.27        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D) @ 
% 3.05/3.27        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.05/3.27      inference('demod', [status(thm)], ['12', '13'])).
% 3.05/3.27  thf(redefinition_r2_relset_1, axiom,
% 3.05/3.27    (![A:$i,B:$i,C:$i,D:$i]:
% 3.05/3.27     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.05/3.27         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.05/3.27       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 3.05/3.27  thf('15', plain,
% 3.05/3.27      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 3.05/3.27         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 3.05/3.27          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 3.05/3.27          | ((X33) = (X36))
% 3.05/3.27          | ~ (r2_relset_1 @ X34 @ X35 @ X33 @ X36))),
% 3.05/3.27      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.05/3.27  thf('16', plain,
% 3.05/3.27      (![X0 : $i]:
% 3.05/3.27         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.05/3.27             (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D) @ X0)
% 3.05/3.27          | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D)
% 3.05/3.27              = (X0))
% 3.05/3.27          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.05/3.27      inference('sup-', [status(thm)], ['14', '15'])).
% 3.05/3.27  thf('17', plain,
% 3.05/3.27      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 3.05/3.27           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 3.05/3.27        | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D)
% 3.05/3.27            = (k6_relat_1 @ sk_A)))),
% 3.05/3.27      inference('sup-', [status(thm)], ['5', '16'])).
% 3.05/3.27  thf(dt_k6_partfun1, axiom,
% 3.05/3.27    (![A:$i]:
% 3.05/3.27     ( ( m1_subset_1 @
% 3.05/3.27         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 3.05/3.27       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 3.05/3.27  thf('18', plain,
% 3.05/3.27      (![X46 : $i]:
% 3.05/3.27         (m1_subset_1 @ (k6_partfun1 @ X46) @ 
% 3.05/3.27          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X46)))),
% 3.05/3.27      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 3.05/3.27  thf('19', plain, (![X53 : $i]: ((k6_partfun1 @ X53) = (k6_relat_1 @ X53))),
% 3.05/3.27      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.05/3.27  thf('20', plain,
% 3.05/3.27      (![X46 : $i]:
% 3.05/3.27         (m1_subset_1 @ (k6_relat_1 @ X46) @ 
% 3.05/3.27          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X46)))),
% 3.05/3.27      inference('demod', [status(thm)], ['18', '19'])).
% 3.05/3.27  thf('21', plain,
% 3.05/3.27      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D)
% 3.05/3.27         = (k6_relat_1 @ sk_A))),
% 3.05/3.27      inference('demod', [status(thm)], ['17', '20'])).
% 3.05/3.27  thf('22', plain,
% 3.05/3.27      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 3.05/3.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.27  thf(t26_funct_2, axiom,
% 3.05/3.27    (![A:$i,B:$i,C:$i,D:$i]:
% 3.05/3.27     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.05/3.27         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.05/3.27       ( ![E:$i]:
% 3.05/3.27         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 3.05/3.27             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.05/3.27           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 3.05/3.27             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 3.05/3.27               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 3.05/3.27  thf('23', plain,
% 3.05/3.27      (![X54 : $i, X55 : $i, X56 : $i, X57 : $i, X58 : $i]:
% 3.05/3.27         (~ (v1_funct_1 @ X54)
% 3.05/3.27          | ~ (v1_funct_2 @ X54 @ X55 @ X56)
% 3.05/3.27          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X56)))
% 3.05/3.27          | ~ (v2_funct_1 @ (k1_partfun1 @ X57 @ X55 @ X55 @ X56 @ X58 @ X54))
% 3.05/3.27          | (v2_funct_1 @ X58)
% 3.05/3.27          | ((X56) = (k1_xboole_0))
% 3.05/3.27          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X57 @ X55)))
% 3.05/3.27          | ~ (v1_funct_2 @ X58 @ X57 @ X55)
% 3.05/3.27          | ~ (v1_funct_1 @ X58))),
% 3.05/3.27      inference('cnf', [status(esa)], [t26_funct_2])).
% 3.05/3.27  thf('24', plain,
% 3.05/3.27      (![X0 : $i, X1 : $i]:
% 3.05/3.27         (~ (v1_funct_1 @ X0)
% 3.05/3.27          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 3.05/3.27          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 3.05/3.27          | ((sk_A) = (k1_xboole_0))
% 3.05/3.27          | (v2_funct_1 @ X0)
% 3.05/3.27          | ~ (v2_funct_1 @ 
% 3.05/3.27               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D))
% 3.05/3.27          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 3.05/3.27          | ~ (v1_funct_1 @ sk_D))),
% 3.05/3.27      inference('sup-', [status(thm)], ['22', '23'])).
% 3.05/3.27  thf('25', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 3.05/3.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.27  thf('26', plain, ((v1_funct_1 @ sk_D)),
% 3.05/3.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.27  thf('27', plain,
% 3.05/3.27      (![X0 : $i, X1 : $i]:
% 3.05/3.27         (~ (v1_funct_1 @ X0)
% 3.05/3.27          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 3.05/3.27          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 3.05/3.27          | ((sk_A) = (k1_xboole_0))
% 3.05/3.27          | (v2_funct_1 @ X0)
% 3.05/3.27          | ~ (v2_funct_1 @ 
% 3.05/3.27               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D)))),
% 3.05/3.27      inference('demod', [status(thm)], ['24', '25', '26'])).
% 3.05/3.27  thf('28', plain,
% 3.05/3.27      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 3.05/3.27        | (v2_funct_1 @ sk_C_1)
% 3.05/3.27        | ((sk_A) = (k1_xboole_0))
% 3.05/3.27        | ~ (m1_subset_1 @ sk_C_1 @ 
% 3.05/3.27             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 3.05/3.27        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)
% 3.05/3.27        | ~ (v1_funct_1 @ sk_C_1))),
% 3.05/3.27      inference('sup-', [status(thm)], ['21', '27'])).
% 3.05/3.27  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 3.05/3.27  thf('29', plain, (![X23 : $i]: (v2_funct_1 @ (k6_relat_1 @ X23))),
% 3.05/3.27      inference('cnf', [status(esa)], [t52_funct_1])).
% 3.05/3.27  thf('30', plain,
% 3.05/3.27      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.05/3.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.27  thf('31', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 3.05/3.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.27  thf('32', plain, ((v1_funct_1 @ sk_C_1)),
% 3.05/3.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.27  thf('33', plain, (((v2_funct_1 @ sk_C_1) | ((sk_A) = (k1_xboole_0)))),
% 3.05/3.27      inference('demod', [status(thm)], ['28', '29', '30', '31', '32'])).
% 3.05/3.27  thf('34', plain, ((~ (v2_funct_1 @ sk_C_1)) <= (~ ((v2_funct_1 @ sk_C_1)))),
% 3.05/3.27      inference('split', [status(esa)], ['0'])).
% 3.05/3.27  thf('35', plain, ((((sk_A) = (k1_xboole_0))) <= (~ ((v2_funct_1 @ sk_C_1)))),
% 3.05/3.27      inference('sup-', [status(thm)], ['33', '34'])).
% 3.05/3.27  thf('36', plain,
% 3.05/3.27      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.05/3.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.27  thf(l13_xboole_0, axiom,
% 3.05/3.27    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 3.05/3.27  thf('37', plain,
% 3.05/3.27      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.05/3.27      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.05/3.27  thf('38', plain,
% 3.05/3.27      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.05/3.27      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.05/3.27  thf(t113_zfmisc_1, axiom,
% 3.05/3.27    (![A:$i,B:$i]:
% 3.05/3.27     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 3.05/3.27       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 3.05/3.27  thf('39', plain,
% 3.05/3.27      (![X5 : $i, X6 : $i]:
% 3.05/3.27         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 3.05/3.27      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.05/3.27  thf('40', plain,
% 3.05/3.27      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 3.05/3.27      inference('simplify', [status(thm)], ['39'])).
% 3.05/3.27  thf('41', plain,
% 3.05/3.27      (![X46 : $i]:
% 3.05/3.27         (m1_subset_1 @ (k6_relat_1 @ X46) @ 
% 3.05/3.27          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X46)))),
% 3.05/3.27      inference('demod', [status(thm)], ['18', '19'])).
% 3.05/3.27  thf('42', plain,
% 3.05/3.27      ((m1_subset_1 @ (k6_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 3.05/3.27      inference('sup+', [status(thm)], ['40', '41'])).
% 3.05/3.27  thf('43', plain,
% 3.05/3.27      (![X5 : $i, X6 : $i]:
% 3.05/3.27         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 3.05/3.27      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.05/3.27  thf('44', plain,
% 3.05/3.27      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 3.05/3.27      inference('simplify', [status(thm)], ['43'])).
% 3.05/3.27  thf(cc3_relset_1, axiom,
% 3.05/3.27    (![A:$i,B:$i]:
% 3.05/3.27     ( ( v1_xboole_0 @ A ) =>
% 3.05/3.27       ( ![C:$i]:
% 3.05/3.27         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.05/3.27           ( v1_xboole_0 @ C ) ) ) ))).
% 3.05/3.27  thf('45', plain,
% 3.05/3.27      (![X27 : $i, X28 : $i, X29 : $i]:
% 3.05/3.27         (~ (v1_xboole_0 @ X27)
% 3.05/3.27          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X29)))
% 3.05/3.27          | (v1_xboole_0 @ X28))),
% 3.05/3.27      inference('cnf', [status(esa)], [cc3_relset_1])).
% 3.05/3.27  thf('46', plain,
% 3.05/3.27      (![X1 : $i]:
% 3.05/3.27         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 3.05/3.27          | (v1_xboole_0 @ X1)
% 3.05/3.27          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 3.05/3.27      inference('sup-', [status(thm)], ['44', '45'])).
% 3.05/3.27  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.05/3.27  thf('47', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.05/3.27      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.05/3.27  thf('48', plain,
% 3.05/3.27      (![X1 : $i]:
% 3.05/3.27         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 3.05/3.27          | (v1_xboole_0 @ X1))),
% 3.05/3.27      inference('demod', [status(thm)], ['46', '47'])).
% 3.05/3.27  thf('49', plain, ((v1_xboole_0 @ (k6_relat_1 @ k1_xboole_0))),
% 3.05/3.27      inference('sup-', [status(thm)], ['42', '48'])).
% 3.05/3.27  thf('50', plain,
% 3.05/3.27      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.05/3.27      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.05/3.27  thf('51', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.05/3.27      inference('sup-', [status(thm)], ['49', '50'])).
% 3.05/3.27  thf('52', plain,
% 3.05/3.27      (![X46 : $i]:
% 3.05/3.27         (m1_subset_1 @ (k6_relat_1 @ X46) @ 
% 3.05/3.27          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X46)))),
% 3.05/3.27      inference('demod', [status(thm)], ['18', '19'])).
% 3.05/3.27  thf('53', plain,
% 3.05/3.27      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 3.05/3.27         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 3.05/3.27          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 3.05/3.27          | (r2_relset_1 @ X34 @ X35 @ X33 @ X36)
% 3.05/3.27          | ((X33) != (X36)))),
% 3.05/3.27      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.05/3.27  thf('54', plain,
% 3.05/3.27      (![X34 : $i, X35 : $i, X36 : $i]:
% 3.05/3.27         ((r2_relset_1 @ X34 @ X35 @ X36 @ X36)
% 3.05/3.27          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 3.05/3.27      inference('simplify', [status(thm)], ['53'])).
% 3.05/3.27  thf('55', plain,
% 3.05/3.27      (![X0 : $i]:
% 3.05/3.27         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 3.05/3.27      inference('sup-', [status(thm)], ['52', '54'])).
% 3.05/3.27  thf('56', plain,
% 3.05/3.27      ((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ 
% 3.05/3.27        (k6_relat_1 @ k1_xboole_0))),
% 3.05/3.27      inference('sup+', [status(thm)], ['51', '55'])).
% 3.05/3.27  thf('57', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.05/3.27      inference('sup-', [status(thm)], ['49', '50'])).
% 3.05/3.27  thf('58', plain,
% 3.05/3.27      ((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 3.05/3.27      inference('demod', [status(thm)], ['56', '57'])).
% 3.05/3.27  thf('59', plain,
% 3.05/3.27      (![X0 : $i]:
% 3.05/3.27         ((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 3.05/3.27          | ~ (v1_xboole_0 @ X0))),
% 3.05/3.27      inference('sup+', [status(thm)], ['38', '58'])).
% 3.05/3.27  thf('60', plain,
% 3.05/3.27      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 3.05/3.27      inference('simplify', [status(thm)], ['39'])).
% 3.05/3.27  thf('61', plain,
% 3.05/3.27      (![X46 : $i]:
% 3.05/3.27         (m1_subset_1 @ (k6_relat_1 @ X46) @ 
% 3.05/3.27          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X46)))),
% 3.05/3.27      inference('demod', [status(thm)], ['18', '19'])).
% 3.05/3.27  thf('62', plain,
% 3.05/3.27      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 3.05/3.27         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 3.05/3.27          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 3.05/3.27          | ((X33) = (X36))
% 3.05/3.27          | ~ (r2_relset_1 @ X34 @ X35 @ X33 @ X36))),
% 3.05/3.27      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.05/3.27  thf('63', plain,
% 3.05/3.27      (![X0 : $i, X1 : $i]:
% 3.05/3.27         (~ (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ X1)
% 3.05/3.27          | ((k6_relat_1 @ X0) = (X1))
% 3.05/3.27          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0))))),
% 3.05/3.27      inference('sup-', [status(thm)], ['61', '62'])).
% 3.05/3.27  thf('64', plain,
% 3.05/3.27      (![X0 : $i]:
% 3.05/3.27         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 3.05/3.27          | ((k6_relat_1 @ k1_xboole_0) = (X0))
% 3.05/3.27          | ~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ 
% 3.05/3.27               (k6_relat_1 @ k1_xboole_0) @ X0))),
% 3.05/3.27      inference('sup-', [status(thm)], ['60', '63'])).
% 3.05/3.27  thf('65', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.05/3.27      inference('sup-', [status(thm)], ['49', '50'])).
% 3.05/3.27  thf('66', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.05/3.27      inference('sup-', [status(thm)], ['49', '50'])).
% 3.05/3.27  thf('67', plain,
% 3.05/3.27      (![X0 : $i]:
% 3.05/3.27         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 3.05/3.27          | ((k1_xboole_0) = (X0))
% 3.05/3.27          | ~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ X0))),
% 3.05/3.27      inference('demod', [status(thm)], ['64', '65', '66'])).
% 3.05/3.27  thf('68', plain,
% 3.05/3.27      (![X0 : $i]:
% 3.05/3.27         (~ (v1_xboole_0 @ X0)
% 3.05/3.27          | ((k1_xboole_0) = (X0))
% 3.05/3.27          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 3.05/3.27      inference('sup-', [status(thm)], ['59', '67'])).
% 3.05/3.27  thf('69', plain,
% 3.05/3.27      (![X1 : $i]:
% 3.05/3.27         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 3.05/3.27          | (v1_xboole_0 @ X1))),
% 3.05/3.27      inference('demod', [status(thm)], ['46', '47'])).
% 3.05/3.27  thf('70', plain,
% 3.05/3.27      (![X0 : $i]:
% 3.05/3.27         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 3.05/3.27          | ((k1_xboole_0) = (X0)))),
% 3.05/3.27      inference('clc', [status(thm)], ['68', '69'])).
% 3.05/3.27  thf('71', plain,
% 3.05/3.27      (![X0 : $i, X1 : $i]:
% 3.05/3.27         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 3.05/3.27          | ~ (v1_xboole_0 @ X0)
% 3.05/3.27          | ((k1_xboole_0) = (X1)))),
% 3.05/3.27      inference('sup-', [status(thm)], ['37', '70'])).
% 3.05/3.27  thf('72', plain,
% 3.05/3.27      ((((k1_xboole_0) = (sk_C_1))
% 3.05/3.27        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.05/3.27      inference('sup-', [status(thm)], ['36', '71'])).
% 3.05/3.27  thf('73', plain,
% 3.05/3.27      (((~ (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))
% 3.05/3.27         | ((k1_xboole_0) = (sk_C_1)))) <= (~ ((v2_funct_1 @ sk_C_1)))),
% 3.05/3.27      inference('sup-', [status(thm)], ['35', '72'])).
% 3.05/3.27  thf('74', plain,
% 3.05/3.27      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 3.05/3.27      inference('simplify', [status(thm)], ['43'])).
% 3.05/3.27  thf('75', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.05/3.27      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.05/3.27  thf('76', plain,
% 3.05/3.27      ((((k1_xboole_0) = (sk_C_1))) <= (~ ((v2_funct_1 @ sk_C_1)))),
% 3.05/3.27      inference('demod', [status(thm)], ['73', '74', '75'])).
% 3.05/3.27  thf('77', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.05/3.27      inference('sup-', [status(thm)], ['49', '50'])).
% 3.05/3.27  thf('78', plain, (![X23 : $i]: (v2_funct_1 @ (k6_relat_1 @ X23))),
% 3.05/3.27      inference('cnf', [status(esa)], [t52_funct_1])).
% 3.05/3.27  thf('79', plain, ((v2_funct_1 @ k1_xboole_0)),
% 3.05/3.27      inference('sup+', [status(thm)], ['77', '78'])).
% 3.05/3.27  thf('80', plain, (((v2_funct_1 @ sk_C_1))),
% 3.05/3.27      inference('demod', [status(thm)], ['2', '76', '79'])).
% 3.05/3.27  thf('81', plain,
% 3.05/3.27      (~ ((v2_funct_2 @ sk_D @ sk_A)) | ~ ((v2_funct_1 @ sk_C_1))),
% 3.05/3.27      inference('split', [status(esa)], ['0'])).
% 3.05/3.27  thf('82', plain, (~ ((v2_funct_2 @ sk_D @ sk_A))),
% 3.05/3.27      inference('sat_resolution*', [status(thm)], ['80', '81'])).
% 3.05/3.27  thf('83', plain, (~ (v2_funct_2 @ sk_D @ sk_A)),
% 3.05/3.27      inference('simpl_trail', [status(thm)], ['1', '82'])).
% 3.05/3.27  thf('84', plain,
% 3.05/3.27      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 3.05/3.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.27  thf('85', plain,
% 3.05/3.27      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.05/3.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.27  thf(redefinition_k1_partfun1, axiom,
% 3.05/3.27    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.05/3.27     ( ( ( v1_funct_1 @ E ) & 
% 3.05/3.27         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.05/3.27         ( v1_funct_1 @ F ) & 
% 3.05/3.27         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.05/3.27       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 3.05/3.27  thf('86', plain,
% 3.05/3.27      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 3.05/3.27         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 3.05/3.27          | ~ (v1_funct_1 @ X47)
% 3.05/3.27          | ~ (v1_funct_1 @ X50)
% 3.05/3.27          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52)))
% 3.05/3.27          | ((k1_partfun1 @ X48 @ X49 @ X51 @ X52 @ X47 @ X50)
% 3.05/3.27              = (k5_relat_1 @ X47 @ X50)))),
% 3.05/3.27      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 3.05/3.27  thf('87', plain,
% 3.05/3.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.05/3.27         (((k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C_1 @ X0)
% 3.05/3.27            = (k5_relat_1 @ sk_C_1 @ X0))
% 3.05/3.27          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.05/3.27          | ~ (v1_funct_1 @ X0)
% 3.05/3.27          | ~ (v1_funct_1 @ sk_C_1))),
% 3.05/3.27      inference('sup-', [status(thm)], ['85', '86'])).
% 3.05/3.27  thf('88', plain, ((v1_funct_1 @ sk_C_1)),
% 3.05/3.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.27  thf('89', plain,
% 3.05/3.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.05/3.27         (((k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C_1 @ X0)
% 3.05/3.27            = (k5_relat_1 @ sk_C_1 @ X0))
% 3.05/3.27          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.05/3.27          | ~ (v1_funct_1 @ X0))),
% 3.05/3.27      inference('demod', [status(thm)], ['87', '88'])).
% 3.05/3.27  thf('90', plain,
% 3.05/3.27      ((~ (v1_funct_1 @ sk_D)
% 3.05/3.27        | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D)
% 3.05/3.27            = (k5_relat_1 @ sk_C_1 @ sk_D)))),
% 3.05/3.27      inference('sup-', [status(thm)], ['84', '89'])).
% 3.05/3.27  thf('91', plain, ((v1_funct_1 @ sk_D)),
% 3.05/3.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.27  thf('92', plain,
% 3.05/3.27      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D)
% 3.05/3.27         = (k6_relat_1 @ sk_A))),
% 3.05/3.27      inference('demod', [status(thm)], ['17', '20'])).
% 3.05/3.27  thf('93', plain, (((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_C_1 @ sk_D))),
% 3.05/3.27      inference('demod', [status(thm)], ['90', '91', '92'])).
% 3.05/3.27  thf(t45_relat_1, axiom,
% 3.05/3.27    (![A:$i]:
% 3.05/3.27     ( ( v1_relat_1 @ A ) =>
% 3.05/3.27       ( ![B:$i]:
% 3.05/3.27         ( ( v1_relat_1 @ B ) =>
% 3.05/3.27           ( r1_tarski @
% 3.05/3.27             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 3.05/3.27  thf('94', plain,
% 3.05/3.27      (![X16 : $i, X17 : $i]:
% 3.05/3.27         (~ (v1_relat_1 @ X16)
% 3.05/3.27          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X17 @ X16)) @ 
% 3.05/3.27             (k2_relat_1 @ X16))
% 3.05/3.27          | ~ (v1_relat_1 @ X17))),
% 3.05/3.27      inference('cnf', [status(esa)], [t45_relat_1])).
% 3.05/3.27  thf(d10_xboole_0, axiom,
% 3.05/3.27    (![A:$i,B:$i]:
% 3.05/3.27     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.05/3.27  thf('95', plain,
% 3.05/3.27      (![X1 : $i, X3 : $i]:
% 3.05/3.27         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 3.05/3.27      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.05/3.27  thf('96', plain,
% 3.05/3.27      (![X0 : $i, X1 : $i]:
% 3.05/3.27         (~ (v1_relat_1 @ X1)
% 3.05/3.27          | ~ (v1_relat_1 @ X0)
% 3.05/3.27          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 3.05/3.27               (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 3.05/3.27          | ((k2_relat_1 @ X0) = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 3.05/3.27      inference('sup-', [status(thm)], ['94', '95'])).
% 3.05/3.27  thf('97', plain,
% 3.05/3.27      ((~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k2_relat_1 @ (k6_relat_1 @ sk_A)))
% 3.05/3.27        | ((k2_relat_1 @ sk_D) = (k2_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_D)))
% 3.05/3.27        | ~ (v1_relat_1 @ sk_D)
% 3.05/3.27        | ~ (v1_relat_1 @ sk_C_1))),
% 3.05/3.27      inference('sup-', [status(thm)], ['93', '96'])).
% 3.05/3.27  thf(t71_relat_1, axiom,
% 3.05/3.27    (![A:$i]:
% 3.05/3.27     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 3.05/3.27       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 3.05/3.27  thf('98', plain, (![X19 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X19)) = (X19))),
% 3.05/3.27      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.05/3.27  thf('99', plain,
% 3.05/3.27      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 3.05/3.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.27  thf(cc2_relset_1, axiom,
% 3.05/3.27    (![A:$i,B:$i,C:$i]:
% 3.05/3.27     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.05/3.27       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.05/3.27  thf('100', plain,
% 3.05/3.27      (![X24 : $i, X25 : $i, X26 : $i]:
% 3.05/3.27         ((v5_relat_1 @ X24 @ X26)
% 3.05/3.27          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 3.05/3.27      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.05/3.27  thf('101', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 3.05/3.27      inference('sup-', [status(thm)], ['99', '100'])).
% 3.05/3.27  thf(d19_relat_1, axiom,
% 3.05/3.27    (![A:$i,B:$i]:
% 3.05/3.27     ( ( v1_relat_1 @ B ) =>
% 3.05/3.27       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 3.05/3.27  thf('102', plain,
% 3.05/3.27      (![X11 : $i, X12 : $i]:
% 3.05/3.27         (~ (v5_relat_1 @ X11 @ X12)
% 3.05/3.27          | (r1_tarski @ (k2_relat_1 @ X11) @ X12)
% 3.05/3.27          | ~ (v1_relat_1 @ X11))),
% 3.05/3.27      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.05/3.27  thf('103', plain,
% 3.05/3.27      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A))),
% 3.05/3.27      inference('sup-', [status(thm)], ['101', '102'])).
% 3.05/3.27  thf('104', plain,
% 3.05/3.27      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 3.05/3.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.27  thf(cc2_relat_1, axiom,
% 3.05/3.27    (![A:$i]:
% 3.05/3.27     ( ( v1_relat_1 @ A ) =>
% 3.05/3.27       ( ![B:$i]:
% 3.05/3.27         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 3.05/3.27  thf('105', plain,
% 3.05/3.27      (![X9 : $i, X10 : $i]:
% 3.05/3.27         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 3.05/3.27          | (v1_relat_1 @ X9)
% 3.05/3.27          | ~ (v1_relat_1 @ X10))),
% 3.05/3.27      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.05/3.27  thf('106', plain,
% 3.05/3.27      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)) | (v1_relat_1 @ sk_D))),
% 3.05/3.27      inference('sup-', [status(thm)], ['104', '105'])).
% 3.05/3.27  thf(fc6_relat_1, axiom,
% 3.05/3.27    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 3.05/3.27  thf('107', plain,
% 3.05/3.27      (![X14 : $i, X15 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X14 @ X15))),
% 3.05/3.27      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.05/3.27  thf('108', plain, ((v1_relat_1 @ sk_D)),
% 3.05/3.27      inference('demod', [status(thm)], ['106', '107'])).
% 3.05/3.27  thf('109', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)),
% 3.05/3.27      inference('demod', [status(thm)], ['103', '108'])).
% 3.05/3.27  thf('110', plain, (((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_C_1 @ sk_D))),
% 3.05/3.27      inference('demod', [status(thm)], ['90', '91', '92'])).
% 3.05/3.27  thf('111', plain, (![X19 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X19)) = (X19))),
% 3.05/3.27      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.05/3.27  thf('112', plain, ((v1_relat_1 @ sk_D)),
% 3.05/3.27      inference('demod', [status(thm)], ['106', '107'])).
% 3.05/3.27  thf('113', plain,
% 3.05/3.27      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.05/3.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.05/3.27  thf('114', plain,
% 3.05/3.27      (![X9 : $i, X10 : $i]:
% 3.05/3.27         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 3.05/3.27          | (v1_relat_1 @ X9)
% 3.05/3.27          | ~ (v1_relat_1 @ X10))),
% 3.05/3.27      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.05/3.27  thf('115', plain,
% 3.05/3.27      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_C_1))),
% 3.05/3.27      inference('sup-', [status(thm)], ['113', '114'])).
% 3.05/3.27  thf('116', plain,
% 3.05/3.27      (![X14 : $i, X15 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X14 @ X15))),
% 3.05/3.27      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.05/3.27  thf('117', plain, ((v1_relat_1 @ sk_C_1)),
% 3.05/3.27      inference('demod', [status(thm)], ['115', '116'])).
% 3.05/3.27  thf('118', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.05/3.27      inference('demod', [status(thm)],
% 3.05/3.27                ['97', '98', '109', '110', '111', '112', '117'])).
% 3.05/3.27  thf('119', plain,
% 3.05/3.27      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 3.05/3.27      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.05/3.27  thf('120', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 3.05/3.27      inference('simplify', [status(thm)], ['119'])).
% 3.05/3.27  thf('121', plain,
% 3.05/3.27      (![X11 : $i, X12 : $i]:
% 3.05/3.27         (~ (r1_tarski @ (k2_relat_1 @ X11) @ X12)
% 3.05/3.27          | (v5_relat_1 @ X11 @ X12)
% 3.05/3.27          | ~ (v1_relat_1 @ X11))),
% 3.05/3.27      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.05/3.27  thf('122', plain,
% 3.05/3.27      (![X0 : $i]:
% 3.05/3.27         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 3.05/3.27      inference('sup-', [status(thm)], ['120', '121'])).
% 3.05/3.27  thf(d3_funct_2, axiom,
% 3.05/3.27    (![A:$i,B:$i]:
% 3.05/3.27     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 3.05/3.27       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 3.05/3.27  thf('123', plain,
% 3.05/3.27      (![X37 : $i, X38 : $i]:
% 3.05/3.27         (((k2_relat_1 @ X38) != (X37))
% 3.05/3.27          | (v2_funct_2 @ X38 @ X37)
% 3.05/3.27          | ~ (v5_relat_1 @ X38 @ X37)
% 3.05/3.27          | ~ (v1_relat_1 @ X38))),
% 3.05/3.27      inference('cnf', [status(esa)], [d3_funct_2])).
% 3.05/3.27  thf('124', plain,
% 3.05/3.27      (![X38 : $i]:
% 3.05/3.27         (~ (v1_relat_1 @ X38)
% 3.05/3.27          | ~ (v5_relat_1 @ X38 @ (k2_relat_1 @ X38))
% 3.05/3.27          | (v2_funct_2 @ X38 @ (k2_relat_1 @ X38)))),
% 3.05/3.27      inference('simplify', [status(thm)], ['123'])).
% 3.05/3.27  thf('125', plain,
% 3.05/3.27      (![X0 : $i]:
% 3.05/3.27         (~ (v1_relat_1 @ X0)
% 3.05/3.27          | (v2_funct_2 @ X0 @ (k2_relat_1 @ X0))
% 3.05/3.27          | ~ (v1_relat_1 @ X0))),
% 3.05/3.27      inference('sup-', [status(thm)], ['122', '124'])).
% 3.05/3.27  thf('126', plain,
% 3.05/3.27      (![X0 : $i]:
% 3.05/3.27         ((v2_funct_2 @ X0 @ (k2_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 3.05/3.27      inference('simplify', [status(thm)], ['125'])).
% 3.05/3.27  thf('127', plain, (((v2_funct_2 @ sk_D @ sk_A) | ~ (v1_relat_1 @ sk_D))),
% 3.05/3.27      inference('sup+', [status(thm)], ['118', '126'])).
% 3.05/3.27  thf('128', plain, ((v1_relat_1 @ sk_D)),
% 3.05/3.27      inference('demod', [status(thm)], ['106', '107'])).
% 3.05/3.27  thf('129', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 3.05/3.27      inference('demod', [status(thm)], ['127', '128'])).
% 3.05/3.27  thf('130', plain, ($false), inference('demod', [status(thm)], ['83', '129'])).
% 3.05/3.27  
% 3.05/3.27  % SZS output end Refutation
% 3.05/3.27  
% 3.05/3.28  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
