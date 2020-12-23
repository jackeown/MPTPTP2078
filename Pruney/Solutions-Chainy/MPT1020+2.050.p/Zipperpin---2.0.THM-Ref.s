%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zU9U3z7M87

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:08 EST 2020

% Result     : Theorem 1.98s
% Output     : Refutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 890 expanded)
%              Number of leaves         :   45 ( 284 expanded)
%              Depth                    :   15
%              Number of atoms          : 1262 (20115 expanded)
%              Number of equality atoms :   82 ( 389 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

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

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k2_funct_2 @ A @ B )
        = ( k2_funct_1 @ B ) ) ) )).

thf('2',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k2_funct_2 @ X34 @ X33 )
        = ( k2_funct_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) )
      | ~ ( v3_funct_2 @ X33 @ X34 @ X34 )
      | ~ ( v1_funct_2 @ X33 @ X34 @ X34 )
      | ~ ( v1_funct_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_B_1 )
      = ( k2_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('8',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('9',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('10',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('11',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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

thf('13',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( X40
        = ( k2_funct_1 @ X43 ) )
      | ~ ( r2_relset_1 @ X42 @ X42 @ ( k1_partfun1 @ X42 @ X41 @ X41 @ X42 @ X43 @ X40 ) @ ( k6_partfun1 @ X42 ) )
      | ( X41 = k1_xboole_0 )
      | ( X42 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X43 )
      | ( ( k2_relset_1 @ X42 @ X41 @ X43 )
       != X41 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) )
      | ~ ( v1_funct_2 @ X43 @ X42 @ X41 )
      | ~ ( v1_funct_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t36_funct_2])).

thf('14',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('15',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( X40
        = ( k2_funct_1 @ X43 ) )
      | ~ ( r2_relset_1 @ X42 @ X42 @ ( k1_partfun1 @ X42 @ X41 @ X41 @ X42 @ X43 @ X40 ) @ ( k6_relat_1 @ X42 ) )
      | ( X41 = k1_xboole_0 )
      | ( X42 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X43 )
      | ( ( k2_relset_1 @ X42 @ X41 @ X43 )
       != X41 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) )
      | ~ ( v1_funct_2 @ X43 @ X42 @ X41 )
      | ~ ( v1_funct_1 @ X43 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( v2_funct_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_relat_1 @ sk_A ) )
      | ( sk_C
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( v2_funct_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_relat_1 @ sk_A ) )
      | ( sk_C
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( sk_C
        = ( k2_funct_1 @ X0 ) )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_relat_1 @ sk_A ) )
      | ( sk_A = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B_1 )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['11','20'])).

thf('22',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('26',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k2_relset_1 @ X20 @ X21 @ X19 )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('27',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B_1 )
    = ( k2_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v3_funct_2 @ C @ A @ B ) )
       => ( ( v1_funct_1 @ C )
          & ( v2_funct_1 @ C )
          & ( v2_funct_2 @ C @ B ) ) ) ) )).

thf('29',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_1 @ X26 )
      | ~ ( v3_funct_2 @ X26 @ X27 @ X28 )
      | ( v2_funct_2 @ X26 @ X28 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('30',plain,
    ( ( v2_funct_2 @ sk_B_1 @ sk_A )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v2_funct_2 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['30','31','32'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('34',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v2_funct_2 @ X30 @ X29 )
      | ( ( k2_relat_1 @ X30 )
        = X29 )
      | ~ ( v5_relat_1 @ X30 @ X29 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v5_relat_1 @ sk_B_1 @ sk_A )
    | ( ( k2_relat_1 @ sk_B_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('37',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('39',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('40',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('42',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v5_relat_1 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('43',plain,(
    v5_relat_1 @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['35','40','43'])).

thf('45',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['27','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_1 @ X26 )
      | ~ ( v3_funct_2 @ X26 @ X27 @ X28 )
      | ( v2_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('48',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,
    ( ( sk_A != sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['21','22','23','24','45','51'])).

thf('53',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_B_1 ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('55',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('57',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( r2_relset_1 @ X23 @ X24 @ X22 @ X25 )
      | ( X22 != X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('58',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r2_relset_1 @ X23 @ X24 @ X25 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['56','58'])).

thf('60',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['55','59'])).

thf('61',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['55','59'])).

thf('62',plain,(
    ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['8','60','61'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('63',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('65',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['55','59'])).

thf('68',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['55','59'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('69',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('70',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['69'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('71',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('72',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_C ) ),
    inference(demod,[status(thm)],['66','67','68','70','71'])).

thf('73',plain,(
    v1_xboole_0 @ sk_C ),
    inference('sup-',[status(thm)],['63','72'])).

thf('74',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('75',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    k1_xboole_0 = sk_C ),
    inference('sup-',[status(thm)],['73','76'])).

thf('78',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('79',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['55','59'])).

thf('83',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['55','59'])).

thf('84',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['69'])).

thf('85',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('86',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['81','82','83','84','85'])).

thf('87',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['78','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('89',plain,(
    k1_xboole_0 = sk_B_1 ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('91',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('92',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['91'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('93',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('94',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('95',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    m1_subset_1 @ ( k6_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['92','95'])).

thf('97',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k6_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('100',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k6_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    v1_xboole_0 @ ( k6_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['90','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('103',plain,
    ( k1_xboole_0
    = ( k6_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf(t67_funct_1,axiom,(
    ! [A: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('104',plain,(
    ! [X15: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ X15 ) )
      = ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_1])).

thf('105',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = ( k6_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,
    ( k1_xboole_0
    = ( k6_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('107',plain,
    ( k1_xboole_0
    = ( k2_funct_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['69'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('110',plain,(
    m1_subset_1 @ ( k6_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['92','95'])).

thf('111',plain,
    ( k1_xboole_0
    = ( k6_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('112',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['109','112'])).

thf('114',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r2_relset_1 @ X23 @ X24 @ X25 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['108','115'])).

thf('117',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('118',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    $false ),
    inference(demod,[status(thm)],['62','77','89','107','118'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zU9U3z7M87
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:08:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 1.98/2.19  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.98/2.19  % Solved by: fo/fo7.sh
% 1.98/2.19  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.98/2.19  % done 2862 iterations in 1.719s
% 1.98/2.19  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.98/2.19  % SZS output start Refutation
% 1.98/2.19  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.98/2.19  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 1.98/2.19  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.98/2.19  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.98/2.19  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.98/2.19  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.98/2.19  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.98/2.19  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.98/2.19  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.98/2.19  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.98/2.19  thf(sk_A_type, type, sk_A: $i).
% 1.98/2.19  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.98/2.19  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.98/2.19  thf(sk_C_type, type, sk_C: $i).
% 1.98/2.19  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.98/2.19  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 1.98/2.19  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.98/2.19  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 1.98/2.19  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.98/2.19  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.98/2.19  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.98/2.19  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.98/2.19  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.98/2.19  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.98/2.19  thf(sk_B_type, type, sk_B: $i > $i).
% 1.98/2.19  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.98/2.19  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.98/2.19  thf(t87_funct_2, conjecture,
% 1.98/2.19    (![A:$i,B:$i]:
% 1.98/2.19     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.98/2.19         ( v3_funct_2 @ B @ A @ A ) & 
% 1.98/2.19         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.98/2.19       ( ![C:$i]:
% 1.98/2.19         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 1.98/2.19             ( v3_funct_2 @ C @ A @ A ) & 
% 1.98/2.19             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.98/2.19           ( ( r2_relset_1 @
% 1.98/2.19               A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 1.98/2.19               ( k6_partfun1 @ A ) ) =>
% 1.98/2.19             ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ))).
% 1.98/2.19  thf(zf_stmt_0, negated_conjecture,
% 1.98/2.19    (~( ![A:$i,B:$i]:
% 1.98/2.19        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.98/2.19            ( v3_funct_2 @ B @ A @ A ) & 
% 1.98/2.19            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.98/2.19          ( ![C:$i]:
% 1.98/2.19            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 1.98/2.19                ( v3_funct_2 @ C @ A @ A ) & 
% 1.98/2.19                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.98/2.19              ( ( r2_relset_1 @
% 1.98/2.19                  A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 1.98/2.19                  ( k6_partfun1 @ A ) ) =>
% 1.98/2.19                ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ) )),
% 1.98/2.19    inference('cnf.neg', [status(esa)], [t87_funct_2])).
% 1.98/2.19  thf('0', plain,
% 1.98/2.19      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_2 @ sk_A @ sk_B_1))),
% 1.98/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.19  thf('1', plain,
% 1.98/2.19      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.98/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.19  thf(redefinition_k2_funct_2, axiom,
% 1.98/2.19    (![A:$i,B:$i]:
% 1.98/2.19     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.98/2.19         ( v3_funct_2 @ B @ A @ A ) & 
% 1.98/2.19         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.98/2.19       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 1.98/2.19  thf('2', plain,
% 1.98/2.19      (![X33 : $i, X34 : $i]:
% 1.98/2.19         (((k2_funct_2 @ X34 @ X33) = (k2_funct_1 @ X33))
% 1.98/2.19          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))
% 1.98/2.19          | ~ (v3_funct_2 @ X33 @ X34 @ X34)
% 1.98/2.19          | ~ (v1_funct_2 @ X33 @ X34 @ X34)
% 1.98/2.19          | ~ (v1_funct_1 @ X33))),
% 1.98/2.19      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 1.98/2.19  thf('3', plain,
% 1.98/2.19      ((~ (v1_funct_1 @ sk_B_1)
% 1.98/2.19        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 1.98/2.19        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 1.98/2.19        | ((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1)))),
% 1.98/2.19      inference('sup-', [status(thm)], ['1', '2'])).
% 1.98/2.19  thf('4', plain, ((v1_funct_1 @ sk_B_1)),
% 1.98/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.19  thf('5', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 1.98/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.19  thf('6', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 1.98/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.19  thf('7', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 1.98/2.19      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 1.98/2.19  thf('8', plain,
% 1.98/2.19      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B_1))),
% 1.98/2.19      inference('demod', [status(thm)], ['0', '7'])).
% 1.98/2.19  thf('9', plain,
% 1.98/2.19      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.98/2.19        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C) @ 
% 1.98/2.19        (k6_partfun1 @ sk_A))),
% 1.98/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.19  thf(redefinition_k6_partfun1, axiom,
% 1.98/2.19    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.98/2.19  thf('10', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 1.98/2.19      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.98/2.19  thf('11', plain,
% 1.98/2.19      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.98/2.19        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C) @ 
% 1.98/2.19        (k6_relat_1 @ sk_A))),
% 1.98/2.19      inference('demod', [status(thm)], ['9', '10'])).
% 1.98/2.19  thf('12', plain,
% 1.98/2.19      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.98/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.19  thf(t36_funct_2, axiom,
% 1.98/2.19    (![A:$i,B:$i,C:$i]:
% 1.98/2.19     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.98/2.19         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.98/2.19       ( ![D:$i]:
% 1.98/2.19         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.98/2.19             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.98/2.19           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.98/2.19               ( r2_relset_1 @
% 1.98/2.19                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.98/2.19                 ( k6_partfun1 @ A ) ) & 
% 1.98/2.19               ( v2_funct_1 @ C ) ) =>
% 1.98/2.19             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.98/2.19               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.98/2.19  thf('13', plain,
% 1.98/2.19      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 1.98/2.19         (~ (v1_funct_1 @ X40)
% 1.98/2.19          | ~ (v1_funct_2 @ X40 @ X41 @ X42)
% 1.98/2.19          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 1.98/2.19          | ((X40) = (k2_funct_1 @ X43))
% 1.98/2.19          | ~ (r2_relset_1 @ X42 @ X42 @ 
% 1.98/2.19               (k1_partfun1 @ X42 @ X41 @ X41 @ X42 @ X43 @ X40) @ 
% 1.98/2.19               (k6_partfun1 @ X42))
% 1.98/2.19          | ((X41) = (k1_xboole_0))
% 1.98/2.19          | ((X42) = (k1_xboole_0))
% 1.98/2.19          | ~ (v2_funct_1 @ X43)
% 1.98/2.19          | ((k2_relset_1 @ X42 @ X41 @ X43) != (X41))
% 1.98/2.19          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41)))
% 1.98/2.19          | ~ (v1_funct_2 @ X43 @ X42 @ X41)
% 1.98/2.19          | ~ (v1_funct_1 @ X43))),
% 1.98/2.19      inference('cnf', [status(esa)], [t36_funct_2])).
% 1.98/2.19  thf('14', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 1.98/2.19      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.98/2.19  thf('15', plain,
% 1.98/2.19      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 1.98/2.19         (~ (v1_funct_1 @ X40)
% 1.98/2.19          | ~ (v1_funct_2 @ X40 @ X41 @ X42)
% 1.98/2.19          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 1.98/2.19          | ((X40) = (k2_funct_1 @ X43))
% 1.98/2.19          | ~ (r2_relset_1 @ X42 @ X42 @ 
% 1.98/2.19               (k1_partfun1 @ X42 @ X41 @ X41 @ X42 @ X43 @ X40) @ 
% 1.98/2.19               (k6_relat_1 @ X42))
% 1.98/2.19          | ((X41) = (k1_xboole_0))
% 1.98/2.19          | ((X42) = (k1_xboole_0))
% 1.98/2.19          | ~ (v2_funct_1 @ X43)
% 1.98/2.19          | ((k2_relset_1 @ X42 @ X41 @ X43) != (X41))
% 1.98/2.19          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41)))
% 1.98/2.19          | ~ (v1_funct_2 @ X43 @ X42 @ X41)
% 1.98/2.19          | ~ (v1_funct_1 @ X43))),
% 1.98/2.19      inference('demod', [status(thm)], ['13', '14'])).
% 1.98/2.19  thf('16', plain,
% 1.98/2.19      (![X0 : $i]:
% 1.98/2.19         (~ (v1_funct_1 @ X0)
% 1.98/2.19          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 1.98/2.19          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.98/2.19          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 1.98/2.19          | ~ (v2_funct_1 @ X0)
% 1.98/2.19          | ((sk_A) = (k1_xboole_0))
% 1.98/2.19          | ((sk_A) = (k1_xboole_0))
% 1.98/2.19          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.98/2.19               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 1.98/2.19               (k6_relat_1 @ sk_A))
% 1.98/2.19          | ((sk_C) = (k2_funct_1 @ X0))
% 1.98/2.19          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 1.98/2.19          | ~ (v1_funct_1 @ sk_C))),
% 1.98/2.19      inference('sup-', [status(thm)], ['12', '15'])).
% 1.98/2.19  thf('17', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 1.98/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.19  thf('18', plain, ((v1_funct_1 @ sk_C)),
% 1.98/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.19  thf('19', plain,
% 1.98/2.19      (![X0 : $i]:
% 1.98/2.19         (~ (v1_funct_1 @ X0)
% 1.98/2.19          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 1.98/2.19          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.98/2.19          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 1.98/2.19          | ~ (v2_funct_1 @ X0)
% 1.98/2.19          | ((sk_A) = (k1_xboole_0))
% 1.98/2.19          | ((sk_A) = (k1_xboole_0))
% 1.98/2.19          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.98/2.19               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 1.98/2.19               (k6_relat_1 @ sk_A))
% 1.98/2.19          | ((sk_C) = (k2_funct_1 @ X0)))),
% 1.98/2.19      inference('demod', [status(thm)], ['16', '17', '18'])).
% 1.98/2.19  thf('20', plain,
% 1.98/2.19      (![X0 : $i]:
% 1.98/2.19         (((sk_C) = (k2_funct_1 @ X0))
% 1.98/2.19          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.98/2.19               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 1.98/2.19               (k6_relat_1 @ sk_A))
% 1.98/2.19          | ((sk_A) = (k1_xboole_0))
% 1.98/2.19          | ~ (v2_funct_1 @ X0)
% 1.98/2.19          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 1.98/2.19          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.98/2.19          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 1.98/2.19          | ~ (v1_funct_1 @ X0))),
% 1.98/2.19      inference('simplify', [status(thm)], ['19'])).
% 1.98/2.19  thf('21', plain,
% 1.98/2.19      ((~ (v1_funct_1 @ sk_B_1)
% 1.98/2.19        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 1.98/2.19        | ~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.98/2.19        | ((k2_relset_1 @ sk_A @ sk_A @ sk_B_1) != (sk_A))
% 1.98/2.19        | ~ (v2_funct_1 @ sk_B_1)
% 1.98/2.19        | ((sk_A) = (k1_xboole_0))
% 1.98/2.19        | ((sk_C) = (k2_funct_1 @ sk_B_1)))),
% 1.98/2.19      inference('sup-', [status(thm)], ['11', '20'])).
% 1.98/2.19  thf('22', plain, ((v1_funct_1 @ sk_B_1)),
% 1.98/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.19  thf('23', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 1.98/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.19  thf('24', plain,
% 1.98/2.19      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.98/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.19  thf('25', plain,
% 1.98/2.19      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.98/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.19  thf(redefinition_k2_relset_1, axiom,
% 1.98/2.19    (![A:$i,B:$i,C:$i]:
% 1.98/2.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.98/2.19       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.98/2.19  thf('26', plain,
% 1.98/2.19      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.98/2.19         (((k2_relset_1 @ X20 @ X21 @ X19) = (k2_relat_1 @ X19))
% 1.98/2.19          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 1.98/2.19      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.98/2.19  thf('27', plain,
% 1.98/2.19      (((k2_relset_1 @ sk_A @ sk_A @ sk_B_1) = (k2_relat_1 @ sk_B_1))),
% 1.98/2.19      inference('sup-', [status(thm)], ['25', '26'])).
% 1.98/2.19  thf('28', plain,
% 1.98/2.19      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.98/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.19  thf(cc2_funct_2, axiom,
% 1.98/2.19    (![A:$i,B:$i,C:$i]:
% 1.98/2.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.98/2.19       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 1.98/2.19         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 1.98/2.19  thf('29', plain,
% 1.98/2.19      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.98/2.19         (~ (v1_funct_1 @ X26)
% 1.98/2.19          | ~ (v3_funct_2 @ X26 @ X27 @ X28)
% 1.98/2.19          | (v2_funct_2 @ X26 @ X28)
% 1.98/2.19          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 1.98/2.19      inference('cnf', [status(esa)], [cc2_funct_2])).
% 1.98/2.19  thf('30', plain,
% 1.98/2.19      (((v2_funct_2 @ sk_B_1 @ sk_A)
% 1.98/2.19        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 1.98/2.19        | ~ (v1_funct_1 @ sk_B_1))),
% 1.98/2.19      inference('sup-', [status(thm)], ['28', '29'])).
% 1.98/2.19  thf('31', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 1.98/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.19  thf('32', plain, ((v1_funct_1 @ sk_B_1)),
% 1.98/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.19  thf('33', plain, ((v2_funct_2 @ sk_B_1 @ sk_A)),
% 1.98/2.19      inference('demod', [status(thm)], ['30', '31', '32'])).
% 1.98/2.19  thf(d3_funct_2, axiom,
% 1.98/2.19    (![A:$i,B:$i]:
% 1.98/2.19     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 1.98/2.19       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 1.98/2.19  thf('34', plain,
% 1.98/2.19      (![X29 : $i, X30 : $i]:
% 1.98/2.19         (~ (v2_funct_2 @ X30 @ X29)
% 1.98/2.19          | ((k2_relat_1 @ X30) = (X29))
% 1.98/2.19          | ~ (v5_relat_1 @ X30 @ X29)
% 1.98/2.19          | ~ (v1_relat_1 @ X30))),
% 1.98/2.19      inference('cnf', [status(esa)], [d3_funct_2])).
% 1.98/2.19  thf('35', plain,
% 1.98/2.19      ((~ (v1_relat_1 @ sk_B_1)
% 1.98/2.19        | ~ (v5_relat_1 @ sk_B_1 @ sk_A)
% 1.98/2.19        | ((k2_relat_1 @ sk_B_1) = (sk_A)))),
% 1.98/2.19      inference('sup-', [status(thm)], ['33', '34'])).
% 1.98/2.19  thf('36', plain,
% 1.98/2.19      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.98/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.19  thf(cc2_relat_1, axiom,
% 1.98/2.19    (![A:$i]:
% 1.98/2.19     ( ( v1_relat_1 @ A ) =>
% 1.98/2.19       ( ![B:$i]:
% 1.98/2.19         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.98/2.19  thf('37', plain,
% 1.98/2.19      (![X11 : $i, X12 : $i]:
% 1.98/2.19         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 1.98/2.19          | (v1_relat_1 @ X11)
% 1.98/2.19          | ~ (v1_relat_1 @ X12))),
% 1.98/2.19      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.98/2.19  thf('38', plain,
% 1.98/2.19      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B_1))),
% 1.98/2.19      inference('sup-', [status(thm)], ['36', '37'])).
% 1.98/2.19  thf(fc6_relat_1, axiom,
% 1.98/2.19    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.98/2.19  thf('39', plain,
% 1.98/2.19      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X13 @ X14))),
% 1.98/2.19      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.98/2.19  thf('40', plain, ((v1_relat_1 @ sk_B_1)),
% 1.98/2.19      inference('demod', [status(thm)], ['38', '39'])).
% 1.98/2.19  thf('41', plain,
% 1.98/2.19      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.98/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.19  thf(cc2_relset_1, axiom,
% 1.98/2.19    (![A:$i,B:$i,C:$i]:
% 1.98/2.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.98/2.19       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.98/2.19  thf('42', plain,
% 1.98/2.19      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.98/2.19         ((v5_relat_1 @ X16 @ X18)
% 1.98/2.19          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.98/2.19      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.98/2.19  thf('43', plain, ((v5_relat_1 @ sk_B_1 @ sk_A)),
% 1.98/2.19      inference('sup-', [status(thm)], ['41', '42'])).
% 1.98/2.19  thf('44', plain, (((k2_relat_1 @ sk_B_1) = (sk_A))),
% 1.98/2.19      inference('demod', [status(thm)], ['35', '40', '43'])).
% 1.98/2.19  thf('45', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B_1) = (sk_A))),
% 1.98/2.19      inference('demod', [status(thm)], ['27', '44'])).
% 1.98/2.19  thf('46', plain,
% 1.98/2.19      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.98/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.19  thf('47', plain,
% 1.98/2.19      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.98/2.19         (~ (v1_funct_1 @ X26)
% 1.98/2.19          | ~ (v3_funct_2 @ X26 @ X27 @ X28)
% 1.98/2.19          | (v2_funct_1 @ X26)
% 1.98/2.19          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 1.98/2.19      inference('cnf', [status(esa)], [cc2_funct_2])).
% 1.98/2.19  thf('48', plain,
% 1.98/2.19      (((v2_funct_1 @ sk_B_1)
% 1.98/2.19        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 1.98/2.19        | ~ (v1_funct_1 @ sk_B_1))),
% 1.98/2.19      inference('sup-', [status(thm)], ['46', '47'])).
% 1.98/2.19  thf('49', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 1.98/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.19  thf('50', plain, ((v1_funct_1 @ sk_B_1)),
% 1.98/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.19  thf('51', plain, ((v2_funct_1 @ sk_B_1)),
% 1.98/2.19      inference('demod', [status(thm)], ['48', '49', '50'])).
% 1.98/2.19  thf('52', plain,
% 1.98/2.19      ((((sk_A) != (sk_A))
% 1.98/2.19        | ((sk_A) = (k1_xboole_0))
% 1.98/2.19        | ((sk_C) = (k2_funct_1 @ sk_B_1)))),
% 1.98/2.19      inference('demod', [status(thm)], ['21', '22', '23', '24', '45', '51'])).
% 1.98/2.19  thf('53', plain,
% 1.98/2.19      ((((sk_C) = (k2_funct_1 @ sk_B_1)) | ((sk_A) = (k1_xboole_0)))),
% 1.98/2.19      inference('simplify', [status(thm)], ['52'])).
% 1.98/2.19  thf('54', plain,
% 1.98/2.19      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B_1))),
% 1.98/2.19      inference('demod', [status(thm)], ['0', '7'])).
% 1.98/2.19  thf('55', plain,
% 1.98/2.19      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 1.98/2.19      inference('sup-', [status(thm)], ['53', '54'])).
% 1.98/2.19  thf('56', plain,
% 1.98/2.19      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.98/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.19  thf(redefinition_r2_relset_1, axiom,
% 1.98/2.19    (![A:$i,B:$i,C:$i,D:$i]:
% 1.98/2.19     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.98/2.19         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.98/2.19       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.98/2.19  thf('57', plain,
% 1.98/2.19      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 1.98/2.19         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 1.98/2.19          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 1.98/2.19          | (r2_relset_1 @ X23 @ X24 @ X22 @ X25)
% 1.98/2.19          | ((X22) != (X25)))),
% 1.98/2.19      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.98/2.19  thf('58', plain,
% 1.98/2.19      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.98/2.19         ((r2_relset_1 @ X23 @ X24 @ X25 @ X25)
% 1.98/2.19          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 1.98/2.19      inference('simplify', [status(thm)], ['57'])).
% 1.98/2.19  thf('59', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C)),
% 1.98/2.19      inference('sup-', [status(thm)], ['56', '58'])).
% 1.98/2.19  thf('60', plain, (((sk_A) = (k1_xboole_0))),
% 1.98/2.19      inference('demod', [status(thm)], ['55', '59'])).
% 1.98/2.19  thf('61', plain, (((sk_A) = (k1_xboole_0))),
% 1.98/2.19      inference('demod', [status(thm)], ['55', '59'])).
% 1.98/2.19  thf('62', plain,
% 1.98/2.19      (~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ 
% 1.98/2.19          (k2_funct_1 @ sk_B_1))),
% 1.98/2.19      inference('demod', [status(thm)], ['8', '60', '61'])).
% 1.98/2.19  thf(d1_xboole_0, axiom,
% 1.98/2.19    (![A:$i]:
% 1.98/2.19     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.98/2.19  thf('63', plain,
% 1.98/2.19      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.98/2.19      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.98/2.19  thf('64', plain,
% 1.98/2.19      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.98/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.19  thf(t5_subset, axiom,
% 1.98/2.19    (![A:$i,B:$i,C:$i]:
% 1.98/2.19     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 1.98/2.19          ( v1_xboole_0 @ C ) ) ))).
% 1.98/2.19  thf('65', plain,
% 1.98/2.19      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.98/2.19         (~ (r2_hidden @ X8 @ X9)
% 1.98/2.19          | ~ (v1_xboole_0 @ X10)
% 1.98/2.19          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 1.98/2.19      inference('cnf', [status(esa)], [t5_subset])).
% 1.98/2.19  thf('66', plain,
% 1.98/2.19      (![X0 : $i]:
% 1.98/2.19         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 1.98/2.19          | ~ (r2_hidden @ X0 @ sk_C))),
% 1.98/2.19      inference('sup-', [status(thm)], ['64', '65'])).
% 1.98/2.19  thf('67', plain, (((sk_A) = (k1_xboole_0))),
% 1.98/2.19      inference('demod', [status(thm)], ['55', '59'])).
% 1.98/2.19  thf('68', plain, (((sk_A) = (k1_xboole_0))),
% 1.98/2.19      inference('demod', [status(thm)], ['55', '59'])).
% 1.98/2.19  thf(t113_zfmisc_1, axiom,
% 1.98/2.19    (![A:$i,B:$i]:
% 1.98/2.19     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.98/2.19       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.98/2.19  thf('69', plain,
% 1.98/2.19      (![X6 : $i, X7 : $i]:
% 1.98/2.19         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 1.98/2.19      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.98/2.19  thf('70', plain,
% 1.98/2.19      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 1.98/2.19      inference('simplify', [status(thm)], ['69'])).
% 1.98/2.19  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.98/2.19  thf('71', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.98/2.19      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.98/2.19  thf('72', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C)),
% 1.98/2.19      inference('demod', [status(thm)], ['66', '67', '68', '70', '71'])).
% 1.98/2.19  thf('73', plain, ((v1_xboole_0 @ sk_C)),
% 1.98/2.19      inference('sup-', [status(thm)], ['63', '72'])).
% 1.98/2.19  thf('74', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.98/2.19      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.98/2.19  thf(t8_boole, axiom,
% 1.98/2.19    (![A:$i,B:$i]:
% 1.98/2.19     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 1.98/2.19  thf('75', plain,
% 1.98/2.19      (![X3 : $i, X4 : $i]:
% 1.98/2.19         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 1.98/2.19      inference('cnf', [status(esa)], [t8_boole])).
% 1.98/2.19  thf('76', plain,
% 1.98/2.19      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.98/2.19      inference('sup-', [status(thm)], ['74', '75'])).
% 1.98/2.19  thf('77', plain, (((k1_xboole_0) = (sk_C))),
% 1.98/2.19      inference('sup-', [status(thm)], ['73', '76'])).
% 1.98/2.19  thf('78', plain,
% 1.98/2.19      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.98/2.19      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.98/2.19  thf('79', plain,
% 1.98/2.19      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.98/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.98/2.19  thf('80', plain,
% 1.98/2.19      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.98/2.19         (~ (r2_hidden @ X8 @ X9)
% 1.98/2.19          | ~ (v1_xboole_0 @ X10)
% 1.98/2.19          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 1.98/2.19      inference('cnf', [status(esa)], [t5_subset])).
% 1.98/2.19  thf('81', plain,
% 1.98/2.19      (![X0 : $i]:
% 1.98/2.19         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 1.98/2.19          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 1.98/2.19      inference('sup-', [status(thm)], ['79', '80'])).
% 1.98/2.19  thf('82', plain, (((sk_A) = (k1_xboole_0))),
% 1.98/2.19      inference('demod', [status(thm)], ['55', '59'])).
% 1.98/2.19  thf('83', plain, (((sk_A) = (k1_xboole_0))),
% 1.98/2.19      inference('demod', [status(thm)], ['55', '59'])).
% 1.98/2.19  thf('84', plain,
% 1.98/2.19      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 1.98/2.19      inference('simplify', [status(thm)], ['69'])).
% 1.98/2.19  thf('85', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.98/2.19      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.98/2.19  thf('86', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B_1)),
% 1.98/2.19      inference('demod', [status(thm)], ['81', '82', '83', '84', '85'])).
% 1.98/2.19  thf('87', plain, ((v1_xboole_0 @ sk_B_1)),
% 1.98/2.19      inference('sup-', [status(thm)], ['78', '86'])).
% 1.98/2.19  thf('88', plain,
% 1.98/2.19      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.98/2.19      inference('sup-', [status(thm)], ['74', '75'])).
% 1.98/2.19  thf('89', plain, (((k1_xboole_0) = (sk_B_1))),
% 1.98/2.19      inference('sup-', [status(thm)], ['87', '88'])).
% 1.98/2.19  thf('90', plain,
% 1.98/2.19      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.98/2.19      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.98/2.19  thf('91', plain,
% 1.98/2.19      (![X6 : $i, X7 : $i]:
% 1.98/2.19         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 1.98/2.19      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.98/2.19  thf('92', plain,
% 1.98/2.19      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 1.98/2.19      inference('simplify', [status(thm)], ['91'])).
% 1.98/2.19  thf(dt_k6_partfun1, axiom,
% 1.98/2.19    (![A:$i]:
% 1.98/2.19     ( ( m1_subset_1 @
% 1.98/2.19         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 1.98/2.19       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 1.98/2.19  thf('93', plain,
% 1.98/2.19      (![X32 : $i]:
% 1.98/2.19         (m1_subset_1 @ (k6_partfun1 @ X32) @ 
% 1.98/2.19          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))),
% 1.98/2.19      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.98/2.19  thf('94', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 1.98/2.19      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.98/2.19  thf('95', plain,
% 1.98/2.19      (![X32 : $i]:
% 1.98/2.19         (m1_subset_1 @ (k6_relat_1 @ X32) @ 
% 1.98/2.19          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))),
% 1.98/2.19      inference('demod', [status(thm)], ['93', '94'])).
% 1.98/2.19  thf('96', plain,
% 1.98/2.19      ((m1_subset_1 @ (k6_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 1.98/2.19      inference('sup+', [status(thm)], ['92', '95'])).
% 1.98/2.19  thf('97', plain,
% 1.98/2.19      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.98/2.19         (~ (r2_hidden @ X8 @ X9)
% 1.98/2.19          | ~ (v1_xboole_0 @ X10)
% 1.98/2.19          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 1.98/2.19      inference('cnf', [status(esa)], [t5_subset])).
% 1.98/2.19  thf('98', plain,
% 1.98/2.19      (![X0 : $i]:
% 1.98/2.19         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.98/2.19          | ~ (r2_hidden @ X0 @ (k6_relat_1 @ k1_xboole_0)))),
% 1.98/2.19      inference('sup-', [status(thm)], ['96', '97'])).
% 1.98/2.19  thf('99', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.98/2.19      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.98/2.19  thf('100', plain,
% 1.98/2.19      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k6_relat_1 @ k1_xboole_0))),
% 1.98/2.19      inference('demod', [status(thm)], ['98', '99'])).
% 1.98/2.19  thf('101', plain, ((v1_xboole_0 @ (k6_relat_1 @ k1_xboole_0))),
% 1.98/2.19      inference('sup-', [status(thm)], ['90', '100'])).
% 1.98/2.19  thf('102', plain,
% 1.98/2.19      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.98/2.19      inference('sup-', [status(thm)], ['74', '75'])).
% 1.98/2.19  thf('103', plain, (((k1_xboole_0) = (k6_relat_1 @ k1_xboole_0))),
% 1.98/2.19      inference('sup-', [status(thm)], ['101', '102'])).
% 1.98/2.19  thf(t67_funct_1, axiom,
% 1.98/2.19    (![A:$i]: ( ( k2_funct_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 1.98/2.19  thf('104', plain,
% 1.98/2.19      (![X15 : $i]: ((k2_funct_1 @ (k6_relat_1 @ X15)) = (k6_relat_1 @ X15))),
% 1.98/2.19      inference('cnf', [status(esa)], [t67_funct_1])).
% 1.98/2.19  thf('105', plain,
% 1.98/2.19      (((k2_funct_1 @ k1_xboole_0) = (k6_relat_1 @ k1_xboole_0))),
% 1.98/2.19      inference('sup+', [status(thm)], ['103', '104'])).
% 1.98/2.19  thf('106', plain, (((k1_xboole_0) = (k6_relat_1 @ k1_xboole_0))),
% 1.98/2.19      inference('sup-', [status(thm)], ['101', '102'])).
% 1.98/2.19  thf('107', plain, (((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0))),
% 1.98/2.19      inference('sup+', [status(thm)], ['105', '106'])).
% 1.98/2.19  thf('108', plain,
% 1.98/2.19      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 1.98/2.19      inference('simplify', [status(thm)], ['69'])).
% 1.98/2.19  thf('109', plain,
% 1.98/2.19      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.98/2.19      inference('sup-', [status(thm)], ['74', '75'])).
% 1.98/2.19  thf('110', plain,
% 1.98/2.19      ((m1_subset_1 @ (k6_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 1.98/2.19      inference('sup+', [status(thm)], ['92', '95'])).
% 1.98/2.19  thf('111', plain, (((k1_xboole_0) = (k6_relat_1 @ k1_xboole_0))),
% 1.98/2.19      inference('sup-', [status(thm)], ['101', '102'])).
% 1.98/2.19  thf('112', plain,
% 1.98/2.19      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 1.98/2.19      inference('demod', [status(thm)], ['110', '111'])).
% 1.98/2.19  thf('113', plain,
% 1.98/2.19      (![X0 : $i]:
% 1.98/2.19         ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 1.98/2.19          | ~ (v1_xboole_0 @ X0))),
% 1.98/2.19      inference('sup+', [status(thm)], ['109', '112'])).
% 1.98/2.19  thf('114', plain,
% 1.98/2.19      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.98/2.19         ((r2_relset_1 @ X23 @ X24 @ X25 @ X25)
% 1.98/2.19          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 1.98/2.19      inference('simplify', [status(thm)], ['57'])).
% 1.98/2.19  thf('115', plain,
% 1.98/2.19      (![X0 : $i, X1 : $i]:
% 1.98/2.19         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 1.98/2.19          | (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0))),
% 1.98/2.19      inference('sup-', [status(thm)], ['113', '114'])).
% 1.98/2.19  thf('116', plain,
% 1.98/2.19      (![X0 : $i]:
% 1.98/2.19         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.98/2.19          | (r2_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 @ k1_xboole_0))),
% 1.98/2.19      inference('sup-', [status(thm)], ['108', '115'])).
% 1.98/2.19  thf('117', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.98/2.19      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.98/2.19  thf('118', plain,
% 1.98/2.19      (![X0 : $i]: (r2_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 1.98/2.19      inference('demod', [status(thm)], ['116', '117'])).
% 1.98/2.19  thf('119', plain, ($false),
% 1.98/2.19      inference('demod', [status(thm)], ['62', '77', '89', '107', '118'])).
% 1.98/2.19  
% 1.98/2.19  % SZS output end Refutation
% 1.98/2.19  
% 1.98/2.20  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
