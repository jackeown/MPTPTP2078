%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WzARAH3GrF

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:06 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 796 expanded)
%              Number of leaves         :   43 ( 256 expanded)
%              Depth                    :   16
%              Number of atoms          : 1464 (19011 expanded)
%              Number of equality atoms :  122 ( 371 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
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

thf('2',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k2_funct_2 @ X27 @ X26 )
        = ( k2_funct_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X27 ) ) )
      | ~ ( v3_funct_2 @ X26 @ X27 @ X27 )
      | ~ ( v1_funct_2 @ X26 @ X27 @ X27 )
      | ~ ( v1_funct_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_B )
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('8',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('9',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('10',plain,(
    ! [X28: $i] :
      ( ( k6_partfun1 @ X28 )
      = ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('11',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k6_relat_1 @ sk_A ) ),
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
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( X33
        = ( k2_funct_1 @ X36 ) )
      | ~ ( r2_relset_1 @ X35 @ X35 @ ( k1_partfun1 @ X35 @ X34 @ X34 @ X35 @ X36 @ X33 ) @ ( k6_partfun1 @ X35 ) )
      | ( X34 = k1_xboole_0 )
      | ( X35 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X36 )
      | ( ( k2_relset_1 @ X35 @ X34 @ X36 )
       != X34 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X35 @ X34 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t36_funct_2])).

thf('14',plain,(
    ! [X28: $i] :
      ( ( k6_partfun1 @ X28 )
      = ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('15',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( X33
        = ( k2_funct_1 @ X36 ) )
      | ~ ( r2_relset_1 @ X35 @ X35 @ ( k1_partfun1 @ X35 @ X34 @ X34 @ X35 @ X36 @ X33 ) @ ( k6_relat_1 @ X35 ) )
      | ( X34 = k1_xboole_0 )
      | ( X35 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X36 )
      | ( ( k2_relset_1 @ X35 @ X34 @ X36 )
       != X34 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X35 @ X34 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
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
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_B )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','20'])).

thf('22',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('26',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('27',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
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

thf('29',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_1 @ X19 )
      | ~ ( v3_funct_2 @ X19 @ X20 @ X21 )
      | ( v2_funct_2 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('30',plain,
    ( ( v2_funct_2 @ sk_B @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v2_funct_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['30','31','32'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('34',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v2_funct_2 @ X23 @ X22 )
      | ( ( k2_relat_1 @ X23 )
        = X22 )
      | ~ ( v5_relat_1 @ X23 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v5_relat_1 @ sk_B @ sk_A )
    | ( ( k2_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('37',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('38',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('40',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v5_relat_1 @ X9 @ X11 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('41',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['35','38','41'])).

thf('43',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['27','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_1 @ X19 )
      | ~ ( v3_funct_2 @ X19 @ X20 @ X21 )
      | ( v2_funct_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('46',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,
    ( ( sk_A != sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','22','23','24','43','49'])).

thf('51',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('53',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('55',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( r2_relset_1 @ X16 @ X17 @ X15 @ X18 )
      | ( X15 != X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('56',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_relset_1 @ X16 @ X17 @ X18 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['54','56'])).

thf('58',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['53','57'])).

thf('59',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['53','57'])).

thf('60',plain,(
    ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','58','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_1 @ X19 )
      | ~ ( v3_funct_2 @ X19 @ X20 @ X21 )
      | ( v2_funct_2 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('63',plain,
    ( ( v2_funct_2 @ sk_C @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v2_funct_2 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v2_funct_2 @ X23 @ X22 )
      | ( ( k2_relat_1 @ X23 )
        = X22 )
      | ~ ( v5_relat_1 @ X23 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('68',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v5_relat_1 @ sk_C @ sk_A )
    | ( ( k2_relat_1 @ sk_C )
      = sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('71',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v5_relat_1 @ X9 @ X11 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('74',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['68','71','74'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('76',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('77',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['69','70'])).

thf('79',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['53','57'])).

thf('81',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['35','38','41'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('85',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['36','37'])).

thf('87',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['53','57'])).

thf('89',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['89'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('91',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('92',plain,(
    ! [X1: $i] :
      ( ( ( k5_relat_1 @ X1 @ ( k6_relat_1 @ ( k2_relat_1 @ X1 ) ) )
        = X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf(t64_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) )
              & ( ( k5_relat_1 @ B @ A )
                = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) )
           => ( B
              = ( k2_funct_1 @ A ) ) ) ) ) )).

thf('93',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ( X4
        = ( k2_funct_1 @ X5 ) )
      | ( ( k5_relat_1 @ X4 @ X5 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X5 ) ) )
      | ( ( k2_relat_1 @ X4 )
       != ( k1_relat_1 @ X5 ) )
      | ~ ( v2_funct_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( X0
       != ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ( X0
        = ( k2_funct_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('95',plain,(
    ! [X2: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('96',plain,(
    ! [X3: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( X0
       != ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ( X0
        = ( k2_funct_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k2_funct_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
       != ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,
    ( ( k1_xboole_0
     != ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ k1_xboole_0 ) ) ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ ( k6_relat_1 @ ( k2_relat_1 @ k1_xboole_0 ) ) )
    | ( ( k2_relat_1 @ k1_xboole_0 )
     != ( k1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ k1_xboole_0 ) ) ) )
    | ( k1_xboole_0
      = ( k2_funct_1 @ ( k6_relat_1 @ ( k2_relat_1 @ k1_xboole_0 ) ) ) )
    | ~ ( v1_funct_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['91','98'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('100',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('101',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('102',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('103',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('104',plain,(
    ! [X2: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('105',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('107',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('108',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('109',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('110',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('111',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('112',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('113',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('114',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( k1_xboole_0 != k1_xboole_0 )
    | ( k1_xboole_0
      = ( k2_funct_1 @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['99','100','101','102','105','106','107','108','109','110','111','112','113'])).

thf('115',plain,
    ( ( k1_xboole_0
      = ( k2_funct_1 @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['89'])).

thf('118',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( k1_xboole_0
    = ( k2_funct_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['115','118'])).

thf('120',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('121',plain,(
    ! [X25: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('122',plain,(
    ! [X28: $i] :
      ( ( k6_partfun1 @ X28 )
      = ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('123',plain,(
    ! [X25: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['120','123'])).

thf('125',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_relset_1 @ X16 @ X17 @ X18 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('126',plain,(
    r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    $false ),
    inference(demod,[status(thm)],['60','82','90','119','126'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WzARAH3GrF
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:36:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.53  % Solved by: fo/fo7.sh
% 0.35/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.53  % done 170 iterations in 0.074s
% 0.35/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.53  % SZS output start Refutation
% 0.35/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.35/0.53  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.35/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.53  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.35/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.35/0.53  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.35/0.53  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.35/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.53  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.35/0.53  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.35/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.53  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.35/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.35/0.53  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.35/0.53  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.35/0.53  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.35/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.35/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.35/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.35/0.53  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.35/0.53  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.35/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.53  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.35/0.53  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.35/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.35/0.53  thf(t87_funct_2, conjecture,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.35/0.53         ( v3_funct_2 @ B @ A @ A ) & 
% 0.35/0.53         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.35/0.53       ( ![C:$i]:
% 0.35/0.53         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.35/0.53             ( v3_funct_2 @ C @ A @ A ) & 
% 0.35/0.53             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.35/0.53           ( ( r2_relset_1 @
% 0.35/0.53               A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 0.35/0.53               ( k6_partfun1 @ A ) ) =>
% 0.35/0.53             ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ))).
% 0.35/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.53    (~( ![A:$i,B:$i]:
% 0.35/0.53        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.35/0.53            ( v3_funct_2 @ B @ A @ A ) & 
% 0.35/0.53            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.35/0.53          ( ![C:$i]:
% 0.35/0.53            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.35/0.53                ( v3_funct_2 @ C @ A @ A ) & 
% 0.35/0.53                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.35/0.53              ( ( r2_relset_1 @
% 0.35/0.53                  A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 0.35/0.53                  ( k6_partfun1 @ A ) ) =>
% 0.35/0.53                ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ) )),
% 0.35/0.53    inference('cnf.neg', [status(esa)], [t87_funct_2])).
% 0.35/0.53  thf('0', plain,
% 0.35/0.53      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_2 @ sk_A @ sk_B))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('1', plain,
% 0.35/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(redefinition_k2_funct_2, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.35/0.53         ( v3_funct_2 @ B @ A @ A ) & 
% 0.35/0.53         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.35/0.53       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.35/0.53  thf('2', plain,
% 0.35/0.53      (![X26 : $i, X27 : $i]:
% 0.35/0.53         (((k2_funct_2 @ X27 @ X26) = (k2_funct_1 @ X26))
% 0.35/0.53          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X27)))
% 0.35/0.53          | ~ (v3_funct_2 @ X26 @ X27 @ X27)
% 0.35/0.53          | ~ (v1_funct_2 @ X26 @ X27 @ X27)
% 0.35/0.53          | ~ (v1_funct_1 @ X26))),
% 0.35/0.53      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.35/0.53  thf('3', plain,
% 0.35/0.53      ((~ (v1_funct_1 @ sk_B)
% 0.35/0.53        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.35/0.53        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.35/0.53        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.35/0.53  thf('4', plain, ((v1_funct_1 @ sk_B)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('5', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('6', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('7', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.35/0.53      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.35/0.53  thf('8', plain, (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.35/0.53      inference('demod', [status(thm)], ['0', '7'])).
% 0.35/0.53  thf('9', plain,
% 0.35/0.53      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.35/0.53        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 0.35/0.53        (k6_partfun1 @ sk_A))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(redefinition_k6_partfun1, axiom,
% 0.35/0.53    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.35/0.53  thf('10', plain, (![X28 : $i]: ((k6_partfun1 @ X28) = (k6_relat_1 @ X28))),
% 0.35/0.53      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.35/0.53  thf('11', plain,
% 0.35/0.53      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.35/0.53        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 0.35/0.53        (k6_relat_1 @ sk_A))),
% 0.35/0.53      inference('demod', [status(thm)], ['9', '10'])).
% 0.35/0.53  thf('12', plain,
% 0.35/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(t36_funct_2, axiom,
% 0.35/0.53    (![A:$i,B:$i,C:$i]:
% 0.35/0.53     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.35/0.53         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.35/0.53       ( ![D:$i]:
% 0.35/0.53         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.35/0.53             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.35/0.53           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.35/0.53               ( r2_relset_1 @
% 0.35/0.53                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.35/0.53                 ( k6_partfun1 @ A ) ) & 
% 0.35/0.53               ( v2_funct_1 @ C ) ) =>
% 0.35/0.53             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.35/0.53               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.35/0.53  thf('13', plain,
% 0.35/0.53      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.35/0.53         (~ (v1_funct_1 @ X33)
% 0.35/0.53          | ~ (v1_funct_2 @ X33 @ X34 @ X35)
% 0.35/0.53          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.35/0.53          | ((X33) = (k2_funct_1 @ X36))
% 0.35/0.53          | ~ (r2_relset_1 @ X35 @ X35 @ 
% 0.35/0.53               (k1_partfun1 @ X35 @ X34 @ X34 @ X35 @ X36 @ X33) @ 
% 0.35/0.53               (k6_partfun1 @ X35))
% 0.35/0.53          | ((X34) = (k1_xboole_0))
% 0.35/0.53          | ((X35) = (k1_xboole_0))
% 0.35/0.53          | ~ (v2_funct_1 @ X36)
% 0.35/0.53          | ((k2_relset_1 @ X35 @ X34 @ X36) != (X34))
% 0.35/0.53          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 0.35/0.53          | ~ (v1_funct_2 @ X36 @ X35 @ X34)
% 0.35/0.53          | ~ (v1_funct_1 @ X36))),
% 0.35/0.53      inference('cnf', [status(esa)], [t36_funct_2])).
% 0.35/0.53  thf('14', plain, (![X28 : $i]: ((k6_partfun1 @ X28) = (k6_relat_1 @ X28))),
% 0.35/0.53      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.35/0.53  thf('15', plain,
% 0.35/0.53      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.35/0.53         (~ (v1_funct_1 @ X33)
% 0.35/0.53          | ~ (v1_funct_2 @ X33 @ X34 @ X35)
% 0.35/0.53          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.35/0.53          | ((X33) = (k2_funct_1 @ X36))
% 0.35/0.53          | ~ (r2_relset_1 @ X35 @ X35 @ 
% 0.35/0.53               (k1_partfun1 @ X35 @ X34 @ X34 @ X35 @ X36 @ X33) @ 
% 0.35/0.53               (k6_relat_1 @ X35))
% 0.35/0.53          | ((X34) = (k1_xboole_0))
% 0.35/0.53          | ((X35) = (k1_xboole_0))
% 0.35/0.53          | ~ (v2_funct_1 @ X36)
% 0.35/0.53          | ((k2_relset_1 @ X35 @ X34 @ X36) != (X34))
% 0.35/0.53          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 0.35/0.53          | ~ (v1_funct_2 @ X36 @ X35 @ X34)
% 0.35/0.53          | ~ (v1_funct_1 @ X36))),
% 0.35/0.53      inference('demod', [status(thm)], ['13', '14'])).
% 0.35/0.53  thf('16', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         (~ (v1_funct_1 @ X0)
% 0.35/0.53          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.35/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.35/0.53          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.35/0.53          | ~ (v2_funct_1 @ X0)
% 0.35/0.53          | ((sk_A) = (k1_xboole_0))
% 0.35/0.53          | ((sk_A) = (k1_xboole_0))
% 0.35/0.53          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.35/0.53               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.35/0.53               (k6_relat_1 @ sk_A))
% 0.35/0.53          | ((sk_C) = (k2_funct_1 @ X0))
% 0.35/0.53          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.35/0.53          | ~ (v1_funct_1 @ sk_C))),
% 0.35/0.53      inference('sup-', [status(thm)], ['12', '15'])).
% 0.35/0.53  thf('17', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('18', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('19', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         (~ (v1_funct_1 @ X0)
% 0.35/0.53          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.35/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.35/0.53          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.35/0.53          | ~ (v2_funct_1 @ X0)
% 0.35/0.53          | ((sk_A) = (k1_xboole_0))
% 0.35/0.53          | ((sk_A) = (k1_xboole_0))
% 0.35/0.53          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.35/0.53               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.35/0.53               (k6_relat_1 @ sk_A))
% 0.35/0.53          | ((sk_C) = (k2_funct_1 @ X0)))),
% 0.35/0.53      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.35/0.53  thf('20', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         (((sk_C) = (k2_funct_1 @ X0))
% 0.35/0.53          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.35/0.53               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.35/0.53               (k6_relat_1 @ sk_A))
% 0.35/0.53          | ((sk_A) = (k1_xboole_0))
% 0.35/0.53          | ~ (v2_funct_1 @ X0)
% 0.35/0.53          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.35/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.35/0.53          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.35/0.53          | ~ (v1_funct_1 @ X0))),
% 0.35/0.53      inference('simplify', [status(thm)], ['19'])).
% 0.35/0.53  thf('21', plain,
% 0.35/0.53      ((~ (v1_funct_1 @ sk_B)
% 0.35/0.53        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.35/0.53        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.35/0.53        | ((k2_relset_1 @ sk_A @ sk_A @ sk_B) != (sk_A))
% 0.35/0.53        | ~ (v2_funct_1 @ sk_B)
% 0.35/0.53        | ((sk_A) = (k1_xboole_0))
% 0.35/0.53        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['11', '20'])).
% 0.35/0.53  thf('22', plain, ((v1_funct_1 @ sk_B)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('23', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('24', plain,
% 0.35/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('25', plain,
% 0.35/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(redefinition_k2_relset_1, axiom,
% 0.35/0.53    (![A:$i,B:$i,C:$i]:
% 0.35/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.53       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.35/0.53  thf('26', plain,
% 0.35/0.53      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.35/0.53         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 0.35/0.53          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.35/0.53      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.35/0.53  thf('27', plain,
% 0.35/0.53      (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (k2_relat_1 @ sk_B))),
% 0.35/0.53      inference('sup-', [status(thm)], ['25', '26'])).
% 0.35/0.53  thf('28', plain,
% 0.35/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(cc2_funct_2, axiom,
% 0.35/0.53    (![A:$i,B:$i,C:$i]:
% 0.35/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.53       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.35/0.53         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.35/0.53  thf('29', plain,
% 0.35/0.53      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.35/0.53         (~ (v1_funct_1 @ X19)
% 0.35/0.53          | ~ (v3_funct_2 @ X19 @ X20 @ X21)
% 0.35/0.53          | (v2_funct_2 @ X19 @ X21)
% 0.35/0.53          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.35/0.53      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.35/0.53  thf('30', plain,
% 0.35/0.53      (((v2_funct_2 @ sk_B @ sk_A)
% 0.35/0.53        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.35/0.53        | ~ (v1_funct_1 @ sk_B))),
% 0.35/0.53      inference('sup-', [status(thm)], ['28', '29'])).
% 0.35/0.53  thf('31', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('32', plain, ((v1_funct_1 @ sk_B)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('33', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 0.35/0.53      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.35/0.53  thf(d3_funct_2, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.35/0.53       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.35/0.53  thf('34', plain,
% 0.35/0.53      (![X22 : $i, X23 : $i]:
% 0.35/0.53         (~ (v2_funct_2 @ X23 @ X22)
% 0.35/0.53          | ((k2_relat_1 @ X23) = (X22))
% 0.35/0.53          | ~ (v5_relat_1 @ X23 @ X22)
% 0.35/0.53          | ~ (v1_relat_1 @ X23))),
% 0.35/0.53      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.35/0.53  thf('35', plain,
% 0.35/0.53      ((~ (v1_relat_1 @ sk_B)
% 0.35/0.53        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 0.35/0.53        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['33', '34'])).
% 0.35/0.53  thf('36', plain,
% 0.35/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(cc1_relset_1, axiom,
% 0.35/0.53    (![A:$i,B:$i,C:$i]:
% 0.35/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.53       ( v1_relat_1 @ C ) ))).
% 0.35/0.53  thf('37', plain,
% 0.35/0.53      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.35/0.53         ((v1_relat_1 @ X6)
% 0.35/0.53          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.35/0.53      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.35/0.53  thf('38', plain, ((v1_relat_1 @ sk_B)),
% 0.35/0.53      inference('sup-', [status(thm)], ['36', '37'])).
% 0.35/0.53  thf('39', plain,
% 0.35/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(cc2_relset_1, axiom,
% 0.35/0.53    (![A:$i,B:$i,C:$i]:
% 0.35/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.53       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.35/0.53  thf('40', plain,
% 0.35/0.53      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.35/0.53         ((v5_relat_1 @ X9 @ X11)
% 0.35/0.53          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.35/0.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.35/0.53  thf('41', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 0.35/0.53      inference('sup-', [status(thm)], ['39', '40'])).
% 0.35/0.53  thf('42', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.35/0.53      inference('demod', [status(thm)], ['35', '38', '41'])).
% 0.35/0.53  thf('43', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 0.35/0.53      inference('demod', [status(thm)], ['27', '42'])).
% 0.35/0.53  thf('44', plain,
% 0.35/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('45', plain,
% 0.35/0.53      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.35/0.53         (~ (v1_funct_1 @ X19)
% 0.35/0.53          | ~ (v3_funct_2 @ X19 @ X20 @ X21)
% 0.35/0.53          | (v2_funct_1 @ X19)
% 0.35/0.53          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.35/0.53      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.35/0.53  thf('46', plain,
% 0.35/0.53      (((v2_funct_1 @ sk_B)
% 0.35/0.53        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.35/0.53        | ~ (v1_funct_1 @ sk_B))),
% 0.35/0.53      inference('sup-', [status(thm)], ['44', '45'])).
% 0.35/0.53  thf('47', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('48', plain, ((v1_funct_1 @ sk_B)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('49', plain, ((v2_funct_1 @ sk_B)),
% 0.35/0.53      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.35/0.53  thf('50', plain,
% 0.35/0.53      ((((sk_A) != (sk_A))
% 0.35/0.53        | ((sk_A) = (k1_xboole_0))
% 0.35/0.53        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 0.35/0.53      inference('demod', [status(thm)], ['21', '22', '23', '24', '43', '49'])).
% 0.35/0.53  thf('51', plain,
% 0.35/0.53      ((((sk_C) = (k2_funct_1 @ sk_B)) | ((sk_A) = (k1_xboole_0)))),
% 0.35/0.53      inference('simplify', [status(thm)], ['50'])).
% 0.35/0.53  thf('52', plain,
% 0.35/0.53      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.35/0.53      inference('demod', [status(thm)], ['0', '7'])).
% 0.35/0.53  thf('53', plain,
% 0.35/0.53      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['51', '52'])).
% 0.35/0.53  thf('54', plain,
% 0.35/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(redefinition_r2_relset_1, axiom,
% 0.35/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.53     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.35/0.53         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.35/0.53       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.35/0.53  thf('55', plain,
% 0.35/0.53      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.35/0.53         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.35/0.53          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.35/0.53          | (r2_relset_1 @ X16 @ X17 @ X15 @ X18)
% 0.35/0.53          | ((X15) != (X18)))),
% 0.35/0.53      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.35/0.53  thf('56', plain,
% 0.35/0.53      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.35/0.53         ((r2_relset_1 @ X16 @ X17 @ X18 @ X18)
% 0.35/0.53          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.35/0.53      inference('simplify', [status(thm)], ['55'])).
% 0.35/0.53  thf('57', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C)),
% 0.35/0.53      inference('sup-', [status(thm)], ['54', '56'])).
% 0.35/0.53  thf('58', plain, (((sk_A) = (k1_xboole_0))),
% 0.35/0.53      inference('demod', [status(thm)], ['53', '57'])).
% 0.35/0.53  thf('59', plain, (((sk_A) = (k1_xboole_0))),
% 0.35/0.53      inference('demod', [status(thm)], ['53', '57'])).
% 0.35/0.53  thf('60', plain,
% 0.35/0.53      (~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.35/0.53      inference('demod', [status(thm)], ['8', '58', '59'])).
% 0.35/0.53  thf('61', plain,
% 0.35/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('62', plain,
% 0.35/0.53      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.35/0.53         (~ (v1_funct_1 @ X19)
% 0.35/0.53          | ~ (v3_funct_2 @ X19 @ X20 @ X21)
% 0.35/0.53          | (v2_funct_2 @ X19 @ X21)
% 0.35/0.53          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.35/0.53      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.35/0.53  thf('63', plain,
% 0.35/0.53      (((v2_funct_2 @ sk_C @ sk_A)
% 0.35/0.53        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.35/0.53        | ~ (v1_funct_1 @ sk_C))),
% 0.35/0.53      inference('sup-', [status(thm)], ['61', '62'])).
% 0.35/0.53  thf('64', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('65', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('66', plain, ((v2_funct_2 @ sk_C @ sk_A)),
% 0.35/0.53      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.35/0.53  thf('67', plain,
% 0.35/0.53      (![X22 : $i, X23 : $i]:
% 0.35/0.53         (~ (v2_funct_2 @ X23 @ X22)
% 0.35/0.53          | ((k2_relat_1 @ X23) = (X22))
% 0.35/0.53          | ~ (v5_relat_1 @ X23 @ X22)
% 0.35/0.53          | ~ (v1_relat_1 @ X23))),
% 0.35/0.53      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.35/0.53  thf('68', plain,
% 0.35/0.53      ((~ (v1_relat_1 @ sk_C)
% 0.35/0.53        | ~ (v5_relat_1 @ sk_C @ sk_A)
% 0.35/0.53        | ((k2_relat_1 @ sk_C) = (sk_A)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['66', '67'])).
% 0.35/0.53  thf('69', plain,
% 0.35/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('70', plain,
% 0.35/0.53      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.35/0.53         ((v1_relat_1 @ X6)
% 0.35/0.53          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.35/0.53      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.35/0.53  thf('71', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.53      inference('sup-', [status(thm)], ['69', '70'])).
% 0.35/0.53  thf('72', plain,
% 0.35/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('73', plain,
% 0.35/0.53      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.35/0.53         ((v5_relat_1 @ X9 @ X11)
% 0.35/0.53          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.35/0.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.35/0.53  thf('74', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.35/0.53      inference('sup-', [status(thm)], ['72', '73'])).
% 0.35/0.53  thf('75', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.35/0.53      inference('demod', [status(thm)], ['68', '71', '74'])).
% 0.35/0.53  thf(t64_relat_1, axiom,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( v1_relat_1 @ A ) =>
% 0.35/0.53       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.35/0.53           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.35/0.53         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.35/0.53  thf('76', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 0.35/0.53          | ((X0) = (k1_xboole_0))
% 0.35/0.53          | ~ (v1_relat_1 @ X0))),
% 0.35/0.53      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.35/0.53  thf('77', plain,
% 0.35/0.53      ((((sk_A) != (k1_xboole_0))
% 0.35/0.53        | ~ (v1_relat_1 @ sk_C)
% 0.35/0.53        | ((sk_C) = (k1_xboole_0)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['75', '76'])).
% 0.35/0.53  thf('78', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.53      inference('sup-', [status(thm)], ['69', '70'])).
% 0.35/0.53  thf('79', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.35/0.53      inference('demod', [status(thm)], ['77', '78'])).
% 0.35/0.53  thf('80', plain, (((sk_A) = (k1_xboole_0))),
% 0.35/0.53      inference('demod', [status(thm)], ['53', '57'])).
% 0.35/0.53  thf('81', plain,
% 0.35/0.53      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.35/0.53      inference('demod', [status(thm)], ['79', '80'])).
% 0.35/0.53  thf('82', plain, (((sk_C) = (k1_xboole_0))),
% 0.35/0.53      inference('simplify', [status(thm)], ['81'])).
% 0.35/0.53  thf('83', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.35/0.53      inference('demod', [status(thm)], ['35', '38', '41'])).
% 0.35/0.53  thf('84', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 0.35/0.53          | ((X0) = (k1_xboole_0))
% 0.35/0.53          | ~ (v1_relat_1 @ X0))),
% 0.35/0.53      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.35/0.53  thf('85', plain,
% 0.35/0.53      ((((sk_A) != (k1_xboole_0))
% 0.35/0.53        | ~ (v1_relat_1 @ sk_B)
% 0.35/0.53        | ((sk_B) = (k1_xboole_0)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['83', '84'])).
% 0.35/0.53  thf('86', plain, ((v1_relat_1 @ sk_B)),
% 0.35/0.53      inference('sup-', [status(thm)], ['36', '37'])).
% 0.35/0.53  thf('87', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.35/0.53      inference('demod', [status(thm)], ['85', '86'])).
% 0.35/0.53  thf('88', plain, (((sk_A) = (k1_xboole_0))),
% 0.35/0.53      inference('demod', [status(thm)], ['53', '57'])).
% 0.35/0.53  thf('89', plain,
% 0.35/0.53      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.35/0.53      inference('demod', [status(thm)], ['87', '88'])).
% 0.35/0.53  thf('90', plain, (((sk_B) = (k1_xboole_0))),
% 0.35/0.53      inference('simplify', [status(thm)], ['89'])).
% 0.35/0.53  thf(t60_relat_1, axiom,
% 0.35/0.53    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.35/0.53     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.35/0.53  thf('91', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.35/0.53      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.35/0.53  thf(t80_relat_1, axiom,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( v1_relat_1 @ A ) =>
% 0.35/0.53       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.35/0.53  thf('92', plain,
% 0.35/0.53      (![X1 : $i]:
% 0.35/0.53         (((k5_relat_1 @ X1 @ (k6_relat_1 @ (k2_relat_1 @ X1))) = (X1))
% 0.35/0.53          | ~ (v1_relat_1 @ X1))),
% 0.35/0.53      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.35/0.53  thf(t64_funct_1, axiom,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.35/0.53       ( ![B:$i]:
% 0.35/0.53         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.35/0.53           ( ( ( v2_funct_1 @ A ) & 
% 0.35/0.53               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.35/0.53               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.35/0.53             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.35/0.53  thf('93', plain,
% 0.35/0.53      (![X4 : $i, X5 : $i]:
% 0.35/0.53         (~ (v1_relat_1 @ X4)
% 0.35/0.53          | ~ (v1_funct_1 @ X4)
% 0.35/0.53          | ((X4) = (k2_funct_1 @ X5))
% 0.35/0.53          | ((k5_relat_1 @ X4 @ X5) != (k6_relat_1 @ (k2_relat_1 @ X5)))
% 0.35/0.53          | ((k2_relat_1 @ X4) != (k1_relat_1 @ X5))
% 0.35/0.53          | ~ (v2_funct_1 @ X5)
% 0.35/0.53          | ~ (v1_funct_1 @ X5)
% 0.35/0.53          | ~ (v1_relat_1 @ X5))),
% 0.35/0.53      inference('cnf', [status(esa)], [t64_funct_1])).
% 0.35/0.53  thf('94', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         (((X0)
% 0.35/0.53            != (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)))))
% 0.35/0.53          | ~ (v1_relat_1 @ X0)
% 0.35/0.53          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.35/0.53          | ~ (v1_funct_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.35/0.53          | ~ (v2_funct_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.35/0.53          | ((k2_relat_1 @ X0)
% 0.35/0.53              != (k1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))
% 0.35/0.53          | ((X0) = (k2_funct_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))
% 0.35/0.53          | ~ (v1_funct_1 @ X0)
% 0.35/0.53          | ~ (v1_relat_1 @ X0))),
% 0.35/0.53      inference('sup-', [status(thm)], ['92', '93'])).
% 0.35/0.53  thf(fc4_funct_1, axiom,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.35/0.53       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.35/0.53  thf('95', plain, (![X2 : $i]: (v1_relat_1 @ (k6_relat_1 @ X2))),
% 0.35/0.53      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.35/0.53  thf('96', plain, (![X3 : $i]: (v2_funct_1 @ (k6_relat_1 @ X3))),
% 0.35/0.53      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.35/0.53  thf('97', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         (((X0)
% 0.35/0.53            != (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)))))
% 0.35/0.53          | ~ (v1_relat_1 @ X0)
% 0.35/0.53          | ~ (v1_funct_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.35/0.53          | ((k2_relat_1 @ X0)
% 0.35/0.53              != (k1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))
% 0.35/0.53          | ((X0) = (k2_funct_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))
% 0.35/0.53          | ~ (v1_funct_1 @ X0)
% 0.35/0.53          | ~ (v1_relat_1 @ X0))),
% 0.35/0.53      inference('demod', [status(thm)], ['94', '95', '96'])).
% 0.35/0.53  thf('98', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         (~ (v1_funct_1 @ X0)
% 0.35/0.53          | ((X0) = (k2_funct_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))
% 0.35/0.53          | ((k2_relat_1 @ X0)
% 0.35/0.53              != (k1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))
% 0.35/0.53          | ~ (v1_funct_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.35/0.53          | ~ (v1_relat_1 @ X0)
% 0.35/0.53          | ((X0)
% 0.35/0.53              != (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))))),
% 0.35/0.53      inference('simplify', [status(thm)], ['97'])).
% 0.35/0.53  thf('99', plain,
% 0.35/0.53      ((((k1_xboole_0)
% 0.35/0.53          != (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ k1_xboole_0))))
% 0.35/0.53        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.35/0.53        | ~ (v1_funct_1 @ (k6_relat_1 @ (k2_relat_1 @ k1_xboole_0)))
% 0.35/0.53        | ((k2_relat_1 @ k1_xboole_0)
% 0.35/0.53            != (k1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ k1_xboole_0))))
% 0.35/0.53        | ((k1_xboole_0)
% 0.35/0.53            = (k2_funct_1 @ (k6_relat_1 @ (k2_relat_1 @ k1_xboole_0))))
% 0.35/0.53        | ~ (v1_funct_1 @ k1_xboole_0))),
% 0.35/0.53      inference('sup-', [status(thm)], ['91', '98'])).
% 0.35/0.53  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.35/0.53  thf('100', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.35/0.53      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.35/0.53  thf('101', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.35/0.53      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.35/0.53  thf('102', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.35/0.53      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.35/0.53  thf('103', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.35/0.53      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.35/0.53  thf('104', plain, (![X2 : $i]: (v1_relat_1 @ (k6_relat_1 @ X2))),
% 0.35/0.53      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.35/0.53  thf('105', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.35/0.53      inference('sup+', [status(thm)], ['103', '104'])).
% 0.35/0.53  thf('106', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.35/0.53      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.35/0.53  thf('107', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.35/0.53      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.35/0.53  thf('108', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.35/0.53      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.35/0.53  thf('109', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.35/0.53      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.35/0.53  thf('110', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.35/0.53      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.35/0.53  thf('111', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.35/0.53      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.35/0.53  thf('112', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.35/0.53      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.35/0.53  thf('113', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.35/0.53      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.35/0.53  thf('114', plain,
% 0.35/0.53      ((((k1_xboole_0) != (k1_xboole_0))
% 0.35/0.53        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.35/0.53        | ((k1_xboole_0) != (k1_xboole_0))
% 0.35/0.53        | ((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0))
% 0.35/0.53        | ~ (v1_funct_1 @ k1_xboole_0))),
% 0.35/0.53      inference('demod', [status(thm)],
% 0.35/0.53                ['99', '100', '101', '102', '105', '106', '107', '108', '109', 
% 0.35/0.53                 '110', '111', '112', '113'])).
% 0.35/0.53  thf('115', plain,
% 0.35/0.53      ((((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0))
% 0.35/0.53        | ~ (v1_funct_1 @ k1_xboole_0))),
% 0.35/0.53      inference('simplify', [status(thm)], ['114'])).
% 0.35/0.53  thf('116', plain, ((v1_funct_1 @ sk_B)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('117', plain, (((sk_B) = (k1_xboole_0))),
% 0.35/0.53      inference('simplify', [status(thm)], ['89'])).
% 0.35/0.53  thf('118', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.35/0.53      inference('demod', [status(thm)], ['116', '117'])).
% 0.35/0.53  thf('119', plain, (((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0))),
% 0.35/0.53      inference('demod', [status(thm)], ['115', '118'])).
% 0.35/0.53  thf('120', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.35/0.53      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.35/0.53  thf(dt_k6_partfun1, axiom,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( m1_subset_1 @
% 0.35/0.53         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.35/0.53       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.35/0.53  thf('121', plain,
% 0.35/0.53      (![X25 : $i]:
% 0.35/0.53         (m1_subset_1 @ (k6_partfun1 @ X25) @ 
% 0.35/0.53          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X25)))),
% 0.35/0.53      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.35/0.53  thf('122', plain, (![X28 : $i]: ((k6_partfun1 @ X28) = (k6_relat_1 @ X28))),
% 0.35/0.53      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.35/0.53  thf('123', plain,
% 0.35/0.53      (![X25 : $i]:
% 0.35/0.53         (m1_subset_1 @ (k6_relat_1 @ X25) @ 
% 0.35/0.53          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X25)))),
% 0.35/0.53      inference('demod', [status(thm)], ['121', '122'])).
% 0.35/0.53  thf('124', plain,
% 0.35/0.53      ((m1_subset_1 @ k1_xboole_0 @ 
% 0.35/0.53        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.35/0.53      inference('sup+', [status(thm)], ['120', '123'])).
% 0.35/0.53  thf('125', plain,
% 0.35/0.53      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.35/0.53         ((r2_relset_1 @ X16 @ X17 @ X18 @ X18)
% 0.35/0.53          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.35/0.53      inference('simplify', [status(thm)], ['55'])).
% 0.35/0.53  thf('126', plain,
% 0.35/0.53      ((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.35/0.53      inference('sup-', [status(thm)], ['124', '125'])).
% 0.35/0.53  thf('127', plain, ($false),
% 0.35/0.53      inference('demod', [status(thm)], ['60', '82', '90', '119', '126'])).
% 0.35/0.53  
% 0.35/0.53  % SZS output end Refutation
% 0.35/0.53  
% 0.38/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
