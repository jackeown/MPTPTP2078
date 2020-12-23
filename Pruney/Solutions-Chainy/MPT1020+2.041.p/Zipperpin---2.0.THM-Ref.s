%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Te4RzBk31K

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:07 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 620 expanded)
%              Number of leaves         :   39 ( 199 expanded)
%              Depth                    :   14
%              Number of atoms          : 1192 (14609 expanded)
%              Number of equality atoms :   95 ( 275 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X25: $i,X26: $i] :
      ( ( ( k2_funct_2 @ X26 @ X25 )
        = ( k2_funct_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X26 ) ) )
      | ~ ( v3_funct_2 @ X25 @ X26 @ X26 )
      | ~ ( v1_funct_2 @ X25 @ X26 @ X26 )
      | ~ ( v1_funct_1 @ X25 ) ) ),
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

thf('10',plain,(
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

thf('11',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( X32
        = ( k2_funct_1 @ X35 ) )
      | ~ ( r2_relset_1 @ X34 @ X34 @ ( k1_partfun1 @ X34 @ X33 @ X33 @ X34 @ X35 @ X32 ) @ ( k6_partfun1 @ X34 ) )
      | ( X33 = k1_xboole_0 )
      | ( X34 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X35 )
      | ( ( k2_relset_1 @ X34 @ X33 @ X35 )
       != X33 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X34 @ X33 )
      | ~ ( v1_funct_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t36_funct_2])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( v2_funct_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      | ( sk_C
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( v2_funct_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      | ( sk_C
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( sk_C
        = ( k2_funct_1 @ X0 ) )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      | ( sk_A = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_B )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('22',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('23',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
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

thf('25',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_funct_1 @ X20 )
      | ~ ( v3_funct_2 @ X20 @ X21 @ X22 )
      | ( v2_funct_2 @ X20 @ X22 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('26',plain,
    ( ( v2_funct_2 @ sk_B @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v2_funct_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['26','27','28'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('30',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v2_funct_2 @ X24 @ X23 )
      | ( ( k2_relat_1 @ X24 )
        = X23 )
      | ~ ( v5_relat_1 @ X24 @ X23 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v5_relat_1 @ sk_B @ sk_A )
    | ( ( k2_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('33',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('34',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('36',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v5_relat_1 @ X9 @ X11 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('37',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['31','34','37'])).

thf('39',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['23','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_funct_1 @ X20 )
      | ~ ( v3_funct_2 @ X20 @ X21 @ X22 )
      | ( v2_funct_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('42',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,
    ( ( sk_A != sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18','19','20','39','45'])).

thf('47',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('49',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('51',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( r2_relset_1 @ X16 @ X17 @ X15 @ X18 )
      | ( X15 != X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('52',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_relset_1 @ X16 @ X17 @ X18 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','53'])).

thf('55',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','53'])).

thf('56',plain,(
    ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_funct_1 @ X20 )
      | ~ ( v3_funct_2 @ X20 @ X21 @ X22 )
      | ( v2_funct_2 @ X20 @ X22 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('59',plain,
    ( ( v2_funct_2 @ sk_C @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v2_funct_2 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v2_funct_2 @ X24 @ X23 )
      | ( ( k2_relat_1 @ X24 )
        = X23 )
      | ~ ( v5_relat_1 @ X24 @ X23 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('64',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v5_relat_1 @ sk_C @ sk_A )
    | ( ( k2_relat_1 @ sk_C )
      = sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('67',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v5_relat_1 @ X9 @ X11 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('70',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['64','67','70'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('72',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('73',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['65','66'])).

thf('75',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','53'])).

thf('77',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['31','34','37'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('81',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['32','33'])).

thf('83',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','53'])).

thf('85',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['85'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('87',plain,(
    ! [X1: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X1 ) )
      = X1 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('88',plain,(
    ! [X27: $i] :
      ( ( k6_partfun1 @ X27 )
      = ( k6_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('89',plain,(
    ! [X1: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ( ( k6_partfun1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('92',plain,(
    ! [X3: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('93',plain,(
    ! [X27: $i] :
      ( ( k6_partfun1 @ X27 )
      = ( k6_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('94',plain,(
    ! [X3: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X3 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( k6_partfun1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['91','94'])).

thf('96',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['95'])).

thf(t67_funct_1,axiom,(
    ! [A: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('97',plain,(
    ! [X5: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ X5 ) )
      = ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_1])).

thf('98',plain,(
    ! [X27: $i] :
      ( ( k6_partfun1 @ X27 )
      = ( k6_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('99',plain,(
    ! [X27: $i] :
      ( ( k6_partfun1 @ X27 )
      = ( k6_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('100',plain,(
    ! [X5: $i] :
      ( ( k2_funct_1 @ ( k6_partfun1 @ X5 ) )
      = ( k6_partfun1 @ X5 ) ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = ( k6_partfun1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['96','100'])).

thf('102',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['95'])).

thf('103',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['95'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('105',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('106',plain,(
    ! [X27: $i] :
      ( ( k6_partfun1 @ X27 )
      = ( k6_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('107',plain,(
    ! [X19: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['104','107'])).

thf('109',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_relset_1 @ X16 @ X17 @ X18 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('110',plain,(
    r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    $false ),
    inference(demod,[status(thm)],['56','78','86','103','110'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Te4RzBk31K
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:53:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.35/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.52  % Solved by: fo/fo7.sh
% 0.35/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.52  % done 129 iterations in 0.063s
% 0.35/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.52  % SZS output start Refutation
% 0.35/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.52  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.35/0.52  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.35/0.52  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.35/0.52  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.35/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.35/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.35/0.52  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.35/0.52  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.35/0.52  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.35/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.35/0.52  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.35/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.35/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.35/0.52  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.35/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.35/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.52  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.35/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.52  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.35/0.52  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.35/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.35/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.52  thf(t87_funct_2, conjecture,
% 0.35/0.52    (![A:$i,B:$i]:
% 0.35/0.52     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.35/0.52         ( v3_funct_2 @ B @ A @ A ) & 
% 0.35/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.35/0.52       ( ![C:$i]:
% 0.35/0.52         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.35/0.52             ( v3_funct_2 @ C @ A @ A ) & 
% 0.35/0.52             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.35/0.52           ( ( r2_relset_1 @
% 0.35/0.52               A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 0.35/0.52               ( k6_partfun1 @ A ) ) =>
% 0.35/0.52             ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ))).
% 0.35/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.52    (~( ![A:$i,B:$i]:
% 0.35/0.52        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.35/0.52            ( v3_funct_2 @ B @ A @ A ) & 
% 0.35/0.52            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.35/0.52          ( ![C:$i]:
% 0.35/0.52            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.35/0.52                ( v3_funct_2 @ C @ A @ A ) & 
% 0.35/0.52                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.35/0.52              ( ( r2_relset_1 @
% 0.35/0.52                  A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 0.35/0.52                  ( k6_partfun1 @ A ) ) =>
% 0.35/0.52                ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ) )),
% 0.35/0.52    inference('cnf.neg', [status(esa)], [t87_funct_2])).
% 0.35/0.52  thf('0', plain,
% 0.35/0.52      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_2 @ sk_A @ sk_B))),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('1', plain,
% 0.35/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf(redefinition_k2_funct_2, axiom,
% 0.35/0.52    (![A:$i,B:$i]:
% 0.35/0.52     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.35/0.52         ( v3_funct_2 @ B @ A @ A ) & 
% 0.35/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.35/0.52       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.35/0.52  thf('2', plain,
% 0.35/0.52      (![X25 : $i, X26 : $i]:
% 0.35/0.52         (((k2_funct_2 @ X26 @ X25) = (k2_funct_1 @ X25))
% 0.35/0.52          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X26)))
% 0.35/0.52          | ~ (v3_funct_2 @ X25 @ X26 @ X26)
% 0.35/0.52          | ~ (v1_funct_2 @ X25 @ X26 @ X26)
% 0.35/0.52          | ~ (v1_funct_1 @ X25))),
% 0.35/0.52      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.35/0.52  thf('3', plain,
% 0.35/0.52      ((~ (v1_funct_1 @ sk_B)
% 0.35/0.52        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.35/0.52        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.35/0.52        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 0.35/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.35/0.52  thf('4', plain, ((v1_funct_1 @ sk_B)),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('5', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('6', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('7', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.35/0.52      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.35/0.52  thf('8', plain, (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.35/0.52      inference('demod', [status(thm)], ['0', '7'])).
% 0.35/0.52  thf('9', plain,
% 0.35/0.52      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.35/0.52        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 0.35/0.52        (k6_partfun1 @ sk_A))),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('10', plain,
% 0.35/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf(t36_funct_2, axiom,
% 0.35/0.52    (![A:$i,B:$i,C:$i]:
% 0.35/0.52     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.35/0.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.35/0.52       ( ![D:$i]:
% 0.35/0.52         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.35/0.52             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.35/0.52           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.35/0.52               ( r2_relset_1 @
% 0.35/0.52                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.35/0.52                 ( k6_partfun1 @ A ) ) & 
% 0.35/0.52               ( v2_funct_1 @ C ) ) =>
% 0.35/0.52             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.35/0.52               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.35/0.52  thf('11', plain,
% 0.35/0.52      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.35/0.52         (~ (v1_funct_1 @ X32)
% 0.35/0.52          | ~ (v1_funct_2 @ X32 @ X33 @ X34)
% 0.35/0.52          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.35/0.52          | ((X32) = (k2_funct_1 @ X35))
% 0.35/0.52          | ~ (r2_relset_1 @ X34 @ X34 @ 
% 0.35/0.52               (k1_partfun1 @ X34 @ X33 @ X33 @ X34 @ X35 @ X32) @ 
% 0.35/0.52               (k6_partfun1 @ X34))
% 0.35/0.52          | ((X33) = (k1_xboole_0))
% 0.35/0.52          | ((X34) = (k1_xboole_0))
% 0.35/0.52          | ~ (v2_funct_1 @ X35)
% 0.35/0.52          | ((k2_relset_1 @ X34 @ X33 @ X35) != (X33))
% 0.35/0.52          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.35/0.52          | ~ (v1_funct_2 @ X35 @ X34 @ X33)
% 0.35/0.52          | ~ (v1_funct_1 @ X35))),
% 0.35/0.52      inference('cnf', [status(esa)], [t36_funct_2])).
% 0.35/0.52  thf('12', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         (~ (v1_funct_1 @ X0)
% 0.35/0.52          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.35/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.35/0.52          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.35/0.52          | ~ (v2_funct_1 @ X0)
% 0.35/0.52          | ((sk_A) = (k1_xboole_0))
% 0.35/0.52          | ((sk_A) = (k1_xboole_0))
% 0.35/0.52          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.35/0.52               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.35/0.52               (k6_partfun1 @ sk_A))
% 0.35/0.52          | ((sk_C) = (k2_funct_1 @ X0))
% 0.35/0.52          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.35/0.52          | ~ (v1_funct_1 @ sk_C))),
% 0.35/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.35/0.52  thf('13', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('14', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('15', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         (~ (v1_funct_1 @ X0)
% 0.35/0.52          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.35/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.35/0.52          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.35/0.52          | ~ (v2_funct_1 @ X0)
% 0.35/0.52          | ((sk_A) = (k1_xboole_0))
% 0.35/0.52          | ((sk_A) = (k1_xboole_0))
% 0.35/0.52          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.35/0.52               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.35/0.52               (k6_partfun1 @ sk_A))
% 0.35/0.52          | ((sk_C) = (k2_funct_1 @ X0)))),
% 0.35/0.52      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.35/0.52  thf('16', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         (((sk_C) = (k2_funct_1 @ X0))
% 0.35/0.52          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.35/0.52               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 0.35/0.52               (k6_partfun1 @ sk_A))
% 0.35/0.52          | ((sk_A) = (k1_xboole_0))
% 0.35/0.52          | ~ (v2_funct_1 @ X0)
% 0.35/0.52          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 0.35/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.35/0.52          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.35/0.52          | ~ (v1_funct_1 @ X0))),
% 0.35/0.52      inference('simplify', [status(thm)], ['15'])).
% 0.35/0.52  thf('17', plain,
% 0.35/0.52      ((~ (v1_funct_1 @ sk_B)
% 0.35/0.52        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.35/0.52        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.35/0.52        | ((k2_relset_1 @ sk_A @ sk_A @ sk_B) != (sk_A))
% 0.35/0.52        | ~ (v2_funct_1 @ sk_B)
% 0.35/0.52        | ((sk_A) = (k1_xboole_0))
% 0.35/0.52        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 0.35/0.52      inference('sup-', [status(thm)], ['9', '16'])).
% 0.35/0.52  thf('18', plain, ((v1_funct_1 @ sk_B)),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('19', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('20', plain,
% 0.35/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('21', plain,
% 0.35/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf(redefinition_k2_relset_1, axiom,
% 0.35/0.52    (![A:$i,B:$i,C:$i]:
% 0.35/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.52       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.35/0.52  thf('22', plain,
% 0.35/0.52      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.35/0.52         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 0.35/0.52          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.35/0.52      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.35/0.52  thf('23', plain,
% 0.35/0.52      (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (k2_relat_1 @ sk_B))),
% 0.35/0.52      inference('sup-', [status(thm)], ['21', '22'])).
% 0.35/0.52  thf('24', plain,
% 0.35/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf(cc2_funct_2, axiom,
% 0.35/0.52    (![A:$i,B:$i,C:$i]:
% 0.35/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.52       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.35/0.52         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.35/0.52  thf('25', plain,
% 0.35/0.52      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.35/0.52         (~ (v1_funct_1 @ X20)
% 0.35/0.52          | ~ (v3_funct_2 @ X20 @ X21 @ X22)
% 0.35/0.52          | (v2_funct_2 @ X20 @ X22)
% 0.35/0.52          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.35/0.52      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.35/0.52  thf('26', plain,
% 0.35/0.52      (((v2_funct_2 @ sk_B @ sk_A)
% 0.35/0.52        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.35/0.52        | ~ (v1_funct_1 @ sk_B))),
% 0.35/0.52      inference('sup-', [status(thm)], ['24', '25'])).
% 0.35/0.52  thf('27', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('28', plain, ((v1_funct_1 @ sk_B)),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('29', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 0.35/0.52      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.35/0.52  thf(d3_funct_2, axiom,
% 0.35/0.52    (![A:$i,B:$i]:
% 0.35/0.52     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.35/0.52       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.35/0.52  thf('30', plain,
% 0.35/0.52      (![X23 : $i, X24 : $i]:
% 0.35/0.52         (~ (v2_funct_2 @ X24 @ X23)
% 0.35/0.52          | ((k2_relat_1 @ X24) = (X23))
% 0.35/0.52          | ~ (v5_relat_1 @ X24 @ X23)
% 0.35/0.52          | ~ (v1_relat_1 @ X24))),
% 0.35/0.52      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.35/0.52  thf('31', plain,
% 0.35/0.52      ((~ (v1_relat_1 @ sk_B)
% 0.35/0.52        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 0.35/0.52        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 0.35/0.52      inference('sup-', [status(thm)], ['29', '30'])).
% 0.35/0.52  thf('32', plain,
% 0.35/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf(cc1_relset_1, axiom,
% 0.35/0.52    (![A:$i,B:$i,C:$i]:
% 0.35/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.52       ( v1_relat_1 @ C ) ))).
% 0.35/0.52  thf('33', plain,
% 0.35/0.52      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.35/0.52         ((v1_relat_1 @ X6)
% 0.35/0.52          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.35/0.52      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.35/0.52  thf('34', plain, ((v1_relat_1 @ sk_B)),
% 0.35/0.52      inference('sup-', [status(thm)], ['32', '33'])).
% 0.35/0.52  thf('35', plain,
% 0.35/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf(cc2_relset_1, axiom,
% 0.35/0.52    (![A:$i,B:$i,C:$i]:
% 0.35/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.52       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.35/0.52  thf('36', plain,
% 0.35/0.52      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.35/0.52         ((v5_relat_1 @ X9 @ X11)
% 0.35/0.52          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.35/0.52      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.35/0.52  thf('37', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 0.35/0.52      inference('sup-', [status(thm)], ['35', '36'])).
% 0.35/0.52  thf('38', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.35/0.52      inference('demod', [status(thm)], ['31', '34', '37'])).
% 0.35/0.52  thf('39', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 0.35/0.52      inference('demod', [status(thm)], ['23', '38'])).
% 0.35/0.52  thf('40', plain,
% 0.35/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('41', plain,
% 0.35/0.52      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.35/0.52         (~ (v1_funct_1 @ X20)
% 0.35/0.52          | ~ (v3_funct_2 @ X20 @ X21 @ X22)
% 0.35/0.52          | (v2_funct_1 @ X20)
% 0.35/0.52          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.35/0.52      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.35/0.52  thf('42', plain,
% 0.35/0.52      (((v2_funct_1 @ sk_B)
% 0.35/0.52        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.35/0.52        | ~ (v1_funct_1 @ sk_B))),
% 0.35/0.52      inference('sup-', [status(thm)], ['40', '41'])).
% 0.35/0.52  thf('43', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('44', plain, ((v1_funct_1 @ sk_B)),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('45', plain, ((v2_funct_1 @ sk_B)),
% 0.35/0.52      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.35/0.52  thf('46', plain,
% 0.35/0.52      ((((sk_A) != (sk_A))
% 0.35/0.52        | ((sk_A) = (k1_xboole_0))
% 0.35/0.52        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 0.35/0.52      inference('demod', [status(thm)], ['17', '18', '19', '20', '39', '45'])).
% 0.35/0.52  thf('47', plain,
% 0.35/0.52      ((((sk_C) = (k2_funct_1 @ sk_B)) | ((sk_A) = (k1_xboole_0)))),
% 0.35/0.52      inference('simplify', [status(thm)], ['46'])).
% 0.35/0.52  thf('48', plain,
% 0.35/0.52      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.35/0.52      inference('demod', [status(thm)], ['0', '7'])).
% 0.35/0.52  thf('49', plain,
% 0.35/0.52      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.35/0.52      inference('sup-', [status(thm)], ['47', '48'])).
% 0.35/0.52  thf('50', plain,
% 0.35/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf(redefinition_r2_relset_1, axiom,
% 0.35/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.35/0.52     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.35/0.52         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.35/0.52       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.35/0.52  thf('51', plain,
% 0.35/0.52      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.35/0.52         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.35/0.52          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.35/0.52          | (r2_relset_1 @ X16 @ X17 @ X15 @ X18)
% 0.35/0.52          | ((X15) != (X18)))),
% 0.35/0.52      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.35/0.52  thf('52', plain,
% 0.35/0.52      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.35/0.52         ((r2_relset_1 @ X16 @ X17 @ X18 @ X18)
% 0.35/0.52          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.35/0.52      inference('simplify', [status(thm)], ['51'])).
% 0.35/0.52  thf('53', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C)),
% 0.35/0.52      inference('sup-', [status(thm)], ['50', '52'])).
% 0.35/0.52  thf('54', plain, (((sk_A) = (k1_xboole_0))),
% 0.35/0.52      inference('demod', [status(thm)], ['49', '53'])).
% 0.35/0.52  thf('55', plain, (((sk_A) = (k1_xboole_0))),
% 0.35/0.52      inference('demod', [status(thm)], ['49', '53'])).
% 0.35/0.52  thf('56', plain,
% 0.35/0.52      (~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ (k2_funct_1 @ sk_B))),
% 0.35/0.52      inference('demod', [status(thm)], ['8', '54', '55'])).
% 0.35/0.52  thf('57', plain,
% 0.35/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('58', plain,
% 0.35/0.52      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.35/0.52         (~ (v1_funct_1 @ X20)
% 0.35/0.52          | ~ (v3_funct_2 @ X20 @ X21 @ X22)
% 0.35/0.52          | (v2_funct_2 @ X20 @ X22)
% 0.35/0.52          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.35/0.52      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.35/0.52  thf('59', plain,
% 0.35/0.52      (((v2_funct_2 @ sk_C @ sk_A)
% 0.35/0.52        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.35/0.52        | ~ (v1_funct_1 @ sk_C))),
% 0.35/0.52      inference('sup-', [status(thm)], ['57', '58'])).
% 0.35/0.52  thf('60', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('61', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('62', plain, ((v2_funct_2 @ sk_C @ sk_A)),
% 0.35/0.52      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.35/0.52  thf('63', plain,
% 0.35/0.52      (![X23 : $i, X24 : $i]:
% 0.35/0.52         (~ (v2_funct_2 @ X24 @ X23)
% 0.35/0.52          | ((k2_relat_1 @ X24) = (X23))
% 0.35/0.52          | ~ (v5_relat_1 @ X24 @ X23)
% 0.35/0.52          | ~ (v1_relat_1 @ X24))),
% 0.35/0.52      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.35/0.52  thf('64', plain,
% 0.35/0.52      ((~ (v1_relat_1 @ sk_C)
% 0.35/0.52        | ~ (v5_relat_1 @ sk_C @ sk_A)
% 0.35/0.52        | ((k2_relat_1 @ sk_C) = (sk_A)))),
% 0.35/0.52      inference('sup-', [status(thm)], ['62', '63'])).
% 0.35/0.52  thf('65', plain,
% 0.35/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('66', plain,
% 0.35/0.52      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.35/0.52         ((v1_relat_1 @ X6)
% 0.35/0.52          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.35/0.52      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.35/0.52  thf('67', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.52      inference('sup-', [status(thm)], ['65', '66'])).
% 0.35/0.52  thf('68', plain,
% 0.35/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('69', plain,
% 0.35/0.52      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.35/0.52         ((v5_relat_1 @ X9 @ X11)
% 0.35/0.52          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.35/0.52      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.35/0.52  thf('70', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.35/0.52      inference('sup-', [status(thm)], ['68', '69'])).
% 0.35/0.52  thf('71', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 0.35/0.52      inference('demod', [status(thm)], ['64', '67', '70'])).
% 0.35/0.52  thf(t64_relat_1, axiom,
% 0.35/0.52    (![A:$i]:
% 0.35/0.52     ( ( v1_relat_1 @ A ) =>
% 0.35/0.52       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.35/0.52           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.35/0.52         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.35/0.52  thf('72', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 0.35/0.52          | ((X0) = (k1_xboole_0))
% 0.35/0.52          | ~ (v1_relat_1 @ X0))),
% 0.35/0.52      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.35/0.52  thf('73', plain,
% 0.35/0.52      ((((sk_A) != (k1_xboole_0))
% 0.35/0.52        | ~ (v1_relat_1 @ sk_C)
% 0.35/0.52        | ((sk_C) = (k1_xboole_0)))),
% 0.35/0.52      inference('sup-', [status(thm)], ['71', '72'])).
% 0.35/0.52  thf('74', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.52      inference('sup-', [status(thm)], ['65', '66'])).
% 0.35/0.52  thf('75', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.35/0.52      inference('demod', [status(thm)], ['73', '74'])).
% 0.35/0.52  thf('76', plain, (((sk_A) = (k1_xboole_0))),
% 0.35/0.52      inference('demod', [status(thm)], ['49', '53'])).
% 0.35/0.52  thf('77', plain,
% 0.35/0.52      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.35/0.52      inference('demod', [status(thm)], ['75', '76'])).
% 0.35/0.52  thf('78', plain, (((sk_C) = (k1_xboole_0))),
% 0.35/0.52      inference('simplify', [status(thm)], ['77'])).
% 0.35/0.52  thf('79', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.35/0.52      inference('demod', [status(thm)], ['31', '34', '37'])).
% 0.35/0.52  thf('80', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 0.35/0.52          | ((X0) = (k1_xboole_0))
% 0.35/0.52          | ~ (v1_relat_1 @ X0))),
% 0.35/0.52      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.35/0.52  thf('81', plain,
% 0.35/0.52      ((((sk_A) != (k1_xboole_0))
% 0.35/0.52        | ~ (v1_relat_1 @ sk_B)
% 0.35/0.52        | ((sk_B) = (k1_xboole_0)))),
% 0.35/0.52      inference('sup-', [status(thm)], ['79', '80'])).
% 0.35/0.52  thf('82', plain, ((v1_relat_1 @ sk_B)),
% 0.35/0.52      inference('sup-', [status(thm)], ['32', '33'])).
% 0.35/0.52  thf('83', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.35/0.52      inference('demod', [status(thm)], ['81', '82'])).
% 0.35/0.52  thf('84', plain, (((sk_A) = (k1_xboole_0))),
% 0.35/0.52      inference('demod', [status(thm)], ['49', '53'])).
% 0.35/0.52  thf('85', plain,
% 0.35/0.52      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.35/0.52      inference('demod', [status(thm)], ['83', '84'])).
% 0.35/0.52  thf('86', plain, (((sk_B) = (k1_xboole_0))),
% 0.35/0.52      inference('simplify', [status(thm)], ['85'])).
% 0.35/0.52  thf(t71_relat_1, axiom,
% 0.35/0.52    (![A:$i]:
% 0.35/0.52     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.35/0.52       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.35/0.52  thf('87', plain, (![X1 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X1)) = (X1))),
% 0.35/0.52      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.35/0.52  thf(redefinition_k6_partfun1, axiom,
% 0.35/0.52    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.35/0.52  thf('88', plain, (![X27 : $i]: ((k6_partfun1 @ X27) = (k6_relat_1 @ X27))),
% 0.35/0.52      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.35/0.52  thf('89', plain, (![X1 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X1)) = (X1))),
% 0.35/0.52      inference('demod', [status(thm)], ['87', '88'])).
% 0.35/0.52  thf('90', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         (((k1_relat_1 @ X0) != (k1_xboole_0))
% 0.35/0.52          | ((X0) = (k1_xboole_0))
% 0.35/0.52          | ~ (v1_relat_1 @ X0))),
% 0.35/0.52      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.35/0.52  thf('91', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         (((X0) != (k1_xboole_0))
% 0.35/0.52          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 0.35/0.52          | ((k6_partfun1 @ X0) = (k1_xboole_0)))),
% 0.35/0.52      inference('sup-', [status(thm)], ['89', '90'])).
% 0.35/0.52  thf(fc4_funct_1, axiom,
% 0.35/0.52    (![A:$i]:
% 0.35/0.52     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.35/0.52       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.35/0.52  thf('92', plain, (![X3 : $i]: (v1_relat_1 @ (k6_relat_1 @ X3))),
% 0.35/0.52      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.35/0.52  thf('93', plain, (![X27 : $i]: ((k6_partfun1 @ X27) = (k6_relat_1 @ X27))),
% 0.35/0.52      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.35/0.52  thf('94', plain, (![X3 : $i]: (v1_relat_1 @ (k6_partfun1 @ X3))),
% 0.35/0.52      inference('demod', [status(thm)], ['92', '93'])).
% 0.35/0.52  thf('95', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         (((X0) != (k1_xboole_0)) | ((k6_partfun1 @ X0) = (k1_xboole_0)))),
% 0.35/0.52      inference('demod', [status(thm)], ['91', '94'])).
% 0.35/0.52  thf('96', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.35/0.52      inference('simplify', [status(thm)], ['95'])).
% 0.35/0.52  thf(t67_funct_1, axiom,
% 0.35/0.52    (![A:$i]: ( ( k2_funct_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 0.35/0.52  thf('97', plain,
% 0.35/0.52      (![X5 : $i]: ((k2_funct_1 @ (k6_relat_1 @ X5)) = (k6_relat_1 @ X5))),
% 0.35/0.52      inference('cnf', [status(esa)], [t67_funct_1])).
% 0.35/0.52  thf('98', plain, (![X27 : $i]: ((k6_partfun1 @ X27) = (k6_relat_1 @ X27))),
% 0.35/0.52      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.35/0.52  thf('99', plain, (![X27 : $i]: ((k6_partfun1 @ X27) = (k6_relat_1 @ X27))),
% 0.35/0.52      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.35/0.52  thf('100', plain,
% 0.35/0.52      (![X5 : $i]: ((k2_funct_1 @ (k6_partfun1 @ X5)) = (k6_partfun1 @ X5))),
% 0.35/0.52      inference('demod', [status(thm)], ['97', '98', '99'])).
% 0.35/0.52  thf('101', plain,
% 0.35/0.52      (((k2_funct_1 @ k1_xboole_0) = (k6_partfun1 @ k1_xboole_0))),
% 0.35/0.52      inference('sup+', [status(thm)], ['96', '100'])).
% 0.35/0.52  thf('102', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.35/0.52      inference('simplify', [status(thm)], ['95'])).
% 0.35/0.52  thf('103', plain, (((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.35/0.52      inference('sup+', [status(thm)], ['101', '102'])).
% 0.35/0.52  thf('104', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.35/0.52      inference('simplify', [status(thm)], ['95'])).
% 0.35/0.52  thf(t29_relset_1, axiom,
% 0.35/0.52    (![A:$i]:
% 0.35/0.52     ( m1_subset_1 @
% 0.35/0.52       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.35/0.52  thf('105', plain,
% 0.35/0.52      (![X19 : $i]:
% 0.35/0.52         (m1_subset_1 @ (k6_relat_1 @ X19) @ 
% 0.35/0.52          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))),
% 0.35/0.52      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.35/0.52  thf('106', plain, (![X27 : $i]: ((k6_partfun1 @ X27) = (k6_relat_1 @ X27))),
% 0.35/0.52      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.35/0.52  thf('107', plain,
% 0.35/0.52      (![X19 : $i]:
% 0.35/0.52         (m1_subset_1 @ (k6_partfun1 @ X19) @ 
% 0.35/0.52          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))),
% 0.35/0.52      inference('demod', [status(thm)], ['105', '106'])).
% 0.35/0.52  thf('108', plain,
% 0.35/0.52      ((m1_subset_1 @ k1_xboole_0 @ 
% 0.35/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.35/0.52      inference('sup+', [status(thm)], ['104', '107'])).
% 0.35/0.52  thf('109', plain,
% 0.35/0.52      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.35/0.52         ((r2_relset_1 @ X16 @ X17 @ X18 @ X18)
% 0.35/0.52          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.35/0.52      inference('simplify', [status(thm)], ['51'])).
% 0.35/0.52  thf('110', plain,
% 0.35/0.52      ((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.35/0.52      inference('sup-', [status(thm)], ['108', '109'])).
% 0.35/0.52  thf('111', plain, ($false),
% 0.35/0.52      inference('demod', [status(thm)], ['56', '78', '86', '103', '110'])).
% 0.35/0.52  
% 0.35/0.52  % SZS output end Refutation
% 0.35/0.52  
% 0.37/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
