%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9ZY1f6bf9o

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:49 EST 2020

% Result     : Theorem 6.73s
% Output     : Refutation 6.73s
% Verified   : 
% Statistics : Number of formulae       :  509 (28031 expanded)
%              Number of leaves         :   54 (8253 expanded)
%              Depth                    :   45
%              Number of atoms          : 4486 (584152 expanded)
%              Number of equality atoms :  234 (6436 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(t76_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ! [C: $i] :
          ( ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ( ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ C @ B ) @ B )
              & ( v2_funct_1 @ B ) )
           => ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ! [C: $i] :
            ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ A )
              & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
           => ( ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ C @ B ) @ B )
                & ( v2_funct_1 @ B ) )
             => ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t76_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k6_partfun1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X21: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('2',plain,(
    ! [X21: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X29: $i] :
      ( ~ ( v2_funct_1 @ X29 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X29 ) @ X29 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('4',plain,(
    ! [X57: $i] :
      ( ( k6_partfun1 @ X57 )
      = ( k6_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('5',plain,(
    ! [X29: $i] :
      ( ~ ( v2_funct_1 @ X29 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X29 ) @ X29 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X28: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k1_relat_1 @ X28 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X62: $i,X63: $i] :
      ( ( ( k1_relset_1 @ X62 @ X62 @ X63 )
        = X62 )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X62 @ X62 ) ) )
      | ~ ( v1_funct_2 @ X63 @ X62 @ X62 )
      | ~ ( v1_funct_1 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('9',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_C )
      = sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('13',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k1_relset_1 @ X36 @ X37 @ X35 )
        = ( k1_relat_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('14',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['9','10','11','14'])).

thf(t44_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( ( k2_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ( ( k5_relat_1 @ A @ B )
                = A ) )
           => ( B
              = ( k6_relat_1 @ ( k1_relat_1 @ B ) ) ) ) ) ) )).

thf('16',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ( X24
        = ( k6_relat_1 @ ( k1_relat_1 @ X24 ) ) )
      | ( ( k5_relat_1 @ X25 @ X24 )
       != X25 )
      | ( ( k2_relat_1 @ X25 )
       != ( k1_relat_1 @ X24 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t44_funct_1])).

thf('17',plain,(
    ! [X57: $i] :
      ( ( k6_partfun1 @ X57 )
      = ( k6_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('18',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ( X24
        = ( k6_partfun1 @ ( k1_relat_1 @ X24 ) ) )
      | ( ( k5_relat_1 @ X25 @ X24 )
       != X25 )
      | ( ( k2_relat_1 @ X25 )
       != ( k1_relat_1 @ X24 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ sk_C )
       != X0 )
      | ( sk_C
        = ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['9','10','11','14'])).

thf('21',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('23',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('25',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('26',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ sk_C )
       != X0 )
      | ( sk_C
        = ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['19','20','21','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( sk_C
        = ( k6_partfun1 @ sk_A ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ sk_C )
       != ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','27'])).

thf('29',plain,
    ( ( ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) )
     != ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( sk_C
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
     != sk_A ) ),
    inference('sup-',[status(thm)],['5','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('31',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('34',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['9','10','11','14'])).

thf('35',plain,
    ( ( ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) )
     != ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( sk_C
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_A != sk_A ) ),
    inference(demod,[status(thm)],['29','30','31','32','33','34'])).

thf('36',plain,
    ( ( sk_C
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) )
     != ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) )
     != ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( sk_C
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('39',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) )
     != ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( sk_C
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_C
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) )
     != ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('43',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( sk_C
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) )
     != ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('46',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v5_relat_1 @ X32 @ X34 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('47',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['45','46'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('48',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v5_relat_1 @ X8 @ X9 )
      | ( r1_tarski @ ( k2_relat_1 @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('51',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X62: $i,X63: $i] :
      ( ( ( k1_relset_1 @ X62 @ X62 @ X63 )
        = X62 )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X62 @ X62 ) ) )
      | ~ ( v1_funct_2 @ X63 @ X62 @ X62 )
      | ~ ( v1_funct_1 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('54',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k1_relset_1 @ X36 @ X37 @ X35 )
        = ( k1_relat_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('59',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['54','55','56','59'])).

thf(t164_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('61',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X22 @ ( k1_relat_1 @ X23 ) )
      | ~ ( v2_funct_1 @ X23 )
      | ( ( k10_relat_1 @ X23 @ ( k9_relat_1 @ X23 @ X22 ) )
        = X22 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t164_funct_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ X0 ) )
        = X0 )
      | ~ ( v2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('65',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('67',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['62','67','68','69'])).

thf('71',plain,
    ( ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ sk_C ) ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['51','70'])).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('72',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) )
        = ( k9_relat_1 @ X14 @ ( k2_relat_1 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('73',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('75',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X46 @ X47 @ X49 @ X50 @ X45 @ X48 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X50 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['73','78'])).

thf('80',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('83',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X53 ) ) )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_funct_1 @ X54 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X56 ) ) )
      | ( ( k1_partfun1 @ X52 @ X53 @ X55 @ X56 @ X51 @ X54 )
        = ( k5_relat_1 @ X51 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
      = ( k5_relat_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['81','86'])).

thf('88',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
    = ( k5_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['79','80','89'])).

thf('91',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v5_relat_1 @ X32 @ X34 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('92',plain,(
    v5_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v5_relat_1 @ X8 @ X9 )
      | ( r1_tarski @ ( k2_relat_1 @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('94',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) )
    | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['79','80','89'])).

thf('96',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('97',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('99',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['94','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['62','67','68','69'])).

thf('102',plain,
    ( ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) )
    = ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ sk_C ) ) ) )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['72','102'])).

thf('104',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('105',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['65','66'])).

thf('106',plain,
    ( ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ sk_C ) ) ) )
    = ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) )
        = ( k9_relat_1 @ X14 @ ( k2_relat_1 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('108',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['94','99'])).

thf('109',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ sk_C ) ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('111',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['65','66'])).

thf('112',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['62','67','68','69'])).

thf('114',plain,
    ( ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ sk_C ) ) ) )
    = ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) )
    = ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['106','114'])).

thf('116',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
    = ( k5_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('118',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['79','80','89'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('120',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ( X41 = X44 )
      | ~ ( r2_relset_1 @ X42 @ X43 @ X41 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_B ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_B )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['118','121'])).

thf('123',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( k5_relat_1 @ sk_C @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['115','124'])).

thf('126',plain,
    ( ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['71','125'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('128',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['62','67','68','69'])).

thf('130',plain,
    ( ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v4_relat_1 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('133',plain,(
    v4_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['131','132'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('134',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X16
        = ( k7_relat_1 @ X16 @ X17 ) )
      | ~ ( v4_relat_1 @ X16 @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('135',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( sk_B
      = ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['65','66'])).

thf('137',plain,
    ( sk_B
    = ( k7_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['135','136'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('138',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) )
        = ( k9_relat_1 @ X12 @ X13 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('139',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = ( k9_relat_1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf('140',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['65','66'])).

thf('141',plain,
    ( ( k2_relat_1 @ sk_B )
    = ( k9_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,
    ( ( k10_relat_1 @ sk_B @ ( k2_relat_1 @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['130','141'])).

thf('143',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference('sup+',[status(thm)],['126','142'])).

thf('144',plain,
    ( ( sk_C
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k6_partfun1 @ sk_A )
     != ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['44','143'])).

thf('145',plain,
    ( ( k5_relat_1 @ sk_C @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['122','123'])).

thf(t48_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) ) )
           => ( ( v2_funct_1 @ B )
              & ( v2_funct_1 @ A ) ) ) ) ) )).

thf('146',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ~ ( v1_funct_1 @ X26 )
      | ( v2_funct_1 @ X26 )
      | ( ( k2_relat_1 @ X26 )
       != ( k1_relat_1 @ X27 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X26 @ X27 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('147',plain,
    ( ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_B ) )
    | ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['65','66'])).

thf('150',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['54','55','56','59'])).

thf('152',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('154',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != sk_A )
    | ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['147','148','149','150','151','152','153'])).

thf('155',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference('sup+',[status(thm)],['126','142'])).

thf('156',plain,
    ( ( sk_A != sk_A )
    | ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('157',plain,(
    v2_funct_1 @ sk_C ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,
    ( ( sk_C
      = ( k6_partfun1 @ sk_A ) )
    | ( ( k6_partfun1 @ sk_A )
     != ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['144','157'])).

thf(t66_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( v2_funct_1 @ B ) )
           => ( ( k2_funct_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k5_relat_1 @ ( k2_funct_1 @ B ) @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('159',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v1_relat_1 @ X30 )
      | ~ ( v1_funct_1 @ X30 )
      | ( ( k2_funct_1 @ ( k5_relat_1 @ X31 @ X30 ) )
        = ( k5_relat_1 @ ( k2_funct_1 @ X30 ) @ ( k2_funct_1 @ X31 ) ) )
      | ~ ( v2_funct_1 @ X30 )
      | ~ ( v2_funct_1 @ X31 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t66_funct_1])).

thf('160',plain,(
    ! [X28: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k2_relat_1 @ X28 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('161',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v1_relat_1 @ X30 )
      | ~ ( v1_funct_1 @ X30 )
      | ( ( k2_funct_1 @ ( k5_relat_1 @ X31 @ X30 ) )
        = ( k5_relat_1 @ ( k2_funct_1 @ X30 ) @ ( k2_funct_1 @ X31 ) ) )
      | ~ ( v2_funct_1 @ X30 )
      | ~ ( v2_funct_1 @ X31 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t66_funct_1])).

thf('162',plain,
    ( ( k5_relat_1 @ sk_C @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['122','123'])).

thf('163',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v1_relat_1 @ X30 )
      | ~ ( v1_funct_1 @ X30 )
      | ( ( k2_funct_1 @ ( k5_relat_1 @ X31 @ X30 ) )
        = ( k5_relat_1 @ ( k2_funct_1 @ X30 ) @ ( k2_funct_1 @ X31 ) ) )
      | ~ ( v2_funct_1 @ X30 )
      | ~ ( v2_funct_1 @ X31 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t66_funct_1])).

thf('164',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) )
        = ( k9_relat_1 @ X14 @ ( k2_relat_1 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('165',plain,(
    ! [X18: $i] :
      ( ( r1_tarski @ X18 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X18 ) @ ( k2_relat_1 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X0 @ X1 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) @ ( k9_relat_1 @ X1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( r1_tarski @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_funct_1 @ X1 ) ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_funct_1 @ X1 ) ) ) @ ( k9_relat_1 @ ( k2_funct_1 @ X1 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['163','166'])).

thf('168',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ( r1_tarski @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) ) ) @ ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['162','167'])).

thf('169',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['54','55','56','59'])).

thf('170',plain,(
    ! [X18: $i] :
      ( ( r1_tarski @ X18 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X18 ) @ ( k2_relat_1 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('171',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('172',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['169','172'])).

thf('174',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['65','66'])).

thf('175',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['173','174'])).

thf(t31_funct_2,axiom,(
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

thf('176',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ~ ( v2_funct_1 @ X58 )
      | ( ( k2_relset_1 @ X60 @ X59 @ X58 )
       != X59 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X58 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X59 @ X60 ) ) )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X60 @ X59 ) ) )
      | ~ ( v1_funct_2 @ X58 @ X60 @ X59 )
      | ~ ( v1_funct_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('177',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ ( k2_relat_1 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ ( k2_relat_1 @ sk_B ) @ sk_B )
     != ( k2_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['54','55','56','59'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('180',plain,(
    ! [X61: $i] :
      ( ( v1_funct_2 @ X61 @ ( k1_relat_1 @ X61 ) @ ( k2_relat_1 @ X61 ) )
      | ~ ( v1_funct_1 @ X61 )
      | ~ ( v1_relat_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('181',plain,
    ( ( v1_funct_2 @ sk_B @ sk_A @ ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['179','180'])).

thf('182',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['65','66'])).

thf('183',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    v1_funct_2 @ sk_B @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['181','182','183'])).

thf('185',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['173','174'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('186',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( ( k2_relset_1 @ X39 @ X40 @ X38 )
        = ( k2_relat_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('187',plain,
    ( ( k2_relset_1 @ sk_A @ ( k2_relat_1 @ sk_B ) @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ) )
    | ( ( k2_relat_1 @ sk_B )
     != ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['177','178','184','187','188'])).

thf('190',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['189'])).

thf('191',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('192',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_B ) @ sk_A ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('194',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['192','193'])).

thf('195',plain,(
    ! [X28: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k1_relat_1 @ X28 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('196',plain,(
    ! [X21: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('197',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['54','55','56','59'])).

thf('198',plain,(
    ! [X21: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('199',plain,(
    ! [X28: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k1_relat_1 @ X28 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('200',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('201',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v5_relat_1 @ X32 @ X34 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('202',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['200','201'])).

thf('203',plain,(
    ! [X0: $i] :
      ( ( v5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['199','202'])).

thf('204',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['198','203'])).

thf('205',plain,(
    ! [X0: $i] :
      ( ( v5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['204'])).

thf('206',plain,
    ( ( v5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['197','205'])).

thf('207',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['65','66'])).

thf('208',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    v5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['206','207','208','209'])).

thf('211',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v5_relat_1 @ X8 @ X9 )
      | ( r1_tarski @ ( k2_relat_1 @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('212',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['210','211'])).

thf('213',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['196','212'])).

thf('214',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['65','66'])).

thf('215',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['213','214','215'])).

thf('217',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('218',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) )
    | ( sk_A
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['216','217'])).

thf('219',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( sk_A
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['195','218'])).

thf('220',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['54','55','56','59'])).

thf('221',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['127'])).

thf('222',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['65','66'])).

thf('223',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,
    ( sk_A
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['219','220','221','222','223','224'])).

thf('226',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference('sup+',[status(thm)],['126','142'])).

thf('227',plain,(
    ! [X21: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('228',plain,(
    ! [X29: $i] :
      ( ~ ( v2_funct_1 @ X29 )
      | ( ( k5_relat_1 @ X29 @ ( k2_funct_1 @ X29 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('229',plain,(
    ! [X57: $i] :
      ( ( k6_partfun1 @ X57 )
      = ( k6_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('230',plain,(
    ! [X29: $i] :
      ( ~ ( v2_funct_1 @ X29 )
      | ( ( k5_relat_1 @ X29 @ ( k2_funct_1 @ X29 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(demod,[status(thm)],['228','229'])).

thf('231',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) )
        = ( k9_relat_1 @ X14 @ ( k2_relat_1 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('232',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['230','231'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('233',plain,(
    ! [X20: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X20 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('234',plain,(
    ! [X57: $i] :
      ( ( k6_partfun1 @ X57 )
      = ( k6_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('235',plain,(
    ! [X20: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X20 ) )
      = X20 ) ),
    inference(demod,[status(thm)],['233','234'])).

thf('236',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['232','235'])).

thf('237',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['236'])).

thf('238',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['227','237'])).

thf('239',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['238'])).

thf('240',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['226','239'])).

thf('241',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['9','10','11','14'])).

thf('242',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('243',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,
    ( ( sk_A
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['240','241','242','243'])).

thf('245',plain,(
    v2_funct_1 @ sk_C ),
    inference(simplify,[status(thm)],['156'])).

thf('246',plain,
    ( sk_A
    = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['244','245'])).

thf('247',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['192','193'])).

thf('248',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['9','10','11','14'])).

thf('249',plain,(
    ! [X21: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('250',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('251',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v4_relat_1 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('252',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['250','251'])).

thf('253',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X16
        = ( k7_relat_1 @ X16 @ X17 ) )
      | ~ ( v4_relat_1 @ X16 @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('254',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['252','253'])).

thf('255',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['254'])).

thf('256',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) )
        = ( k9_relat_1 @ X12 @ X13 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('257',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['255','256'])).

thf('258',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['257'])).

thf('259',plain,(
    ! [X21: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('260',plain,(
    ! [X28: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k1_relat_1 @ X28 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('261',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['254'])).

thf('262',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['254'])).

thf('263',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) )
        = ( k9_relat_1 @ X12 @ X13 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('264',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['200','201'])).

thf('265',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['263','264'])).

thf('266',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['262','265'])).

thf('267',plain,(
    ! [X0: $i] :
      ( ( v5_relat_1 @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['266'])).

thf('268',plain,(
    ! [X0: $i] :
      ( ( v5_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['261','267'])).

thf('269',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['268'])).

thf('270',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v5_relat_1 @ X8 @ X9 )
      | ( r1_tarski @ ( k2_relat_1 @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('271',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['269','270'])).

thf('272',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['271'])).

thf('273',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('274',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_relat_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['272','273'])).

thf('275',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_relat_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['260','274'])).

thf('276',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k1_relat_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['259','275'])).

thf('277',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_relat_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['276'])).

thf('278',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_relat_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['258','277'])).

thf('279',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k1_relat_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['249','278'])).

thf('280',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_relat_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['279'])).

thf('281',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('282',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['280','281'])).

thf('283',plain,
    ( ( r1_tarski @ sk_A @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['248','282'])).

thf('284',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('285',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('286',plain,
    ( ( r1_tarski @ sk_A @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['283','284','285'])).

thf('287',plain,(
    v2_funct_1 @ sk_C ),
    inference(simplify,[status(thm)],['156'])).

thf('288',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['286','287'])).

thf('289',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('290',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['288','289'])).

thf('291',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['9','10','11','14'])).

thf('292',plain,(
    ! [X21: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('293',plain,(
    ! [X0: $i] :
      ( ( v5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['204'])).

thf('294',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v5_relat_1 @ X8 @ X9 )
      | ( r1_tarski @ ( k2_relat_1 @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('295',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['293','294'])).

thf('296',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['292','295'])).

thf('297',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['296'])).

thf('298',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['291','297'])).

thf('299',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('300',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('301',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['298','299','300'])).

thf('302',plain,(
    v2_funct_1 @ sk_C ),
    inference(simplify,[status(thm)],['156'])).

thf('303',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['301','302'])).

thf('304',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = sk_A ),
    inference(demod,[status(thm)],['290','303'])).

thf('305',plain,(
    ! [X21: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('306',plain,(
    ! [X28: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k2_relat_1 @ X28 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('307',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('308',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['306','307'])).

thf('309',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['305','308'])).

thf('310',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['309'])).

thf('311',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['304','310'])).

thf('312',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference('sup+',[status(thm)],['126','142'])).

thf('313',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('314',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('315',plain,(
    v2_funct_1 @ sk_C ),
    inference(simplify,[status(thm)],['156'])).

thf('316',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['311','312','313','314','315'])).

thf('317',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('318',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['316','317'])).

thf('319',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('320',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['318','319'])).

thf('321',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['65','66'])).

thf('322',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('323',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('324',plain,(
    v2_funct_1 @ sk_C ),
    inference(simplify,[status(thm)],['156'])).

thf('325',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('326',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('327',plain,(
    r1_tarski @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['168','194','225','246','247','320','321','322','323','324','325','326'])).

thf('328',plain,
    ( ( r1_tarski @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['161','327'])).

thf('329',plain,
    ( ( k5_relat_1 @ sk_C @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['122','123'])).

thf('330',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('331',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('332',plain,(
    v2_funct_1 @ sk_C ),
    inference(simplify,[status(thm)],['156'])).

thf('333',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('334',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('335',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['65','66'])).

thf('336',plain,(
    r1_tarski @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['328','329','330','331','332','333','334','335'])).

thf('337',plain,
    ( ( r1_tarski @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) ) @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['160','336'])).

thf('338',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['65','66'])).

thf('339',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('340',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('341',plain,(
    r1_tarski @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) ) @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['337','338','339','340'])).

thf('342',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('343',plain,(
    m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['341','342'])).

thf('344',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v4_relat_1 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('345',plain,(
    v4_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['343','344'])).

thf('346',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X16
        = ( k7_relat_1 @ X16 @ X17 ) )
      | ~ ( v4_relat_1 @ X16 @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('347',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k7_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['345','346'])).

thf('348',plain,(
    m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['341','342'])).

thf('349',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('350',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_B ) @ sk_A ) )
    | ( v1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['348','349'])).

thf('351',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('352',plain,(
    v1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['350','351'])).

thf('353',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k7_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['347','352'])).

thf('354',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k7_relat_1 @ ( k2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['159','353'])).

thf('355',plain,
    ( ( k5_relat_1 @ sk_C @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['122','123'])).

thf('356',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['189'])).

thf('357',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v4_relat_1 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('358',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['356','357'])).

thf('359',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X16
        = ( k7_relat_1 @ X16 @ X17 ) )
      | ~ ( v4_relat_1 @ X16 @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('360',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k2_funct_1 @ sk_B )
      = ( k7_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['358','359'])).

thf('361',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['192','193'])).

thf('362',plain,
    ( ( k2_funct_1 @ sk_B )
    = ( k7_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['360','361'])).

thf('363',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('364',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('365',plain,(
    v2_funct_1 @ sk_C ),
    inference(simplify,[status(thm)],['156'])).

thf('366',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('367',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('368',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['65','66'])).

thf('369',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['354','355','362','363','364','365','366','367','368'])).

thf('370',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['311','312','313','314','315'])).

thf('371',plain,(
    ! [X62: $i,X63: $i] :
      ( ( ( k1_relset_1 @ X62 @ X62 @ X63 )
        = X62 )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X62 @ X62 ) ) )
      | ~ ( v1_funct_2 @ X63 @ X62 @ X62 )
      | ~ ( v1_funct_1 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('372',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ sk_C ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['370','371'])).

thf('373',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['9','10','11','14'])).

thf('374',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('375',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['373','374'])).

thf('376',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('377',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['375','376'])).

thf('378',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ~ ( v2_funct_1 @ X58 )
      | ( ( k2_relset_1 @ X60 @ X59 @ X58 )
       != X59 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X58 ) )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X60 @ X59 ) ) )
      | ~ ( v1_funct_2 @ X58 @ X60 @ X59 )
      | ~ ( v1_funct_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('379',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['377','378'])).

thf('380',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('381',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['9','10','11','14'])).

thf('382',plain,(
    ! [X61: $i] :
      ( ( v1_funct_2 @ X61 @ ( k1_relat_1 @ X61 ) @ ( k2_relat_1 @ X61 ) )
      | ~ ( v1_funct_1 @ X61 )
      | ~ ( v1_relat_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('383',plain,
    ( ( v1_funct_2 @ sk_C @ sk_A @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['381','382'])).

thf('384',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('385',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('386',plain,(
    v1_funct_2 @ sk_C @ sk_A @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['383','384','385'])).

thf('387',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['375','376'])).

thf('388',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( ( k2_relset_1 @ X39 @ X40 @ X38 )
        = ( k2_relat_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('389',plain,
    ( ( k2_relset_1 @ sk_A @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['387','388'])).

thf('390',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['379','380','386','389'])).

thf('391',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['390'])).

thf('392',plain,(
    v2_funct_1 @ sk_C ),
    inference(simplify,[status(thm)],['156'])).

thf('393',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['391','392'])).

thf('394',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('395',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ~ ( v2_funct_1 @ X58 )
      | ( ( k2_relset_1 @ X60 @ X59 @ X58 )
       != X59 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X58 ) @ X59 @ X60 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X60 @ X59 ) ) )
      | ~ ( v1_funct_2 @ X58 @ X60 @ X59 )
      | ~ ( v1_funct_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('396',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_A @ sk_A )
    | ( ( k2_relset_1 @ sk_A @ sk_A @ sk_C )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['394','395'])).

thf('397',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('398',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('399',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('400',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( ( k2_relset_1 @ X39 @ X40 @ X38 )
        = ( k2_relat_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('401',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['399','400'])).

thf('402',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_A @ sk_A )
    | ( ( k2_relat_1 @ sk_C )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['396','397','398','401'])).

thf('403',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference('sup+',[status(thm)],['126','142'])).

thf('404',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_A @ sk_A )
    | ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['402','403'])).

thf('405',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_A @ sk_A ) ),
    inference(simplify,[status(thm)],['404'])).

thf('406',plain,(
    v2_funct_1 @ sk_C ),
    inference(simplify,[status(thm)],['156'])).

thf('407',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['405','406'])).

thf('408',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference('sup+',[status(thm)],['126','142'])).

thf('409',plain,(
    ! [X28: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k2_relat_1 @ X28 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('410',plain,(
    ! [X21: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('411',plain,(
    ! [X28: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k1_relat_1 @ X28 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('412',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('413',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['411','412'])).

thf('414',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['410','413'])).

thf('415',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['414'])).

thf('416',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['409','415'])).

thf('417',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['416'])).

thf('418',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k1_relset_1 @ X36 @ X37 @ X35 )
        = ( k1_relat_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('419',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relset_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) @ ( k2_funct_1 @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['417','418'])).

thf('420',plain,
    ( ( ( k1_relset_1 @ sk_A @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['408','419'])).

thf('421',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['9','10','11','14'])).

thf('422',plain,(
    v2_funct_1 @ sk_C ),
    inference(simplify,[status(thm)],['156'])).

thf('423',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('424',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['24','25'])).

thf('425',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['420','421','422','423','424'])).

thf('426',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = sk_A ),
    inference(demod,[status(thm)],['372','393','407','425'])).

thf('427',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ( X24
        = ( k6_partfun1 @ ( k1_relat_1 @ X24 ) ) )
      | ( ( k5_relat_1 @ X25 @ X24 )
       != X25 )
      | ( ( k2_relat_1 @ X25 )
       != ( k1_relat_1 @ X24 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('428',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ sk_C ) )
       != X0 )
      | ( ( k2_funct_1 @ sk_C )
        = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['426','427'])).

thf('429',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = sk_A ),
    inference(demod,[status(thm)],['372','393','407','425'])).

thf('430',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['391','392'])).

thf('431',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['318','319'])).

thf('432',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ sk_C ) )
       != X0 )
      | ( ( k2_funct_1 @ sk_C )
        = ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['428','429','430','431'])).

thf('433',plain,
    ( ( ( k2_funct_1 @ sk_B )
     != ( k2_funct_1 @ sk_B ) )
    | ( ( k2_funct_1 @ sk_C )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['369','432'])).

thf('434',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['173','174'])).

thf('435',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ~ ( v2_funct_1 @ X58 )
      | ( ( k2_relset_1 @ X60 @ X59 @ X58 )
       != X59 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X58 ) )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X60 @ X59 ) ) )
      | ~ ( v1_funct_2 @ X58 @ X60 @ X59 )
      | ~ ( v1_funct_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('436',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ ( k2_relat_1 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k2_relset_1 @ sk_A @ ( k2_relat_1 @ sk_B ) @ sk_B )
     != ( k2_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['434','435'])).

thf('437',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('438',plain,(
    v1_funct_2 @ sk_B @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['181','182','183'])).

thf('439',plain,
    ( ( k2_relset_1 @ sk_A @ ( k2_relat_1 @ sk_B ) @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('440',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('441',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k2_relat_1 @ sk_B )
     != ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['436','437','438','439','440'])).

thf('442',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['441'])).

thf('443',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['192','193'])).

thf('444',plain,
    ( sk_A
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['219','220','221','222','223','224'])).

thf('445',plain,
    ( ( ( k2_funct_1 @ sk_B )
     != ( k2_funct_1 @ sk_B ) )
    | ( ( k2_funct_1 @ sk_C )
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_A != sk_A ) ),
    inference(demod,[status(thm)],['433','442','443','444'])).

thf('446',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k6_partfun1 @ sk_A ) ),
    inference(simplify,[status(thm)],['445'])).

thf('447',plain,
    ( ( sk_C
      = ( k6_partfun1 @ sk_A ) )
    | ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['158','446'])).

thf('448',plain,
    ( sk_C
    = ( k6_partfun1 @ sk_A ) ),
    inference(simplify,[status(thm)],['447'])).

thf('449',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('450',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ( r2_relset_1 @ X42 @ X43 @ X41 @ X44 )
      | ( X41 != X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('451',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( r2_relset_1 @ X42 @ X43 @ X44 @ X44 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) ) ) ),
    inference(simplify,[status(thm)],['450'])).

thf('452',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['449','451'])).

thf('453',plain,(
    $false ),
    inference(demod,[status(thm)],['0','448','452'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9ZY1f6bf9o
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:39:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 6.73/6.99  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 6.73/6.99  % Solved by: fo/fo7.sh
% 6.73/6.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.73/6.99  % done 7469 iterations in 6.529s
% 6.73/6.99  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 6.73/6.99  % SZS output start Refutation
% 6.73/6.99  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.73/6.99  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 6.73/6.99  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 6.73/6.99  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 6.73/6.99  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 6.73/6.99  thf(sk_C_type, type, sk_C: $i).
% 6.73/6.99  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 6.73/6.99  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.73/6.99  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 6.73/6.99  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 6.73/6.99  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 6.73/6.99  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 6.73/6.99  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 6.73/6.99  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 6.73/6.99  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.73/6.99  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 6.73/6.99  thf(sk_B_type, type, sk_B: $i).
% 6.73/6.99  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 6.73/6.99  thf(sk_A_type, type, sk_A: $i).
% 6.73/6.99  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 6.73/6.99  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 6.73/6.99  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 6.73/6.99  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 6.73/6.99  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 6.73/6.99  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 6.73/6.99  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 6.73/6.99  thf(t76_funct_2, conjecture,
% 6.73/6.99    (![A:$i,B:$i]:
% 6.73/6.99     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 6.73/6.99         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 6.73/6.99       ( ![C:$i]:
% 6.73/6.99         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 6.73/6.99             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 6.73/6.99           ( ( ( r2_relset_1 @
% 6.73/6.99                 A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ C @ B ) @ B ) & 
% 6.73/6.99               ( v2_funct_1 @ B ) ) =>
% 6.73/6.99             ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ))).
% 6.73/6.99  thf(zf_stmt_0, negated_conjecture,
% 6.73/6.99    (~( ![A:$i,B:$i]:
% 6.73/6.99        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 6.73/6.99            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 6.73/6.99          ( ![C:$i]:
% 6.73/6.99            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 6.73/6.99                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 6.73/6.99              ( ( ( r2_relset_1 @
% 6.73/6.99                    A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ C @ B ) @ B ) & 
% 6.73/6.99                  ( v2_funct_1 @ B ) ) =>
% 6.73/6.99                ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ) )),
% 6.73/6.99    inference('cnf.neg', [status(esa)], [t76_funct_2])).
% 6.73/6.99  thf('0', plain,
% 6.73/6.99      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_partfun1 @ sk_A))),
% 6.73/6.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/6.99  thf(dt_k2_funct_1, axiom,
% 6.73/6.99    (![A:$i]:
% 6.73/6.99     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 6.73/6.99       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 6.73/6.99         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 6.73/6.99  thf('1', plain,
% 6.73/6.99      (![X21 : $i]:
% 6.73/6.99         ((v1_relat_1 @ (k2_funct_1 @ X21))
% 6.73/6.99          | ~ (v1_funct_1 @ X21)
% 6.73/6.99          | ~ (v1_relat_1 @ X21))),
% 6.73/6.99      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.73/6.99  thf('2', plain,
% 6.73/6.99      (![X21 : $i]:
% 6.73/6.99         ((v1_funct_1 @ (k2_funct_1 @ X21))
% 6.73/6.99          | ~ (v1_funct_1 @ X21)
% 6.73/6.99          | ~ (v1_relat_1 @ X21))),
% 6.73/6.99      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.73/6.99  thf(t61_funct_1, axiom,
% 6.73/6.99    (![A:$i]:
% 6.73/6.99     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 6.73/6.99       ( ( v2_funct_1 @ A ) =>
% 6.73/6.99         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 6.73/6.99             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 6.73/6.99           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 6.73/6.99             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 6.73/6.99  thf('3', plain,
% 6.73/6.99      (![X29 : $i]:
% 6.73/6.99         (~ (v2_funct_1 @ X29)
% 6.73/6.99          | ((k5_relat_1 @ (k2_funct_1 @ X29) @ X29)
% 6.73/6.99              = (k6_relat_1 @ (k2_relat_1 @ X29)))
% 6.73/6.99          | ~ (v1_funct_1 @ X29)
% 6.73/6.99          | ~ (v1_relat_1 @ X29))),
% 6.73/6.99      inference('cnf', [status(esa)], [t61_funct_1])).
% 6.73/6.99  thf(redefinition_k6_partfun1, axiom,
% 6.73/6.99    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 6.73/6.99  thf('4', plain, (![X57 : $i]: ((k6_partfun1 @ X57) = (k6_relat_1 @ X57))),
% 6.73/6.99      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 6.73/6.99  thf('5', plain,
% 6.73/6.99      (![X29 : $i]:
% 6.73/6.99         (~ (v2_funct_1 @ X29)
% 6.73/6.99          | ((k5_relat_1 @ (k2_funct_1 @ X29) @ X29)
% 6.73/6.99              = (k6_partfun1 @ (k2_relat_1 @ X29)))
% 6.73/6.99          | ~ (v1_funct_1 @ X29)
% 6.73/6.99          | ~ (v1_relat_1 @ X29))),
% 6.73/6.99      inference('demod', [status(thm)], ['3', '4'])).
% 6.73/6.99  thf(t55_funct_1, axiom,
% 6.73/6.99    (![A:$i]:
% 6.73/6.99     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 6.73/6.99       ( ( v2_funct_1 @ A ) =>
% 6.73/6.99         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 6.73/6.99           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 6.73/6.99  thf('6', plain,
% 6.73/6.99      (![X28 : $i]:
% 6.73/6.99         (~ (v2_funct_1 @ X28)
% 6.73/6.99          | ((k1_relat_1 @ X28) = (k2_relat_1 @ (k2_funct_1 @ X28)))
% 6.73/6.99          | ~ (v1_funct_1 @ X28)
% 6.73/6.99          | ~ (v1_relat_1 @ X28))),
% 6.73/6.99      inference('cnf', [status(esa)], [t55_funct_1])).
% 6.73/6.99  thf('7', plain,
% 6.73/6.99      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.73/6.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/6.99  thf(t67_funct_2, axiom,
% 6.73/6.99    (![A:$i,B:$i]:
% 6.73/6.99     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 6.73/6.99         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 6.73/6.99       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 6.73/6.99  thf('8', plain,
% 6.73/6.99      (![X62 : $i, X63 : $i]:
% 6.73/6.99         (((k1_relset_1 @ X62 @ X62 @ X63) = (X62))
% 6.73/6.99          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X62 @ X62)))
% 6.73/6.99          | ~ (v1_funct_2 @ X63 @ X62 @ X62)
% 6.73/6.99          | ~ (v1_funct_1 @ X63))),
% 6.73/6.99      inference('cnf', [status(esa)], [t67_funct_2])).
% 6.73/6.99  thf('9', plain,
% 6.73/6.99      ((~ (v1_funct_1 @ sk_C)
% 6.73/6.99        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 6.73/6.99        | ((k1_relset_1 @ sk_A @ sk_A @ sk_C) = (sk_A)))),
% 6.73/6.99      inference('sup-', [status(thm)], ['7', '8'])).
% 6.73/6.99  thf('10', plain, ((v1_funct_1 @ sk_C)),
% 6.73/6.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/6.99  thf('11', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 6.73/6.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/6.99  thf('12', plain,
% 6.73/6.99      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.73/6.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/6.99  thf(redefinition_k1_relset_1, axiom,
% 6.73/6.99    (![A:$i,B:$i,C:$i]:
% 6.73/6.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.73/6.99       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 6.73/6.99  thf('13', plain,
% 6.73/6.99      (![X35 : $i, X36 : $i, X37 : $i]:
% 6.73/6.99         (((k1_relset_1 @ X36 @ X37 @ X35) = (k1_relat_1 @ X35))
% 6.73/6.99          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 6.73/6.99      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 6.73/6.99  thf('14', plain,
% 6.73/6.99      (((k1_relset_1 @ sk_A @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 6.73/6.99      inference('sup-', [status(thm)], ['12', '13'])).
% 6.73/6.99  thf('15', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 6.73/6.99      inference('demod', [status(thm)], ['9', '10', '11', '14'])).
% 6.73/6.99  thf(t44_funct_1, axiom,
% 6.73/6.99    (![A:$i]:
% 6.73/6.99     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 6.73/6.99       ( ![B:$i]:
% 6.73/6.99         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 6.73/6.99           ( ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 6.73/6.99               ( ( k5_relat_1 @ A @ B ) = ( A ) ) ) =>
% 6.73/6.99             ( ( B ) = ( k6_relat_1 @ ( k1_relat_1 @ B ) ) ) ) ) ) ))).
% 6.73/6.99  thf('16', plain,
% 6.73/6.99      (![X24 : $i, X25 : $i]:
% 6.73/6.99         (~ (v1_relat_1 @ X24)
% 6.73/6.99          | ~ (v1_funct_1 @ X24)
% 6.73/6.99          | ((X24) = (k6_relat_1 @ (k1_relat_1 @ X24)))
% 6.73/6.99          | ((k5_relat_1 @ X25 @ X24) != (X25))
% 6.73/6.99          | ((k2_relat_1 @ X25) != (k1_relat_1 @ X24))
% 6.73/6.99          | ~ (v1_funct_1 @ X25)
% 6.73/6.99          | ~ (v1_relat_1 @ X25))),
% 6.73/6.99      inference('cnf', [status(esa)], [t44_funct_1])).
% 6.73/6.99  thf('17', plain, (![X57 : $i]: ((k6_partfun1 @ X57) = (k6_relat_1 @ X57))),
% 6.73/6.99      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 6.73/6.99  thf('18', plain,
% 6.73/6.99      (![X24 : $i, X25 : $i]:
% 6.73/6.99         (~ (v1_relat_1 @ X24)
% 6.73/6.99          | ~ (v1_funct_1 @ X24)
% 6.73/6.99          | ((X24) = (k6_partfun1 @ (k1_relat_1 @ X24)))
% 6.73/6.99          | ((k5_relat_1 @ X25 @ X24) != (X25))
% 6.73/6.99          | ((k2_relat_1 @ X25) != (k1_relat_1 @ X24))
% 6.73/6.99          | ~ (v1_funct_1 @ X25)
% 6.73/6.99          | ~ (v1_relat_1 @ X25))),
% 6.73/6.99      inference('demod', [status(thm)], ['16', '17'])).
% 6.73/6.99  thf('19', plain,
% 6.73/6.99      (![X0 : $i]:
% 6.73/6.99         (((k2_relat_1 @ X0) != (sk_A))
% 6.73/6.99          | ~ (v1_relat_1 @ X0)
% 6.73/6.99          | ~ (v1_funct_1 @ X0)
% 6.73/6.99          | ((k5_relat_1 @ X0 @ sk_C) != (X0))
% 6.73/6.99          | ((sk_C) = (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 6.73/6.99          | ~ (v1_funct_1 @ sk_C)
% 6.73/6.99          | ~ (v1_relat_1 @ sk_C))),
% 6.73/6.99      inference('sup-', [status(thm)], ['15', '18'])).
% 6.73/6.99  thf('20', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 6.73/6.99      inference('demod', [status(thm)], ['9', '10', '11', '14'])).
% 6.73/6.99  thf('21', plain, ((v1_funct_1 @ sk_C)),
% 6.73/6.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/6.99  thf('22', plain,
% 6.73/6.99      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.73/6.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/6.99  thf(cc2_relat_1, axiom,
% 6.73/6.99    (![A:$i]:
% 6.73/6.99     ( ( v1_relat_1 @ A ) =>
% 6.73/6.99       ( ![B:$i]:
% 6.73/6.99         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 6.73/6.99  thf('23', plain,
% 6.73/6.99      (![X6 : $i, X7 : $i]:
% 6.73/6.99         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 6.73/6.99          | (v1_relat_1 @ X6)
% 6.73/6.99          | ~ (v1_relat_1 @ X7))),
% 6.73/6.99      inference('cnf', [status(esa)], [cc2_relat_1])).
% 6.73/6.99  thf('24', plain,
% 6.73/6.99      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_C))),
% 6.73/6.99      inference('sup-', [status(thm)], ['22', '23'])).
% 6.73/6.99  thf(fc6_relat_1, axiom,
% 6.73/6.99    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 6.73/6.99  thf('25', plain,
% 6.73/6.99      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 6.73/6.99      inference('cnf', [status(esa)], [fc6_relat_1])).
% 6.73/6.99  thf('26', plain, ((v1_relat_1 @ sk_C)),
% 6.73/6.99      inference('demod', [status(thm)], ['24', '25'])).
% 6.73/6.99  thf('27', plain,
% 6.73/6.99      (![X0 : $i]:
% 6.73/6.99         (((k2_relat_1 @ X0) != (sk_A))
% 6.73/6.99          | ~ (v1_relat_1 @ X0)
% 6.73/6.99          | ~ (v1_funct_1 @ X0)
% 6.73/6.99          | ((k5_relat_1 @ X0 @ sk_C) != (X0))
% 6.73/6.99          | ((sk_C) = (k6_partfun1 @ sk_A)))),
% 6.73/6.99      inference('demod', [status(thm)], ['19', '20', '21', '26'])).
% 6.73/6.99  thf('28', plain,
% 6.73/6.99      (![X0 : $i]:
% 6.73/6.99         (((k1_relat_1 @ X0) != (sk_A))
% 6.73/6.99          | ~ (v1_relat_1 @ X0)
% 6.73/6.99          | ~ (v1_funct_1 @ X0)
% 6.73/6.99          | ~ (v2_funct_1 @ X0)
% 6.73/6.99          | ((sk_C) = (k6_partfun1 @ sk_A))
% 6.73/6.99          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ sk_C) != (k2_funct_1 @ X0))
% 6.73/6.99          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.73/6.99          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 6.73/6.99      inference('sup-', [status(thm)], ['6', '27'])).
% 6.73/6.99  thf('29', plain,
% 6.73/6.99      ((((k6_partfun1 @ (k2_relat_1 @ sk_C)) != (k2_funct_1 @ sk_C))
% 6.73/6.99        | ~ (v1_relat_1 @ sk_C)
% 6.73/6.99        | ~ (v1_funct_1 @ sk_C)
% 6.73/6.99        | ~ (v2_funct_1 @ sk_C)
% 6.73/6.99        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 6.73/6.99        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 6.73/6.99        | ((sk_C) = (k6_partfun1 @ sk_A))
% 6.73/6.99        | ~ (v2_funct_1 @ sk_C)
% 6.73/6.99        | ~ (v1_funct_1 @ sk_C)
% 6.73/6.99        | ~ (v1_relat_1 @ sk_C)
% 6.73/6.99        | ((k1_relat_1 @ sk_C) != (sk_A)))),
% 6.73/6.99      inference('sup-', [status(thm)], ['5', '28'])).
% 6.73/6.99  thf('30', plain, ((v1_relat_1 @ sk_C)),
% 6.73/6.99      inference('demod', [status(thm)], ['24', '25'])).
% 6.73/6.99  thf('31', plain, ((v1_funct_1 @ sk_C)),
% 6.73/6.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/6.99  thf('32', plain, ((v1_funct_1 @ sk_C)),
% 6.73/6.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/6.99  thf('33', plain, ((v1_relat_1 @ sk_C)),
% 6.73/6.99      inference('demod', [status(thm)], ['24', '25'])).
% 6.73/6.99  thf('34', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 6.73/6.99      inference('demod', [status(thm)], ['9', '10', '11', '14'])).
% 6.73/6.99  thf('35', plain,
% 6.73/6.99      ((((k6_partfun1 @ (k2_relat_1 @ sk_C)) != (k2_funct_1 @ sk_C))
% 6.73/6.99        | ~ (v2_funct_1 @ sk_C)
% 6.73/6.99        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 6.73/6.99        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 6.73/6.99        | ((sk_C) = (k6_partfun1 @ sk_A))
% 6.73/6.99        | ~ (v2_funct_1 @ sk_C)
% 6.73/6.99        | ((sk_A) != (sk_A)))),
% 6.73/6.99      inference('demod', [status(thm)], ['29', '30', '31', '32', '33', '34'])).
% 6.73/6.99  thf('36', plain,
% 6.73/6.99      ((((sk_C) = (k6_partfun1 @ sk_A))
% 6.73/6.99        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 6.73/6.99        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 6.73/6.99        | ~ (v2_funct_1 @ sk_C)
% 6.73/6.99        | ((k6_partfun1 @ (k2_relat_1 @ sk_C)) != (k2_funct_1 @ sk_C)))),
% 6.73/6.99      inference('simplify', [status(thm)], ['35'])).
% 6.73/6.99  thf('37', plain,
% 6.73/6.99      ((~ (v1_relat_1 @ sk_C)
% 6.73/7.00        | ~ (v1_funct_1 @ sk_C)
% 6.73/7.00        | ((k6_partfun1 @ (k2_relat_1 @ sk_C)) != (k2_funct_1 @ sk_C))
% 6.73/7.00        | ~ (v2_funct_1 @ sk_C)
% 6.73/7.00        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 6.73/7.00        | ((sk_C) = (k6_partfun1 @ sk_A)))),
% 6.73/7.00      inference('sup-', [status(thm)], ['2', '36'])).
% 6.73/7.00  thf('38', plain, ((v1_relat_1 @ sk_C)),
% 6.73/7.00      inference('demod', [status(thm)], ['24', '25'])).
% 6.73/7.00  thf('39', plain, ((v1_funct_1 @ sk_C)),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('40', plain,
% 6.73/7.00      ((((k6_partfun1 @ (k2_relat_1 @ sk_C)) != (k2_funct_1 @ sk_C))
% 6.73/7.00        | ~ (v2_funct_1 @ sk_C)
% 6.73/7.00        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 6.73/7.00        | ((sk_C) = (k6_partfun1 @ sk_A)))),
% 6.73/7.00      inference('demod', [status(thm)], ['37', '38', '39'])).
% 6.73/7.00  thf('41', plain,
% 6.73/7.00      ((~ (v1_relat_1 @ sk_C)
% 6.73/7.00        | ~ (v1_funct_1 @ sk_C)
% 6.73/7.00        | ((sk_C) = (k6_partfun1 @ sk_A))
% 6.73/7.00        | ~ (v2_funct_1 @ sk_C)
% 6.73/7.00        | ((k6_partfun1 @ (k2_relat_1 @ sk_C)) != (k2_funct_1 @ sk_C)))),
% 6.73/7.00      inference('sup-', [status(thm)], ['1', '40'])).
% 6.73/7.00  thf('42', plain, ((v1_relat_1 @ sk_C)),
% 6.73/7.00      inference('demod', [status(thm)], ['24', '25'])).
% 6.73/7.00  thf('43', plain, ((v1_funct_1 @ sk_C)),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('44', plain,
% 6.73/7.00      ((((sk_C) = (k6_partfun1 @ sk_A))
% 6.73/7.00        | ~ (v2_funct_1 @ sk_C)
% 6.73/7.00        | ((k6_partfun1 @ (k2_relat_1 @ sk_C)) != (k2_funct_1 @ sk_C)))),
% 6.73/7.00      inference('demod', [status(thm)], ['41', '42', '43'])).
% 6.73/7.00  thf('45', plain,
% 6.73/7.00      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf(cc2_relset_1, axiom,
% 6.73/7.00    (![A:$i,B:$i,C:$i]:
% 6.73/7.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.73/7.00       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 6.73/7.00  thf('46', plain,
% 6.73/7.00      (![X32 : $i, X33 : $i, X34 : $i]:
% 6.73/7.00         ((v5_relat_1 @ X32 @ X34)
% 6.73/7.00          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 6.73/7.00      inference('cnf', [status(esa)], [cc2_relset_1])).
% 6.73/7.00  thf('47', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 6.73/7.00      inference('sup-', [status(thm)], ['45', '46'])).
% 6.73/7.00  thf(d19_relat_1, axiom,
% 6.73/7.00    (![A:$i,B:$i]:
% 6.73/7.00     ( ( v1_relat_1 @ B ) =>
% 6.73/7.00       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 6.73/7.00  thf('48', plain,
% 6.73/7.00      (![X8 : $i, X9 : $i]:
% 6.73/7.00         (~ (v5_relat_1 @ X8 @ X9)
% 6.73/7.00          | (r1_tarski @ (k2_relat_1 @ X8) @ X9)
% 6.73/7.00          | ~ (v1_relat_1 @ X8))),
% 6.73/7.00      inference('cnf', [status(esa)], [d19_relat_1])).
% 6.73/7.00  thf('49', plain,
% 6.73/7.00      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A))),
% 6.73/7.00      inference('sup-', [status(thm)], ['47', '48'])).
% 6.73/7.00  thf('50', plain, ((v1_relat_1 @ sk_C)),
% 6.73/7.00      inference('demod', [status(thm)], ['24', '25'])).
% 6.73/7.00  thf('51', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A)),
% 6.73/7.00      inference('demod', [status(thm)], ['49', '50'])).
% 6.73/7.00  thf('52', plain,
% 6.73/7.00      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('53', plain,
% 6.73/7.00      (![X62 : $i, X63 : $i]:
% 6.73/7.00         (((k1_relset_1 @ X62 @ X62 @ X63) = (X62))
% 6.73/7.00          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X62 @ X62)))
% 6.73/7.00          | ~ (v1_funct_2 @ X63 @ X62 @ X62)
% 6.73/7.00          | ~ (v1_funct_1 @ X63))),
% 6.73/7.00      inference('cnf', [status(esa)], [t67_funct_2])).
% 6.73/7.00  thf('54', plain,
% 6.73/7.00      ((~ (v1_funct_1 @ sk_B)
% 6.73/7.00        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 6.73/7.00        | ((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A)))),
% 6.73/7.00      inference('sup-', [status(thm)], ['52', '53'])).
% 6.73/7.00  thf('55', plain, ((v1_funct_1 @ sk_B)),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('56', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('57', plain,
% 6.73/7.00      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('58', plain,
% 6.73/7.00      (![X35 : $i, X36 : $i, X37 : $i]:
% 6.73/7.00         (((k1_relset_1 @ X36 @ X37 @ X35) = (k1_relat_1 @ X35))
% 6.73/7.00          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 6.73/7.00      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 6.73/7.00  thf('59', plain,
% 6.73/7.00      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 6.73/7.00      inference('sup-', [status(thm)], ['57', '58'])).
% 6.73/7.00  thf('60', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 6.73/7.00      inference('demod', [status(thm)], ['54', '55', '56', '59'])).
% 6.73/7.00  thf(t164_funct_1, axiom,
% 6.73/7.00    (![A:$i,B:$i]:
% 6.73/7.00     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 6.73/7.00       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 6.73/7.00         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 6.73/7.00  thf('61', plain,
% 6.73/7.00      (![X22 : $i, X23 : $i]:
% 6.73/7.00         (~ (r1_tarski @ X22 @ (k1_relat_1 @ X23))
% 6.73/7.00          | ~ (v2_funct_1 @ X23)
% 6.73/7.00          | ((k10_relat_1 @ X23 @ (k9_relat_1 @ X23 @ X22)) = (X22))
% 6.73/7.00          | ~ (v1_funct_1 @ X23)
% 6.73/7.00          | ~ (v1_relat_1 @ X23))),
% 6.73/7.00      inference('cnf', [status(esa)], [t164_funct_1])).
% 6.73/7.00  thf('62', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         (~ (r1_tarski @ X0 @ sk_A)
% 6.73/7.00          | ~ (v1_relat_1 @ sk_B)
% 6.73/7.00          | ~ (v1_funct_1 @ sk_B)
% 6.73/7.00          | ((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ X0)) = (X0))
% 6.73/7.00          | ~ (v2_funct_1 @ sk_B))),
% 6.73/7.00      inference('sup-', [status(thm)], ['60', '61'])).
% 6.73/7.00  thf('63', plain,
% 6.73/7.00      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('64', plain,
% 6.73/7.00      (![X6 : $i, X7 : $i]:
% 6.73/7.00         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 6.73/7.00          | (v1_relat_1 @ X6)
% 6.73/7.00          | ~ (v1_relat_1 @ X7))),
% 6.73/7.00      inference('cnf', [status(esa)], [cc2_relat_1])).
% 6.73/7.00  thf('65', plain,
% 6.73/7.00      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 6.73/7.00      inference('sup-', [status(thm)], ['63', '64'])).
% 6.73/7.00  thf('66', plain,
% 6.73/7.00      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 6.73/7.00      inference('cnf', [status(esa)], [fc6_relat_1])).
% 6.73/7.00  thf('67', plain, ((v1_relat_1 @ sk_B)),
% 6.73/7.00      inference('demod', [status(thm)], ['65', '66'])).
% 6.73/7.00  thf('68', plain, ((v1_funct_1 @ sk_B)),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('69', plain, ((v2_funct_1 @ sk_B)),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('70', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         (~ (r1_tarski @ X0 @ sk_A)
% 6.73/7.00          | ((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ X0)) = (X0)))),
% 6.73/7.00      inference('demod', [status(thm)], ['62', '67', '68', '69'])).
% 6.73/7.00  thf('71', plain,
% 6.73/7.00      (((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ (k2_relat_1 @ sk_C)))
% 6.73/7.00         = (k2_relat_1 @ sk_C))),
% 6.73/7.00      inference('sup-', [status(thm)], ['51', '70'])).
% 6.73/7.00  thf(t160_relat_1, axiom,
% 6.73/7.00    (![A:$i]:
% 6.73/7.00     ( ( v1_relat_1 @ A ) =>
% 6.73/7.00       ( ![B:$i]:
% 6.73/7.00         ( ( v1_relat_1 @ B ) =>
% 6.73/7.00           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 6.73/7.00             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 6.73/7.00  thf('72', plain,
% 6.73/7.00      (![X14 : $i, X15 : $i]:
% 6.73/7.00         (~ (v1_relat_1 @ X14)
% 6.73/7.00          | ((k2_relat_1 @ (k5_relat_1 @ X15 @ X14))
% 6.73/7.00              = (k9_relat_1 @ X14 @ (k2_relat_1 @ X15)))
% 6.73/7.00          | ~ (v1_relat_1 @ X15))),
% 6.73/7.00      inference('cnf', [status(esa)], [t160_relat_1])).
% 6.73/7.00  thf('73', plain,
% 6.73/7.00      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('74', plain,
% 6.73/7.00      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf(dt_k1_partfun1, axiom,
% 6.73/7.00    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 6.73/7.00     ( ( ( v1_funct_1 @ E ) & 
% 6.73/7.00         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 6.73/7.00         ( v1_funct_1 @ F ) & 
% 6.73/7.00         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 6.73/7.00       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 6.73/7.00         ( m1_subset_1 @
% 6.73/7.00           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 6.73/7.00           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 6.73/7.00  thf('75', plain,
% 6.73/7.00      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 6.73/7.00         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 6.73/7.00          | ~ (v1_funct_1 @ X45)
% 6.73/7.00          | ~ (v1_funct_1 @ X48)
% 6.73/7.00          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50)))
% 6.73/7.00          | (m1_subset_1 @ (k1_partfun1 @ X46 @ X47 @ X49 @ X50 @ X45 @ X48) @ 
% 6.73/7.00             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X50))))),
% 6.73/7.00      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 6.73/7.00  thf('76', plain,
% 6.73/7.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.73/7.00         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1) @ 
% 6.73/7.00           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 6.73/7.00          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 6.73/7.00          | ~ (v1_funct_1 @ X1)
% 6.73/7.00          | ~ (v1_funct_1 @ sk_C))),
% 6.73/7.00      inference('sup-', [status(thm)], ['74', '75'])).
% 6.73/7.00  thf('77', plain, ((v1_funct_1 @ sk_C)),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('78', plain,
% 6.73/7.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.73/7.00         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1) @ 
% 6.73/7.00           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 6.73/7.00          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 6.73/7.00          | ~ (v1_funct_1 @ X1))),
% 6.73/7.00      inference('demod', [status(thm)], ['76', '77'])).
% 6.73/7.00  thf('79', plain,
% 6.73/7.00      ((~ (v1_funct_1 @ sk_B)
% 6.73/7.00        | (m1_subset_1 @ 
% 6.73/7.00           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) @ 
% 6.73/7.00           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 6.73/7.00      inference('sup-', [status(thm)], ['73', '78'])).
% 6.73/7.00  thf('80', plain, ((v1_funct_1 @ sk_B)),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('81', plain,
% 6.73/7.00      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('82', plain,
% 6.73/7.00      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf(redefinition_k1_partfun1, axiom,
% 6.73/7.00    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 6.73/7.00     ( ( ( v1_funct_1 @ E ) & 
% 6.73/7.00         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 6.73/7.00         ( v1_funct_1 @ F ) & 
% 6.73/7.00         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 6.73/7.00       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 6.73/7.00  thf('83', plain,
% 6.73/7.00      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 6.73/7.00         (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X53)))
% 6.73/7.00          | ~ (v1_funct_1 @ X51)
% 6.73/7.00          | ~ (v1_funct_1 @ X54)
% 6.73/7.00          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X56)))
% 6.73/7.00          | ((k1_partfun1 @ X52 @ X53 @ X55 @ X56 @ X51 @ X54)
% 6.73/7.00              = (k5_relat_1 @ X51 @ X54)))),
% 6.73/7.00      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 6.73/7.00  thf('84', plain,
% 6.73/7.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.73/7.00         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0)
% 6.73/7.00            = (k5_relat_1 @ sk_C @ X0))
% 6.73/7.00          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 6.73/7.00          | ~ (v1_funct_1 @ X0)
% 6.73/7.00          | ~ (v1_funct_1 @ sk_C))),
% 6.73/7.00      inference('sup-', [status(thm)], ['82', '83'])).
% 6.73/7.00  thf('85', plain, ((v1_funct_1 @ sk_C)),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('86', plain,
% 6.73/7.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.73/7.00         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0)
% 6.73/7.00            = (k5_relat_1 @ sk_C @ X0))
% 6.73/7.00          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 6.73/7.00          | ~ (v1_funct_1 @ X0))),
% 6.73/7.00      inference('demod', [status(thm)], ['84', '85'])).
% 6.73/7.00  thf('87', plain,
% 6.73/7.00      ((~ (v1_funct_1 @ sk_B)
% 6.73/7.00        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)
% 6.73/7.00            = (k5_relat_1 @ sk_C @ sk_B)))),
% 6.73/7.00      inference('sup-', [status(thm)], ['81', '86'])).
% 6.73/7.00  thf('88', plain, ((v1_funct_1 @ sk_B)),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('89', plain,
% 6.73/7.00      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)
% 6.73/7.00         = (k5_relat_1 @ sk_C @ sk_B))),
% 6.73/7.00      inference('demod', [status(thm)], ['87', '88'])).
% 6.73/7.00  thf('90', plain,
% 6.73/7.00      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_B) @ 
% 6.73/7.00        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.73/7.00      inference('demod', [status(thm)], ['79', '80', '89'])).
% 6.73/7.00  thf('91', plain,
% 6.73/7.00      (![X32 : $i, X33 : $i, X34 : $i]:
% 6.73/7.00         ((v5_relat_1 @ X32 @ X34)
% 6.73/7.00          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 6.73/7.00      inference('cnf', [status(esa)], [cc2_relset_1])).
% 6.73/7.00  thf('92', plain, ((v5_relat_1 @ (k5_relat_1 @ sk_C @ sk_B) @ sk_A)),
% 6.73/7.00      inference('sup-', [status(thm)], ['90', '91'])).
% 6.73/7.00  thf('93', plain,
% 6.73/7.00      (![X8 : $i, X9 : $i]:
% 6.73/7.00         (~ (v5_relat_1 @ X8 @ X9)
% 6.73/7.00          | (r1_tarski @ (k2_relat_1 @ X8) @ X9)
% 6.73/7.00          | ~ (v1_relat_1 @ X8))),
% 6.73/7.00      inference('cnf', [status(esa)], [d19_relat_1])).
% 6.73/7.00  thf('94', plain,
% 6.73/7.00      ((~ (v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B))
% 6.73/7.00        | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)) @ sk_A))),
% 6.73/7.00      inference('sup-', [status(thm)], ['92', '93'])).
% 6.73/7.00  thf('95', plain,
% 6.73/7.00      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_B) @ 
% 6.73/7.00        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.73/7.00      inference('demod', [status(thm)], ['79', '80', '89'])).
% 6.73/7.00  thf('96', plain,
% 6.73/7.00      (![X6 : $i, X7 : $i]:
% 6.73/7.00         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 6.73/7.00          | (v1_relat_1 @ X6)
% 6.73/7.00          | ~ (v1_relat_1 @ X7))),
% 6.73/7.00      inference('cnf', [status(esa)], [cc2_relat_1])).
% 6.73/7.00  thf('97', plain,
% 6.73/7.00      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 6.73/7.00        | (v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))),
% 6.73/7.00      inference('sup-', [status(thm)], ['95', '96'])).
% 6.73/7.00  thf('98', plain,
% 6.73/7.00      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 6.73/7.00      inference('cnf', [status(esa)], [fc6_relat_1])).
% 6.73/7.00  thf('99', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B))),
% 6.73/7.00      inference('demod', [status(thm)], ['97', '98'])).
% 6.73/7.00  thf('100', plain,
% 6.73/7.00      ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)) @ sk_A)),
% 6.73/7.00      inference('demod', [status(thm)], ['94', '99'])).
% 6.73/7.00  thf('101', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         (~ (r1_tarski @ X0 @ sk_A)
% 6.73/7.00          | ((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ X0)) = (X0)))),
% 6.73/7.00      inference('demod', [status(thm)], ['62', '67', '68', '69'])).
% 6.73/7.00  thf('102', plain,
% 6.73/7.00      (((k10_relat_1 @ sk_B @ 
% 6.73/7.00         (k9_relat_1 @ sk_B @ (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_B))))
% 6.73/7.00         = (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))),
% 6.73/7.00      inference('sup-', [status(thm)], ['100', '101'])).
% 6.73/7.00  thf('103', plain,
% 6.73/7.00      ((((k10_relat_1 @ sk_B @ 
% 6.73/7.00          (k9_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ (k2_relat_1 @ sk_C))))
% 6.73/7.00          = (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))
% 6.73/7.00        | ~ (v1_relat_1 @ sk_C)
% 6.73/7.00        | ~ (v1_relat_1 @ sk_B))),
% 6.73/7.00      inference('sup+', [status(thm)], ['72', '102'])).
% 6.73/7.00  thf('104', plain, ((v1_relat_1 @ sk_C)),
% 6.73/7.00      inference('demod', [status(thm)], ['24', '25'])).
% 6.73/7.00  thf('105', plain, ((v1_relat_1 @ sk_B)),
% 6.73/7.00      inference('demod', [status(thm)], ['65', '66'])).
% 6.73/7.00  thf('106', plain,
% 6.73/7.00      (((k10_relat_1 @ sk_B @ 
% 6.73/7.00         (k9_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ (k2_relat_1 @ sk_C))))
% 6.73/7.00         = (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))),
% 6.73/7.00      inference('demod', [status(thm)], ['103', '104', '105'])).
% 6.73/7.00  thf('107', plain,
% 6.73/7.00      (![X14 : $i, X15 : $i]:
% 6.73/7.00         (~ (v1_relat_1 @ X14)
% 6.73/7.00          | ((k2_relat_1 @ (k5_relat_1 @ X15 @ X14))
% 6.73/7.00              = (k9_relat_1 @ X14 @ (k2_relat_1 @ X15)))
% 6.73/7.00          | ~ (v1_relat_1 @ X15))),
% 6.73/7.00      inference('cnf', [status(esa)], [t160_relat_1])).
% 6.73/7.00  thf('108', plain,
% 6.73/7.00      ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)) @ sk_A)),
% 6.73/7.00      inference('demod', [status(thm)], ['94', '99'])).
% 6.73/7.00  thf('109', plain,
% 6.73/7.00      (((r1_tarski @ (k9_relat_1 @ sk_B @ (k2_relat_1 @ sk_C)) @ sk_A)
% 6.73/7.00        | ~ (v1_relat_1 @ sk_C)
% 6.73/7.00        | ~ (v1_relat_1 @ sk_B))),
% 6.73/7.00      inference('sup+', [status(thm)], ['107', '108'])).
% 6.73/7.00  thf('110', plain, ((v1_relat_1 @ sk_C)),
% 6.73/7.00      inference('demod', [status(thm)], ['24', '25'])).
% 6.73/7.00  thf('111', plain, ((v1_relat_1 @ sk_B)),
% 6.73/7.00      inference('demod', [status(thm)], ['65', '66'])).
% 6.73/7.00  thf('112', plain,
% 6.73/7.00      ((r1_tarski @ (k9_relat_1 @ sk_B @ (k2_relat_1 @ sk_C)) @ sk_A)),
% 6.73/7.00      inference('demod', [status(thm)], ['109', '110', '111'])).
% 6.73/7.00  thf('113', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         (~ (r1_tarski @ X0 @ sk_A)
% 6.73/7.00          | ((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ X0)) = (X0)))),
% 6.73/7.00      inference('demod', [status(thm)], ['62', '67', '68', '69'])).
% 6.73/7.00  thf('114', plain,
% 6.73/7.00      (((k10_relat_1 @ sk_B @ 
% 6.73/7.00         (k9_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ (k2_relat_1 @ sk_C))))
% 6.73/7.00         = (k9_relat_1 @ sk_B @ (k2_relat_1 @ sk_C)))),
% 6.73/7.00      inference('sup-', [status(thm)], ['112', '113'])).
% 6.73/7.00  thf('115', plain,
% 6.73/7.00      (((k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_B))
% 6.73/7.00         = (k9_relat_1 @ sk_B @ (k2_relat_1 @ sk_C)))),
% 6.73/7.00      inference('sup+', [status(thm)], ['106', '114'])).
% 6.73/7.00  thf('116', plain,
% 6.73/7.00      ((r2_relset_1 @ sk_A @ sk_A @ 
% 6.73/7.00        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) @ sk_B)),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('117', plain,
% 6.73/7.00      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)
% 6.73/7.00         = (k5_relat_1 @ sk_C @ sk_B))),
% 6.73/7.00      inference('demod', [status(thm)], ['87', '88'])).
% 6.73/7.00  thf('118', plain,
% 6.73/7.00      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_B) @ sk_B)),
% 6.73/7.00      inference('demod', [status(thm)], ['116', '117'])).
% 6.73/7.00  thf('119', plain,
% 6.73/7.00      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_B) @ 
% 6.73/7.00        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.73/7.00      inference('demod', [status(thm)], ['79', '80', '89'])).
% 6.73/7.00  thf(redefinition_r2_relset_1, axiom,
% 6.73/7.00    (![A:$i,B:$i,C:$i,D:$i]:
% 6.73/7.00     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 6.73/7.00         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.73/7.00       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 6.73/7.00  thf('120', plain,
% 6.73/7.00      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 6.73/7.00         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 6.73/7.00          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 6.73/7.00          | ((X41) = (X44))
% 6.73/7.00          | ~ (r2_relset_1 @ X42 @ X43 @ X41 @ X44))),
% 6.73/7.00      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 6.73/7.00  thf('121', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_B) @ X0)
% 6.73/7.00          | ((k5_relat_1 @ sk_C @ sk_B) = (X0))
% 6.73/7.00          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 6.73/7.00      inference('sup-', [status(thm)], ['119', '120'])).
% 6.73/7.00  thf('122', plain,
% 6.73/7.00      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 6.73/7.00        | ((k5_relat_1 @ sk_C @ sk_B) = (sk_B)))),
% 6.73/7.00      inference('sup-', [status(thm)], ['118', '121'])).
% 6.73/7.00  thf('123', plain,
% 6.73/7.00      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('124', plain, (((k5_relat_1 @ sk_C @ sk_B) = (sk_B))),
% 6.73/7.00      inference('demod', [status(thm)], ['122', '123'])).
% 6.73/7.00  thf('125', plain,
% 6.73/7.00      (((k2_relat_1 @ sk_B) = (k9_relat_1 @ sk_B @ (k2_relat_1 @ sk_C)))),
% 6.73/7.00      inference('demod', [status(thm)], ['115', '124'])).
% 6.73/7.00  thf('126', plain,
% 6.73/7.00      (((k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)) = (k2_relat_1 @ sk_C))),
% 6.73/7.00      inference('demod', [status(thm)], ['71', '125'])).
% 6.73/7.00  thf(d10_xboole_0, axiom,
% 6.73/7.00    (![A:$i,B:$i]:
% 6.73/7.00     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 6.73/7.00  thf('127', plain,
% 6.73/7.00      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 6.73/7.00      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.73/7.00  thf('128', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 6.73/7.00      inference('simplify', [status(thm)], ['127'])).
% 6.73/7.00  thf('129', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         (~ (r1_tarski @ X0 @ sk_A)
% 6.73/7.00          | ((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ X0)) = (X0)))),
% 6.73/7.00      inference('demod', [status(thm)], ['62', '67', '68', '69'])).
% 6.73/7.00  thf('130', plain,
% 6.73/7.00      (((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) = (sk_A))),
% 6.73/7.00      inference('sup-', [status(thm)], ['128', '129'])).
% 6.73/7.00  thf('131', plain,
% 6.73/7.00      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('132', plain,
% 6.73/7.00      (![X32 : $i, X33 : $i, X34 : $i]:
% 6.73/7.00         ((v4_relat_1 @ X32 @ X33)
% 6.73/7.00          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 6.73/7.00      inference('cnf', [status(esa)], [cc2_relset_1])).
% 6.73/7.00  thf('133', plain, ((v4_relat_1 @ sk_B @ sk_A)),
% 6.73/7.00      inference('sup-', [status(thm)], ['131', '132'])).
% 6.73/7.00  thf(t209_relat_1, axiom,
% 6.73/7.00    (![A:$i,B:$i]:
% 6.73/7.00     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 6.73/7.00       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 6.73/7.00  thf('134', plain,
% 6.73/7.00      (![X16 : $i, X17 : $i]:
% 6.73/7.00         (((X16) = (k7_relat_1 @ X16 @ X17))
% 6.73/7.00          | ~ (v4_relat_1 @ X16 @ X17)
% 6.73/7.00          | ~ (v1_relat_1 @ X16))),
% 6.73/7.00      inference('cnf', [status(esa)], [t209_relat_1])).
% 6.73/7.00  thf('135', plain,
% 6.73/7.00      ((~ (v1_relat_1 @ sk_B) | ((sk_B) = (k7_relat_1 @ sk_B @ sk_A)))),
% 6.73/7.00      inference('sup-', [status(thm)], ['133', '134'])).
% 6.73/7.00  thf('136', plain, ((v1_relat_1 @ sk_B)),
% 6.73/7.00      inference('demod', [status(thm)], ['65', '66'])).
% 6.73/7.00  thf('137', plain, (((sk_B) = (k7_relat_1 @ sk_B @ sk_A))),
% 6.73/7.00      inference('demod', [status(thm)], ['135', '136'])).
% 6.73/7.00  thf(t148_relat_1, axiom,
% 6.73/7.00    (![A:$i,B:$i]:
% 6.73/7.00     ( ( v1_relat_1 @ B ) =>
% 6.73/7.00       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 6.73/7.00  thf('138', plain,
% 6.73/7.00      (![X12 : $i, X13 : $i]:
% 6.73/7.00         (((k2_relat_1 @ (k7_relat_1 @ X12 @ X13)) = (k9_relat_1 @ X12 @ X13))
% 6.73/7.00          | ~ (v1_relat_1 @ X12))),
% 6.73/7.00      inference('cnf', [status(esa)], [t148_relat_1])).
% 6.73/7.00  thf('139', plain,
% 6.73/7.00      ((((k2_relat_1 @ sk_B) = (k9_relat_1 @ sk_B @ sk_A))
% 6.73/7.00        | ~ (v1_relat_1 @ sk_B))),
% 6.73/7.00      inference('sup+', [status(thm)], ['137', '138'])).
% 6.73/7.00  thf('140', plain, ((v1_relat_1 @ sk_B)),
% 6.73/7.00      inference('demod', [status(thm)], ['65', '66'])).
% 6.73/7.00  thf('141', plain, (((k2_relat_1 @ sk_B) = (k9_relat_1 @ sk_B @ sk_A))),
% 6.73/7.00      inference('demod', [status(thm)], ['139', '140'])).
% 6.73/7.00  thf('142', plain, (((k10_relat_1 @ sk_B @ (k2_relat_1 @ sk_B)) = (sk_A))),
% 6.73/7.00      inference('demod', [status(thm)], ['130', '141'])).
% 6.73/7.00  thf('143', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 6.73/7.00      inference('sup+', [status(thm)], ['126', '142'])).
% 6.73/7.00  thf('144', plain,
% 6.73/7.00      ((((sk_C) = (k6_partfun1 @ sk_A))
% 6.73/7.00        | ~ (v2_funct_1 @ sk_C)
% 6.73/7.00        | ((k6_partfun1 @ sk_A) != (k2_funct_1 @ sk_C)))),
% 6.73/7.00      inference('demod', [status(thm)], ['44', '143'])).
% 6.73/7.00  thf('145', plain, (((k5_relat_1 @ sk_C @ sk_B) = (sk_B))),
% 6.73/7.00      inference('demod', [status(thm)], ['122', '123'])).
% 6.73/7.00  thf(t48_funct_1, axiom,
% 6.73/7.00    (![A:$i]:
% 6.73/7.00     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 6.73/7.00       ( ![B:$i]:
% 6.73/7.00         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 6.73/7.00           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 6.73/7.00               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 6.73/7.00             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 6.73/7.00  thf('146', plain,
% 6.73/7.00      (![X26 : $i, X27 : $i]:
% 6.73/7.00         (~ (v1_relat_1 @ X26)
% 6.73/7.00          | ~ (v1_funct_1 @ X26)
% 6.73/7.00          | (v2_funct_1 @ X26)
% 6.73/7.00          | ((k2_relat_1 @ X26) != (k1_relat_1 @ X27))
% 6.73/7.00          | ~ (v2_funct_1 @ (k5_relat_1 @ X26 @ X27))
% 6.73/7.00          | ~ (v1_funct_1 @ X27)
% 6.73/7.00          | ~ (v1_relat_1 @ X27))),
% 6.73/7.00      inference('cnf', [status(esa)], [t48_funct_1])).
% 6.73/7.00  thf('147', plain,
% 6.73/7.00      ((~ (v2_funct_1 @ sk_B)
% 6.73/7.00        | ~ (v1_relat_1 @ sk_B)
% 6.73/7.00        | ~ (v1_funct_1 @ sk_B)
% 6.73/7.00        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_B))
% 6.73/7.00        | (v2_funct_1 @ sk_C)
% 6.73/7.00        | ~ (v1_funct_1 @ sk_C)
% 6.73/7.00        | ~ (v1_relat_1 @ sk_C))),
% 6.73/7.00      inference('sup-', [status(thm)], ['145', '146'])).
% 6.73/7.00  thf('148', plain, ((v2_funct_1 @ sk_B)),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('149', plain, ((v1_relat_1 @ sk_B)),
% 6.73/7.00      inference('demod', [status(thm)], ['65', '66'])).
% 6.73/7.00  thf('150', plain, ((v1_funct_1 @ sk_B)),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('151', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 6.73/7.00      inference('demod', [status(thm)], ['54', '55', '56', '59'])).
% 6.73/7.00  thf('152', plain, ((v1_funct_1 @ sk_C)),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('153', plain, ((v1_relat_1 @ sk_C)),
% 6.73/7.00      inference('demod', [status(thm)], ['24', '25'])).
% 6.73/7.00  thf('154', plain, ((((k2_relat_1 @ sk_C) != (sk_A)) | (v2_funct_1 @ sk_C))),
% 6.73/7.00      inference('demod', [status(thm)],
% 6.73/7.00                ['147', '148', '149', '150', '151', '152', '153'])).
% 6.73/7.00  thf('155', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 6.73/7.00      inference('sup+', [status(thm)], ['126', '142'])).
% 6.73/7.00  thf('156', plain, ((((sk_A) != (sk_A)) | (v2_funct_1 @ sk_C))),
% 6.73/7.00      inference('demod', [status(thm)], ['154', '155'])).
% 6.73/7.00  thf('157', plain, ((v2_funct_1 @ sk_C)),
% 6.73/7.00      inference('simplify', [status(thm)], ['156'])).
% 6.73/7.00  thf('158', plain,
% 6.73/7.00      ((((sk_C) = (k6_partfun1 @ sk_A))
% 6.73/7.00        | ((k6_partfun1 @ sk_A) != (k2_funct_1 @ sk_C)))),
% 6.73/7.00      inference('demod', [status(thm)], ['144', '157'])).
% 6.73/7.00  thf(t66_funct_1, axiom,
% 6.73/7.00    (![A:$i]:
% 6.73/7.00     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 6.73/7.00       ( ![B:$i]:
% 6.73/7.00         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 6.73/7.00           ( ( ( v2_funct_1 @ A ) & ( v2_funct_1 @ B ) ) =>
% 6.73/7.00             ( ( k2_funct_1 @ ( k5_relat_1 @ A @ B ) ) =
% 6.73/7.00               ( k5_relat_1 @ ( k2_funct_1 @ B ) @ ( k2_funct_1 @ A ) ) ) ) ) ) ))).
% 6.73/7.00  thf('159', plain,
% 6.73/7.00      (![X30 : $i, X31 : $i]:
% 6.73/7.00         (~ (v1_relat_1 @ X30)
% 6.73/7.00          | ~ (v1_funct_1 @ X30)
% 6.73/7.00          | ((k2_funct_1 @ (k5_relat_1 @ X31 @ X30))
% 6.73/7.00              = (k5_relat_1 @ (k2_funct_1 @ X30) @ (k2_funct_1 @ X31)))
% 6.73/7.00          | ~ (v2_funct_1 @ X30)
% 6.73/7.00          | ~ (v2_funct_1 @ X31)
% 6.73/7.00          | ~ (v1_funct_1 @ X31)
% 6.73/7.00          | ~ (v1_relat_1 @ X31))),
% 6.73/7.00      inference('cnf', [status(esa)], [t66_funct_1])).
% 6.73/7.00  thf('160', plain,
% 6.73/7.00      (![X28 : $i]:
% 6.73/7.00         (~ (v2_funct_1 @ X28)
% 6.73/7.00          | ((k2_relat_1 @ X28) = (k1_relat_1 @ (k2_funct_1 @ X28)))
% 6.73/7.00          | ~ (v1_funct_1 @ X28)
% 6.73/7.00          | ~ (v1_relat_1 @ X28))),
% 6.73/7.00      inference('cnf', [status(esa)], [t55_funct_1])).
% 6.73/7.00  thf('161', plain,
% 6.73/7.00      (![X30 : $i, X31 : $i]:
% 6.73/7.00         (~ (v1_relat_1 @ X30)
% 6.73/7.00          | ~ (v1_funct_1 @ X30)
% 6.73/7.00          | ((k2_funct_1 @ (k5_relat_1 @ X31 @ X30))
% 6.73/7.00              = (k5_relat_1 @ (k2_funct_1 @ X30) @ (k2_funct_1 @ X31)))
% 6.73/7.00          | ~ (v2_funct_1 @ X30)
% 6.73/7.00          | ~ (v2_funct_1 @ X31)
% 6.73/7.00          | ~ (v1_funct_1 @ X31)
% 6.73/7.00          | ~ (v1_relat_1 @ X31))),
% 6.73/7.00      inference('cnf', [status(esa)], [t66_funct_1])).
% 6.73/7.00  thf('162', plain, (((k5_relat_1 @ sk_C @ sk_B) = (sk_B))),
% 6.73/7.00      inference('demod', [status(thm)], ['122', '123'])).
% 6.73/7.00  thf('163', plain,
% 6.73/7.00      (![X30 : $i, X31 : $i]:
% 6.73/7.00         (~ (v1_relat_1 @ X30)
% 6.73/7.00          | ~ (v1_funct_1 @ X30)
% 6.73/7.00          | ((k2_funct_1 @ (k5_relat_1 @ X31 @ X30))
% 6.73/7.00              = (k5_relat_1 @ (k2_funct_1 @ X30) @ (k2_funct_1 @ X31)))
% 6.73/7.00          | ~ (v2_funct_1 @ X30)
% 6.73/7.00          | ~ (v2_funct_1 @ X31)
% 6.73/7.00          | ~ (v1_funct_1 @ X31)
% 6.73/7.00          | ~ (v1_relat_1 @ X31))),
% 6.73/7.00      inference('cnf', [status(esa)], [t66_funct_1])).
% 6.73/7.00  thf('164', plain,
% 6.73/7.00      (![X14 : $i, X15 : $i]:
% 6.73/7.00         (~ (v1_relat_1 @ X14)
% 6.73/7.00          | ((k2_relat_1 @ (k5_relat_1 @ X15 @ X14))
% 6.73/7.00              = (k9_relat_1 @ X14 @ (k2_relat_1 @ X15)))
% 6.73/7.00          | ~ (v1_relat_1 @ X15))),
% 6.73/7.00      inference('cnf', [status(esa)], [t160_relat_1])).
% 6.73/7.00  thf(t21_relat_1, axiom,
% 6.73/7.00    (![A:$i]:
% 6.73/7.00     ( ( v1_relat_1 @ A ) =>
% 6.73/7.00       ( r1_tarski @
% 6.73/7.00         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 6.73/7.00  thf('165', plain,
% 6.73/7.00      (![X18 : $i]:
% 6.73/7.00         ((r1_tarski @ X18 @ 
% 6.73/7.00           (k2_zfmisc_1 @ (k1_relat_1 @ X18) @ (k2_relat_1 @ X18)))
% 6.73/7.00          | ~ (v1_relat_1 @ X18))),
% 6.73/7.00      inference('cnf', [status(esa)], [t21_relat_1])).
% 6.73/7.00  thf('166', plain,
% 6.73/7.00      (![X0 : $i, X1 : $i]:
% 6.73/7.00         ((r1_tarski @ (k5_relat_1 @ X0 @ X1) @ 
% 6.73/7.00           (k2_zfmisc_1 @ (k1_relat_1 @ (k5_relat_1 @ X0 @ X1)) @ 
% 6.73/7.00            (k9_relat_1 @ X1 @ (k2_relat_1 @ X0))))
% 6.73/7.00          | ~ (v1_relat_1 @ X0)
% 6.73/7.00          | ~ (v1_relat_1 @ X1)
% 6.73/7.00          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ X1)))),
% 6.73/7.00      inference('sup+', [status(thm)], ['164', '165'])).
% 6.73/7.00  thf('167', plain,
% 6.73/7.00      (![X0 : $i, X1 : $i]:
% 6.73/7.00         (~ (v1_relat_1 @ (k2_funct_1 @ (k5_relat_1 @ X1 @ X0)))
% 6.73/7.00          | ~ (v1_relat_1 @ X1)
% 6.73/7.00          | ~ (v1_funct_1 @ X1)
% 6.73/7.00          | ~ (v2_funct_1 @ X1)
% 6.73/7.00          | ~ (v2_funct_1 @ X0)
% 6.73/7.00          | ~ (v1_funct_1 @ X0)
% 6.73/7.00          | ~ (v1_relat_1 @ X0)
% 6.73/7.00          | ~ (v1_relat_1 @ (k2_funct_1 @ X1))
% 6.73/7.00          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 6.73/7.00          | (r1_tarski @ 
% 6.73/7.00             (k5_relat_1 @ (k2_funct_1 @ X0) @ (k2_funct_1 @ X1)) @ 
% 6.73/7.00             (k2_zfmisc_1 @ 
% 6.73/7.00              (k1_relat_1 @ 
% 6.73/7.00               (k5_relat_1 @ (k2_funct_1 @ X0) @ (k2_funct_1 @ X1))) @ 
% 6.73/7.00              (k9_relat_1 @ (k2_funct_1 @ X1) @ 
% 6.73/7.00               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 6.73/7.00      inference('sup-', [status(thm)], ['163', '166'])).
% 6.73/7.00  thf('168', plain,
% 6.73/7.00      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 6.73/7.00        | (r1_tarski @ 
% 6.73/7.00           (k5_relat_1 @ (k2_funct_1 @ sk_B) @ (k2_funct_1 @ sk_C)) @ 
% 6.73/7.00           (k2_zfmisc_1 @ 
% 6.73/7.00            (k1_relat_1 @ 
% 6.73/7.00             (k5_relat_1 @ (k2_funct_1 @ sk_B) @ (k2_funct_1 @ sk_C))) @ 
% 6.73/7.00            (k9_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 6.73/7.00             (k2_relat_1 @ (k2_funct_1 @ sk_B)))))
% 6.73/7.00        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 6.73/7.00        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 6.73/7.00        | ~ (v1_relat_1 @ sk_B)
% 6.73/7.00        | ~ (v1_funct_1 @ sk_B)
% 6.73/7.00        | ~ (v2_funct_1 @ sk_B)
% 6.73/7.00        | ~ (v2_funct_1 @ sk_C)
% 6.73/7.00        | ~ (v1_funct_1 @ sk_C)
% 6.73/7.00        | ~ (v1_relat_1 @ sk_C))),
% 6.73/7.00      inference('sup-', [status(thm)], ['162', '167'])).
% 6.73/7.00  thf('169', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 6.73/7.00      inference('demod', [status(thm)], ['54', '55', '56', '59'])).
% 6.73/7.00  thf('170', plain,
% 6.73/7.00      (![X18 : $i]:
% 6.73/7.00         ((r1_tarski @ X18 @ 
% 6.73/7.00           (k2_zfmisc_1 @ (k1_relat_1 @ X18) @ (k2_relat_1 @ X18)))
% 6.73/7.00          | ~ (v1_relat_1 @ X18))),
% 6.73/7.00      inference('cnf', [status(esa)], [t21_relat_1])).
% 6.73/7.00  thf(t3_subset, axiom,
% 6.73/7.00    (![A:$i,B:$i]:
% 6.73/7.00     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 6.73/7.00  thf('171', plain,
% 6.73/7.00      (![X3 : $i, X5 : $i]:
% 6.73/7.00         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 6.73/7.00      inference('cnf', [status(esa)], [t3_subset])).
% 6.73/7.00  thf('172', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         (~ (v1_relat_1 @ X0)
% 6.73/7.00          | (m1_subset_1 @ X0 @ 
% 6.73/7.00             (k1_zfmisc_1 @ 
% 6.73/7.00              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 6.73/7.00      inference('sup-', [status(thm)], ['170', '171'])).
% 6.73/7.00  thf('173', plain,
% 6.73/7.00      (((m1_subset_1 @ sk_B @ 
% 6.73/7.00         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B))))
% 6.73/7.00        | ~ (v1_relat_1 @ sk_B))),
% 6.73/7.00      inference('sup+', [status(thm)], ['169', '172'])).
% 6.73/7.00  thf('174', plain, ((v1_relat_1 @ sk_B)),
% 6.73/7.00      inference('demod', [status(thm)], ['65', '66'])).
% 6.73/7.00  thf('175', plain,
% 6.73/7.00      ((m1_subset_1 @ sk_B @ 
% 6.73/7.00        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B))))),
% 6.73/7.00      inference('demod', [status(thm)], ['173', '174'])).
% 6.73/7.00  thf(t31_funct_2, axiom,
% 6.73/7.00    (![A:$i,B:$i,C:$i]:
% 6.73/7.00     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 6.73/7.00         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.73/7.00       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 6.73/7.00         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 6.73/7.00           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 6.73/7.00           ( m1_subset_1 @
% 6.73/7.00             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 6.73/7.00  thf('176', plain,
% 6.73/7.00      (![X58 : $i, X59 : $i, X60 : $i]:
% 6.73/7.00         (~ (v2_funct_1 @ X58)
% 6.73/7.00          | ((k2_relset_1 @ X60 @ X59 @ X58) != (X59))
% 6.73/7.00          | (m1_subset_1 @ (k2_funct_1 @ X58) @ 
% 6.73/7.00             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X59 @ X60)))
% 6.73/7.00          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X60 @ X59)))
% 6.73/7.00          | ~ (v1_funct_2 @ X58 @ X60 @ X59)
% 6.73/7.00          | ~ (v1_funct_1 @ X58))),
% 6.73/7.00      inference('cnf', [status(esa)], [t31_funct_2])).
% 6.73/7.00  thf('177', plain,
% 6.73/7.00      ((~ (v1_funct_1 @ sk_B)
% 6.73/7.00        | ~ (v1_funct_2 @ sk_B @ sk_A @ (k2_relat_1 @ sk_B))
% 6.73/7.00        | (m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 6.73/7.00           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_B) @ sk_A)))
% 6.73/7.00        | ((k2_relset_1 @ sk_A @ (k2_relat_1 @ sk_B) @ sk_B)
% 6.73/7.00            != (k2_relat_1 @ sk_B))
% 6.73/7.00        | ~ (v2_funct_1 @ sk_B))),
% 6.73/7.00      inference('sup-', [status(thm)], ['175', '176'])).
% 6.73/7.00  thf('178', plain, ((v1_funct_1 @ sk_B)),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('179', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 6.73/7.00      inference('demod', [status(thm)], ['54', '55', '56', '59'])).
% 6.73/7.00  thf(t3_funct_2, axiom,
% 6.73/7.00    (![A:$i]:
% 6.73/7.00     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 6.73/7.00       ( ( v1_funct_1 @ A ) & 
% 6.73/7.00         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 6.73/7.00         ( m1_subset_1 @
% 6.73/7.00           A @ 
% 6.73/7.00           ( k1_zfmisc_1 @
% 6.73/7.00             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 6.73/7.00  thf('180', plain,
% 6.73/7.00      (![X61 : $i]:
% 6.73/7.00         ((v1_funct_2 @ X61 @ (k1_relat_1 @ X61) @ (k2_relat_1 @ X61))
% 6.73/7.00          | ~ (v1_funct_1 @ X61)
% 6.73/7.00          | ~ (v1_relat_1 @ X61))),
% 6.73/7.00      inference('cnf', [status(esa)], [t3_funct_2])).
% 6.73/7.00  thf('181', plain,
% 6.73/7.00      (((v1_funct_2 @ sk_B @ sk_A @ (k2_relat_1 @ sk_B))
% 6.73/7.00        | ~ (v1_relat_1 @ sk_B)
% 6.73/7.00        | ~ (v1_funct_1 @ sk_B))),
% 6.73/7.00      inference('sup+', [status(thm)], ['179', '180'])).
% 6.73/7.00  thf('182', plain, ((v1_relat_1 @ sk_B)),
% 6.73/7.00      inference('demod', [status(thm)], ['65', '66'])).
% 6.73/7.00  thf('183', plain, ((v1_funct_1 @ sk_B)),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('184', plain, ((v1_funct_2 @ sk_B @ sk_A @ (k2_relat_1 @ sk_B))),
% 6.73/7.00      inference('demod', [status(thm)], ['181', '182', '183'])).
% 6.73/7.00  thf('185', plain,
% 6.73/7.00      ((m1_subset_1 @ sk_B @ 
% 6.73/7.00        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B))))),
% 6.73/7.00      inference('demod', [status(thm)], ['173', '174'])).
% 6.73/7.00  thf(redefinition_k2_relset_1, axiom,
% 6.73/7.00    (![A:$i,B:$i,C:$i]:
% 6.73/7.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.73/7.00       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 6.73/7.00  thf('186', plain,
% 6.73/7.00      (![X38 : $i, X39 : $i, X40 : $i]:
% 6.73/7.00         (((k2_relset_1 @ X39 @ X40 @ X38) = (k2_relat_1 @ X38))
% 6.73/7.00          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40))))),
% 6.73/7.00      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 6.73/7.00  thf('187', plain,
% 6.73/7.00      (((k2_relset_1 @ sk_A @ (k2_relat_1 @ sk_B) @ sk_B) = (k2_relat_1 @ sk_B))),
% 6.73/7.00      inference('sup-', [status(thm)], ['185', '186'])).
% 6.73/7.00  thf('188', plain, ((v2_funct_1 @ sk_B)),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('189', plain,
% 6.73/7.00      (((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 6.73/7.00         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_B) @ sk_A)))
% 6.73/7.00        | ((k2_relat_1 @ sk_B) != (k2_relat_1 @ sk_B)))),
% 6.73/7.00      inference('demod', [status(thm)], ['177', '178', '184', '187', '188'])).
% 6.73/7.00  thf('190', plain,
% 6.73/7.00      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 6.73/7.00        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_B) @ sk_A)))),
% 6.73/7.00      inference('simplify', [status(thm)], ['189'])).
% 6.73/7.00  thf('191', plain,
% 6.73/7.00      (![X6 : $i, X7 : $i]:
% 6.73/7.00         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 6.73/7.00          | (v1_relat_1 @ X6)
% 6.73/7.00          | ~ (v1_relat_1 @ X7))),
% 6.73/7.00      inference('cnf', [status(esa)], [cc2_relat_1])).
% 6.73/7.00  thf('192', plain,
% 6.73/7.00      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_B) @ sk_A))
% 6.73/7.00        | (v1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 6.73/7.00      inference('sup-', [status(thm)], ['190', '191'])).
% 6.73/7.00  thf('193', plain,
% 6.73/7.00      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 6.73/7.00      inference('cnf', [status(esa)], [fc6_relat_1])).
% 6.73/7.00  thf('194', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 6.73/7.00      inference('demod', [status(thm)], ['192', '193'])).
% 6.73/7.00  thf('195', plain,
% 6.73/7.00      (![X28 : $i]:
% 6.73/7.00         (~ (v2_funct_1 @ X28)
% 6.73/7.00          | ((k1_relat_1 @ X28) = (k2_relat_1 @ (k2_funct_1 @ X28)))
% 6.73/7.00          | ~ (v1_funct_1 @ X28)
% 6.73/7.00          | ~ (v1_relat_1 @ X28))),
% 6.73/7.00      inference('cnf', [status(esa)], [t55_funct_1])).
% 6.73/7.00  thf('196', plain,
% 6.73/7.00      (![X21 : $i]:
% 6.73/7.00         ((v1_relat_1 @ (k2_funct_1 @ X21))
% 6.73/7.00          | ~ (v1_funct_1 @ X21)
% 6.73/7.00          | ~ (v1_relat_1 @ X21))),
% 6.73/7.00      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.73/7.00  thf('197', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 6.73/7.00      inference('demod', [status(thm)], ['54', '55', '56', '59'])).
% 6.73/7.00  thf('198', plain,
% 6.73/7.00      (![X21 : $i]:
% 6.73/7.00         ((v1_relat_1 @ (k2_funct_1 @ X21))
% 6.73/7.00          | ~ (v1_funct_1 @ X21)
% 6.73/7.00          | ~ (v1_relat_1 @ X21))),
% 6.73/7.00      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.73/7.00  thf('199', plain,
% 6.73/7.00      (![X28 : $i]:
% 6.73/7.00         (~ (v2_funct_1 @ X28)
% 6.73/7.00          | ((k1_relat_1 @ X28) = (k2_relat_1 @ (k2_funct_1 @ X28)))
% 6.73/7.00          | ~ (v1_funct_1 @ X28)
% 6.73/7.00          | ~ (v1_relat_1 @ X28))),
% 6.73/7.00      inference('cnf', [status(esa)], [t55_funct_1])).
% 6.73/7.00  thf('200', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         (~ (v1_relat_1 @ X0)
% 6.73/7.00          | (m1_subset_1 @ X0 @ 
% 6.73/7.00             (k1_zfmisc_1 @ 
% 6.73/7.00              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 6.73/7.00      inference('sup-', [status(thm)], ['170', '171'])).
% 6.73/7.00  thf('201', plain,
% 6.73/7.00      (![X32 : $i, X33 : $i, X34 : $i]:
% 6.73/7.00         ((v5_relat_1 @ X32 @ X34)
% 6.73/7.00          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 6.73/7.00      inference('cnf', [status(esa)], [cc2_relset_1])).
% 6.73/7.00  thf('202', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 6.73/7.00      inference('sup-', [status(thm)], ['200', '201'])).
% 6.73/7.00  thf('203', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         ((v5_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0))
% 6.73/7.00          | ~ (v1_relat_1 @ X0)
% 6.73/7.00          | ~ (v1_funct_1 @ X0)
% 6.73/7.00          | ~ (v2_funct_1 @ X0)
% 6.73/7.00          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 6.73/7.00      inference('sup+', [status(thm)], ['199', '202'])).
% 6.73/7.00  thf('204', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         (~ (v1_relat_1 @ X0)
% 6.73/7.00          | ~ (v1_funct_1 @ X0)
% 6.73/7.00          | ~ (v2_funct_1 @ X0)
% 6.73/7.00          | ~ (v1_funct_1 @ X0)
% 6.73/7.00          | ~ (v1_relat_1 @ X0)
% 6.73/7.00          | (v5_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0)))),
% 6.73/7.00      inference('sup-', [status(thm)], ['198', '203'])).
% 6.73/7.00  thf('205', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         ((v5_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0))
% 6.73/7.00          | ~ (v2_funct_1 @ X0)
% 6.73/7.00          | ~ (v1_funct_1 @ X0)
% 6.73/7.00          | ~ (v1_relat_1 @ X0))),
% 6.73/7.00      inference('simplify', [status(thm)], ['204'])).
% 6.73/7.00  thf('206', plain,
% 6.73/7.00      (((v5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)
% 6.73/7.00        | ~ (v1_relat_1 @ sk_B)
% 6.73/7.00        | ~ (v1_funct_1 @ sk_B)
% 6.73/7.00        | ~ (v2_funct_1 @ sk_B))),
% 6.73/7.00      inference('sup+', [status(thm)], ['197', '205'])).
% 6.73/7.00  thf('207', plain, ((v1_relat_1 @ sk_B)),
% 6.73/7.00      inference('demod', [status(thm)], ['65', '66'])).
% 6.73/7.00  thf('208', plain, ((v1_funct_1 @ sk_B)),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('209', plain, ((v2_funct_1 @ sk_B)),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('210', plain, ((v5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)),
% 6.73/7.00      inference('demod', [status(thm)], ['206', '207', '208', '209'])).
% 6.73/7.00  thf('211', plain,
% 6.73/7.00      (![X8 : $i, X9 : $i]:
% 6.73/7.00         (~ (v5_relat_1 @ X8 @ X9)
% 6.73/7.00          | (r1_tarski @ (k2_relat_1 @ X8) @ X9)
% 6.73/7.00          | ~ (v1_relat_1 @ X8))),
% 6.73/7.00      inference('cnf', [status(esa)], [d19_relat_1])).
% 6.73/7.00  thf('212', plain,
% 6.73/7.00      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 6.73/7.00        | (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_B)) @ sk_A))),
% 6.73/7.00      inference('sup-', [status(thm)], ['210', '211'])).
% 6.73/7.00  thf('213', plain,
% 6.73/7.00      ((~ (v1_relat_1 @ sk_B)
% 6.73/7.00        | ~ (v1_funct_1 @ sk_B)
% 6.73/7.00        | (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_B)) @ sk_A))),
% 6.73/7.00      inference('sup-', [status(thm)], ['196', '212'])).
% 6.73/7.00  thf('214', plain, ((v1_relat_1 @ sk_B)),
% 6.73/7.00      inference('demod', [status(thm)], ['65', '66'])).
% 6.73/7.00  thf('215', plain, ((v1_funct_1 @ sk_B)),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('216', plain, ((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_B)) @ sk_A)),
% 6.73/7.00      inference('demod', [status(thm)], ['213', '214', '215'])).
% 6.73/7.00  thf('217', plain,
% 6.73/7.00      (![X0 : $i, X2 : $i]:
% 6.73/7.00         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 6.73/7.00      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.73/7.00  thf('218', plain,
% 6.73/7.00      ((~ (r1_tarski @ sk_A @ (k2_relat_1 @ (k2_funct_1 @ sk_B)))
% 6.73/7.00        | ((sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_B))))),
% 6.73/7.00      inference('sup-', [status(thm)], ['216', '217'])).
% 6.73/7.00  thf('219', plain,
% 6.73/7.00      ((~ (r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))
% 6.73/7.00        | ~ (v1_relat_1 @ sk_B)
% 6.73/7.00        | ~ (v1_funct_1 @ sk_B)
% 6.73/7.00        | ~ (v2_funct_1 @ sk_B)
% 6.73/7.00        | ((sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_B))))),
% 6.73/7.00      inference('sup-', [status(thm)], ['195', '218'])).
% 6.73/7.00  thf('220', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 6.73/7.00      inference('demod', [status(thm)], ['54', '55', '56', '59'])).
% 6.73/7.00  thf('221', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 6.73/7.00      inference('simplify', [status(thm)], ['127'])).
% 6.73/7.00  thf('222', plain, ((v1_relat_1 @ sk_B)),
% 6.73/7.00      inference('demod', [status(thm)], ['65', '66'])).
% 6.73/7.00  thf('223', plain, ((v1_funct_1 @ sk_B)),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('224', plain, ((v2_funct_1 @ sk_B)),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('225', plain, (((sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_B)))),
% 6.73/7.00      inference('demod', [status(thm)],
% 6.73/7.00                ['219', '220', '221', '222', '223', '224'])).
% 6.73/7.00  thf('226', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 6.73/7.00      inference('sup+', [status(thm)], ['126', '142'])).
% 6.73/7.00  thf('227', plain,
% 6.73/7.00      (![X21 : $i]:
% 6.73/7.00         ((v1_relat_1 @ (k2_funct_1 @ X21))
% 6.73/7.00          | ~ (v1_funct_1 @ X21)
% 6.73/7.00          | ~ (v1_relat_1 @ X21))),
% 6.73/7.00      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.73/7.00  thf('228', plain,
% 6.73/7.00      (![X29 : $i]:
% 6.73/7.00         (~ (v2_funct_1 @ X29)
% 6.73/7.00          | ((k5_relat_1 @ X29 @ (k2_funct_1 @ X29))
% 6.73/7.00              = (k6_relat_1 @ (k1_relat_1 @ X29)))
% 6.73/7.00          | ~ (v1_funct_1 @ X29)
% 6.73/7.00          | ~ (v1_relat_1 @ X29))),
% 6.73/7.00      inference('cnf', [status(esa)], [t61_funct_1])).
% 6.73/7.00  thf('229', plain, (![X57 : $i]: ((k6_partfun1 @ X57) = (k6_relat_1 @ X57))),
% 6.73/7.00      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 6.73/7.00  thf('230', plain,
% 6.73/7.00      (![X29 : $i]:
% 6.73/7.00         (~ (v2_funct_1 @ X29)
% 6.73/7.00          | ((k5_relat_1 @ X29 @ (k2_funct_1 @ X29))
% 6.73/7.00              = (k6_partfun1 @ (k1_relat_1 @ X29)))
% 6.73/7.00          | ~ (v1_funct_1 @ X29)
% 6.73/7.00          | ~ (v1_relat_1 @ X29))),
% 6.73/7.00      inference('demod', [status(thm)], ['228', '229'])).
% 6.73/7.00  thf('231', plain,
% 6.73/7.00      (![X14 : $i, X15 : $i]:
% 6.73/7.00         (~ (v1_relat_1 @ X14)
% 6.73/7.00          | ((k2_relat_1 @ (k5_relat_1 @ X15 @ X14))
% 6.73/7.00              = (k9_relat_1 @ X14 @ (k2_relat_1 @ X15)))
% 6.73/7.00          | ~ (v1_relat_1 @ X15))),
% 6.73/7.00      inference('cnf', [status(esa)], [t160_relat_1])).
% 6.73/7.00  thf('232', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         (((k2_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 6.73/7.00            = (k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))
% 6.73/7.00          | ~ (v1_relat_1 @ X0)
% 6.73/7.00          | ~ (v1_funct_1 @ X0)
% 6.73/7.00          | ~ (v2_funct_1 @ X0)
% 6.73/7.00          | ~ (v1_relat_1 @ X0)
% 6.73/7.00          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 6.73/7.00      inference('sup+', [status(thm)], ['230', '231'])).
% 6.73/7.00  thf(t71_relat_1, axiom,
% 6.73/7.00    (![A:$i]:
% 6.73/7.00     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 6.73/7.00       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 6.73/7.00  thf('233', plain, (![X20 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X20)) = (X20))),
% 6.73/7.00      inference('cnf', [status(esa)], [t71_relat_1])).
% 6.73/7.00  thf('234', plain, (![X57 : $i]: ((k6_partfun1 @ X57) = (k6_relat_1 @ X57))),
% 6.73/7.00      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 6.73/7.00  thf('235', plain,
% 6.73/7.00      (![X20 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X20)) = (X20))),
% 6.73/7.00      inference('demod', [status(thm)], ['233', '234'])).
% 6.73/7.00  thf('236', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         (((k1_relat_1 @ X0)
% 6.73/7.00            = (k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))
% 6.73/7.00          | ~ (v1_relat_1 @ X0)
% 6.73/7.00          | ~ (v1_funct_1 @ X0)
% 6.73/7.00          | ~ (v2_funct_1 @ X0)
% 6.73/7.00          | ~ (v1_relat_1 @ X0)
% 6.73/7.00          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 6.73/7.00      inference('demod', [status(thm)], ['232', '235'])).
% 6.73/7.00  thf('237', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 6.73/7.00          | ~ (v2_funct_1 @ X0)
% 6.73/7.00          | ~ (v1_funct_1 @ X0)
% 6.73/7.00          | ~ (v1_relat_1 @ X0)
% 6.73/7.00          | ((k1_relat_1 @ X0)
% 6.73/7.00              = (k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))))),
% 6.73/7.00      inference('simplify', [status(thm)], ['236'])).
% 6.73/7.00  thf('238', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         (~ (v1_relat_1 @ X0)
% 6.73/7.00          | ~ (v1_funct_1 @ X0)
% 6.73/7.00          | ((k1_relat_1 @ X0)
% 6.73/7.00              = (k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))
% 6.73/7.00          | ~ (v1_relat_1 @ X0)
% 6.73/7.00          | ~ (v1_funct_1 @ X0)
% 6.73/7.00          | ~ (v2_funct_1 @ X0))),
% 6.73/7.00      inference('sup-', [status(thm)], ['227', '237'])).
% 6.73/7.00  thf('239', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         (~ (v2_funct_1 @ X0)
% 6.73/7.00          | ((k1_relat_1 @ X0)
% 6.73/7.00              = (k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))
% 6.73/7.00          | ~ (v1_funct_1 @ X0)
% 6.73/7.00          | ~ (v1_relat_1 @ X0))),
% 6.73/7.00      inference('simplify', [status(thm)], ['238'])).
% 6.73/7.00  thf('240', plain,
% 6.73/7.00      ((((k1_relat_1 @ sk_C) = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A))
% 6.73/7.00        | ~ (v1_relat_1 @ sk_C)
% 6.73/7.00        | ~ (v1_funct_1 @ sk_C)
% 6.73/7.00        | ~ (v2_funct_1 @ sk_C))),
% 6.73/7.00      inference('sup+', [status(thm)], ['226', '239'])).
% 6.73/7.00  thf('241', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 6.73/7.00      inference('demod', [status(thm)], ['9', '10', '11', '14'])).
% 6.73/7.00  thf('242', plain, ((v1_relat_1 @ sk_C)),
% 6.73/7.00      inference('demod', [status(thm)], ['24', '25'])).
% 6.73/7.00  thf('243', plain, ((v1_funct_1 @ sk_C)),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('244', plain,
% 6.73/7.00      ((((sk_A) = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A))
% 6.73/7.00        | ~ (v2_funct_1 @ sk_C))),
% 6.73/7.00      inference('demod', [status(thm)], ['240', '241', '242', '243'])).
% 6.73/7.00  thf('245', plain, ((v2_funct_1 @ sk_C)),
% 6.73/7.00      inference('simplify', [status(thm)], ['156'])).
% 6.73/7.00  thf('246', plain, (((sk_A) = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A))),
% 6.73/7.00      inference('demod', [status(thm)], ['244', '245'])).
% 6.73/7.00  thf('247', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 6.73/7.00      inference('demod', [status(thm)], ['192', '193'])).
% 6.73/7.00  thf('248', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 6.73/7.00      inference('demod', [status(thm)], ['9', '10', '11', '14'])).
% 6.73/7.00  thf('249', plain,
% 6.73/7.00      (![X21 : $i]:
% 6.73/7.00         ((v1_relat_1 @ (k2_funct_1 @ X21))
% 6.73/7.00          | ~ (v1_funct_1 @ X21)
% 6.73/7.00          | ~ (v1_relat_1 @ X21))),
% 6.73/7.00      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.73/7.00  thf('250', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         (~ (v1_relat_1 @ X0)
% 6.73/7.00          | (m1_subset_1 @ X0 @ 
% 6.73/7.00             (k1_zfmisc_1 @ 
% 6.73/7.00              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 6.73/7.00      inference('sup-', [status(thm)], ['170', '171'])).
% 6.73/7.00  thf('251', plain,
% 6.73/7.00      (![X32 : $i, X33 : $i, X34 : $i]:
% 6.73/7.00         ((v4_relat_1 @ X32 @ X33)
% 6.73/7.00          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 6.73/7.00      inference('cnf', [status(esa)], [cc2_relset_1])).
% 6.73/7.00  thf('252', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 6.73/7.00      inference('sup-', [status(thm)], ['250', '251'])).
% 6.73/7.00  thf('253', plain,
% 6.73/7.00      (![X16 : $i, X17 : $i]:
% 6.73/7.00         (((X16) = (k7_relat_1 @ X16 @ X17))
% 6.73/7.00          | ~ (v4_relat_1 @ X16 @ X17)
% 6.73/7.00          | ~ (v1_relat_1 @ X16))),
% 6.73/7.00      inference('cnf', [status(esa)], [t209_relat_1])).
% 6.73/7.00  thf('254', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         (~ (v1_relat_1 @ X0)
% 6.73/7.00          | ~ (v1_relat_1 @ X0)
% 6.73/7.00          | ((X0) = (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 6.73/7.00      inference('sup-', [status(thm)], ['252', '253'])).
% 6.73/7.00  thf('255', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         (((X0) = (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))) | ~ (v1_relat_1 @ X0))),
% 6.73/7.00      inference('simplify', [status(thm)], ['254'])).
% 6.73/7.00  thf('256', plain,
% 6.73/7.00      (![X12 : $i, X13 : $i]:
% 6.73/7.00         (((k2_relat_1 @ (k7_relat_1 @ X12 @ X13)) = (k9_relat_1 @ X12 @ X13))
% 6.73/7.00          | ~ (v1_relat_1 @ X12))),
% 6.73/7.00      inference('cnf', [status(esa)], [t148_relat_1])).
% 6.73/7.00  thf('257', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         (((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 6.73/7.00          | ~ (v1_relat_1 @ X0)
% 6.73/7.00          | ~ (v1_relat_1 @ X0))),
% 6.73/7.00      inference('sup+', [status(thm)], ['255', '256'])).
% 6.73/7.00  thf('258', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         (~ (v1_relat_1 @ X0)
% 6.73/7.00          | ((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 6.73/7.00      inference('simplify', [status(thm)], ['257'])).
% 6.73/7.00  thf('259', plain,
% 6.73/7.00      (![X21 : $i]:
% 6.73/7.00         ((v1_relat_1 @ (k2_funct_1 @ X21))
% 6.73/7.00          | ~ (v1_funct_1 @ X21)
% 6.73/7.00          | ~ (v1_relat_1 @ X21))),
% 6.73/7.00      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.73/7.00  thf('260', plain,
% 6.73/7.00      (![X28 : $i]:
% 6.73/7.00         (~ (v2_funct_1 @ X28)
% 6.73/7.00          | ((k1_relat_1 @ X28) = (k2_relat_1 @ (k2_funct_1 @ X28)))
% 6.73/7.00          | ~ (v1_funct_1 @ X28)
% 6.73/7.00          | ~ (v1_relat_1 @ X28))),
% 6.73/7.00      inference('cnf', [status(esa)], [t55_funct_1])).
% 6.73/7.00  thf('261', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         (((X0) = (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))) | ~ (v1_relat_1 @ X0))),
% 6.73/7.00      inference('simplify', [status(thm)], ['254'])).
% 6.73/7.00  thf('262', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         (((X0) = (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))) | ~ (v1_relat_1 @ X0))),
% 6.73/7.00      inference('simplify', [status(thm)], ['254'])).
% 6.73/7.00  thf('263', plain,
% 6.73/7.00      (![X12 : $i, X13 : $i]:
% 6.73/7.00         (((k2_relat_1 @ (k7_relat_1 @ X12 @ X13)) = (k9_relat_1 @ X12 @ X13))
% 6.73/7.00          | ~ (v1_relat_1 @ X12))),
% 6.73/7.00      inference('cnf', [status(esa)], [t148_relat_1])).
% 6.73/7.00  thf('264', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 6.73/7.00      inference('sup-', [status(thm)], ['200', '201'])).
% 6.73/7.00  thf('265', plain,
% 6.73/7.00      (![X0 : $i, X1 : $i]:
% 6.73/7.00         ((v5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 6.73/7.00          | ~ (v1_relat_1 @ X1)
% 6.73/7.00          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 6.73/7.00      inference('sup+', [status(thm)], ['263', '264'])).
% 6.73/7.00  thf('266', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         (~ (v1_relat_1 @ X0)
% 6.73/7.00          | ~ (v1_relat_1 @ X0)
% 6.73/7.00          | ~ (v1_relat_1 @ X0)
% 6.73/7.00          | (v5_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) @ 
% 6.73/7.00             (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 6.73/7.00      inference('sup-', [status(thm)], ['262', '265'])).
% 6.73/7.00  thf('267', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         ((v5_relat_1 @ (k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) @ 
% 6.73/7.00           (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 6.73/7.00          | ~ (v1_relat_1 @ X0))),
% 6.73/7.00      inference('simplify', [status(thm)], ['266'])).
% 6.73/7.00  thf('268', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         ((v5_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 6.73/7.00          | ~ (v1_relat_1 @ X0)
% 6.73/7.00          | ~ (v1_relat_1 @ X0))),
% 6.73/7.00      inference('sup+', [status(thm)], ['261', '267'])).
% 6.73/7.00  thf('269', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         (~ (v1_relat_1 @ X0)
% 6.73/7.00          | (v5_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 6.73/7.00      inference('simplify', [status(thm)], ['268'])).
% 6.73/7.00  thf('270', plain,
% 6.73/7.00      (![X8 : $i, X9 : $i]:
% 6.73/7.00         (~ (v5_relat_1 @ X8 @ X9)
% 6.73/7.00          | (r1_tarski @ (k2_relat_1 @ X8) @ X9)
% 6.73/7.00          | ~ (v1_relat_1 @ X8))),
% 6.73/7.00      inference('cnf', [status(esa)], [d19_relat_1])).
% 6.73/7.00  thf('271', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         (~ (v1_relat_1 @ X0)
% 6.73/7.00          | ~ (v1_relat_1 @ X0)
% 6.73/7.00          | (r1_tarski @ (k2_relat_1 @ X0) @ 
% 6.73/7.00             (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 6.73/7.00      inference('sup-', [status(thm)], ['269', '270'])).
% 6.73/7.00  thf('272', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         ((r1_tarski @ (k2_relat_1 @ X0) @ 
% 6.73/7.00           (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 6.73/7.00          | ~ (v1_relat_1 @ X0))),
% 6.73/7.00      inference('simplify', [status(thm)], ['271'])).
% 6.73/7.00  thf('273', plain,
% 6.73/7.00      (![X3 : $i, X5 : $i]:
% 6.73/7.00         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 6.73/7.00      inference('cnf', [status(esa)], [t3_subset])).
% 6.73/7.00  thf('274', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         (~ (v1_relat_1 @ X0)
% 6.73/7.00          | (m1_subset_1 @ (k2_relat_1 @ X0) @ 
% 6.73/7.00             (k1_zfmisc_1 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))))),
% 6.73/7.00      inference('sup-', [status(thm)], ['272', '273'])).
% 6.73/7.00  thf('275', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         ((m1_subset_1 @ (k1_relat_1 @ X0) @ 
% 6.73/7.00           (k1_zfmisc_1 @ 
% 6.73/7.00            (k9_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))))
% 6.73/7.00          | ~ (v1_relat_1 @ X0)
% 6.73/7.00          | ~ (v1_funct_1 @ X0)
% 6.73/7.00          | ~ (v2_funct_1 @ X0)
% 6.73/7.00          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 6.73/7.00      inference('sup+', [status(thm)], ['260', '274'])).
% 6.73/7.00  thf('276', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         (~ (v1_relat_1 @ X0)
% 6.73/7.00          | ~ (v1_funct_1 @ X0)
% 6.73/7.00          | ~ (v2_funct_1 @ X0)
% 6.73/7.00          | ~ (v1_funct_1 @ X0)
% 6.73/7.00          | ~ (v1_relat_1 @ X0)
% 6.73/7.00          | (m1_subset_1 @ (k1_relat_1 @ X0) @ 
% 6.73/7.00             (k1_zfmisc_1 @ 
% 6.73/7.00              (k9_relat_1 @ (k2_funct_1 @ X0) @ 
% 6.73/7.00               (k1_relat_1 @ (k2_funct_1 @ X0))))))),
% 6.73/7.00      inference('sup-', [status(thm)], ['259', '275'])).
% 6.73/7.00  thf('277', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         ((m1_subset_1 @ (k1_relat_1 @ X0) @ 
% 6.73/7.00           (k1_zfmisc_1 @ 
% 6.73/7.00            (k9_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))))
% 6.73/7.00          | ~ (v2_funct_1 @ X0)
% 6.73/7.00          | ~ (v1_funct_1 @ X0)
% 6.73/7.00          | ~ (v1_relat_1 @ X0))),
% 6.73/7.00      inference('simplify', [status(thm)], ['276'])).
% 6.73/7.00  thf('278', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         ((m1_subset_1 @ (k1_relat_1 @ X0) @ 
% 6.73/7.00           (k1_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 6.73/7.00          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 6.73/7.00          | ~ (v1_relat_1 @ X0)
% 6.73/7.00          | ~ (v1_funct_1 @ X0)
% 6.73/7.00          | ~ (v2_funct_1 @ X0))),
% 6.73/7.00      inference('sup+', [status(thm)], ['258', '277'])).
% 6.73/7.00  thf('279', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         (~ (v1_relat_1 @ X0)
% 6.73/7.00          | ~ (v1_funct_1 @ X0)
% 6.73/7.00          | ~ (v2_funct_1 @ X0)
% 6.73/7.00          | ~ (v1_funct_1 @ X0)
% 6.73/7.00          | ~ (v1_relat_1 @ X0)
% 6.73/7.00          | (m1_subset_1 @ (k1_relat_1 @ X0) @ 
% 6.73/7.00             (k1_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 6.73/7.00      inference('sup-', [status(thm)], ['249', '278'])).
% 6.73/7.00  thf('280', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         ((m1_subset_1 @ (k1_relat_1 @ X0) @ 
% 6.73/7.00           (k1_zfmisc_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 6.73/7.00          | ~ (v2_funct_1 @ X0)
% 6.73/7.00          | ~ (v1_funct_1 @ X0)
% 6.73/7.00          | ~ (v1_relat_1 @ X0))),
% 6.73/7.00      inference('simplify', [status(thm)], ['279'])).
% 6.73/7.00  thf('281', plain,
% 6.73/7.00      (![X3 : $i, X4 : $i]:
% 6.73/7.00         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 6.73/7.00      inference('cnf', [status(esa)], [t3_subset])).
% 6.73/7.00  thf('282', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         (~ (v1_relat_1 @ X0)
% 6.73/7.00          | ~ (v1_funct_1 @ X0)
% 6.73/7.00          | ~ (v2_funct_1 @ X0)
% 6.73/7.00          | (r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 6.73/7.00      inference('sup-', [status(thm)], ['280', '281'])).
% 6.73/7.00  thf('283', plain,
% 6.73/7.00      (((r1_tarski @ sk_A @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 6.73/7.00        | ~ (v2_funct_1 @ sk_C)
% 6.73/7.00        | ~ (v1_funct_1 @ sk_C)
% 6.73/7.00        | ~ (v1_relat_1 @ sk_C))),
% 6.73/7.00      inference('sup+', [status(thm)], ['248', '282'])).
% 6.73/7.00  thf('284', plain, ((v1_funct_1 @ sk_C)),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('285', plain, ((v1_relat_1 @ sk_C)),
% 6.73/7.00      inference('demod', [status(thm)], ['24', '25'])).
% 6.73/7.00  thf('286', plain,
% 6.73/7.00      (((r1_tarski @ sk_A @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 6.73/7.00        | ~ (v2_funct_1 @ sk_C))),
% 6.73/7.00      inference('demod', [status(thm)], ['283', '284', '285'])).
% 6.73/7.00  thf('287', plain, ((v2_funct_1 @ sk_C)),
% 6.73/7.00      inference('simplify', [status(thm)], ['156'])).
% 6.73/7.00  thf('288', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 6.73/7.00      inference('demod', [status(thm)], ['286', '287'])).
% 6.73/7.00  thf('289', plain,
% 6.73/7.00      (![X0 : $i, X2 : $i]:
% 6.73/7.00         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 6.73/7.00      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.73/7.00  thf('290', plain,
% 6.73/7.00      ((~ (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)
% 6.73/7.00        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_A)))),
% 6.73/7.00      inference('sup-', [status(thm)], ['288', '289'])).
% 6.73/7.00  thf('291', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 6.73/7.00      inference('demod', [status(thm)], ['9', '10', '11', '14'])).
% 6.73/7.00  thf('292', plain,
% 6.73/7.00      (![X21 : $i]:
% 6.73/7.00         ((v1_relat_1 @ (k2_funct_1 @ X21))
% 6.73/7.00          | ~ (v1_funct_1 @ X21)
% 6.73/7.00          | ~ (v1_relat_1 @ X21))),
% 6.73/7.00      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.73/7.00  thf('293', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         ((v5_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0))
% 6.73/7.00          | ~ (v2_funct_1 @ X0)
% 6.73/7.00          | ~ (v1_funct_1 @ X0)
% 6.73/7.00          | ~ (v1_relat_1 @ X0))),
% 6.73/7.00      inference('simplify', [status(thm)], ['204'])).
% 6.73/7.00  thf('294', plain,
% 6.73/7.00      (![X8 : $i, X9 : $i]:
% 6.73/7.00         (~ (v5_relat_1 @ X8 @ X9)
% 6.73/7.00          | (r1_tarski @ (k2_relat_1 @ X8) @ X9)
% 6.73/7.00          | ~ (v1_relat_1 @ X8))),
% 6.73/7.00      inference('cnf', [status(esa)], [d19_relat_1])).
% 6.73/7.00  thf('295', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         (~ (v1_relat_1 @ X0)
% 6.73/7.00          | ~ (v1_funct_1 @ X0)
% 6.73/7.00          | ~ (v2_funct_1 @ X0)
% 6.73/7.00          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 6.73/7.00          | (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 6.73/7.00      inference('sup-', [status(thm)], ['293', '294'])).
% 6.73/7.00  thf('296', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         (~ (v1_relat_1 @ X0)
% 6.73/7.00          | ~ (v1_funct_1 @ X0)
% 6.73/7.00          | (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 6.73/7.00          | ~ (v2_funct_1 @ X0)
% 6.73/7.00          | ~ (v1_funct_1 @ X0)
% 6.73/7.00          | ~ (v1_relat_1 @ X0))),
% 6.73/7.00      inference('sup-', [status(thm)], ['292', '295'])).
% 6.73/7.00  thf('297', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         (~ (v2_funct_1 @ X0)
% 6.73/7.00          | (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 6.73/7.00          | ~ (v1_funct_1 @ X0)
% 6.73/7.00          | ~ (v1_relat_1 @ X0))),
% 6.73/7.00      inference('simplify', [status(thm)], ['296'])).
% 6.73/7.00  thf('298', plain,
% 6.73/7.00      (((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)
% 6.73/7.00        | ~ (v1_relat_1 @ sk_C)
% 6.73/7.00        | ~ (v1_funct_1 @ sk_C)
% 6.73/7.00        | ~ (v2_funct_1 @ sk_C))),
% 6.73/7.00      inference('sup+', [status(thm)], ['291', '297'])).
% 6.73/7.00  thf('299', plain, ((v1_relat_1 @ sk_C)),
% 6.73/7.00      inference('demod', [status(thm)], ['24', '25'])).
% 6.73/7.00  thf('300', plain, ((v1_funct_1 @ sk_C)),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('301', plain,
% 6.73/7.00      (((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)
% 6.73/7.00        | ~ (v2_funct_1 @ sk_C))),
% 6.73/7.00      inference('demod', [status(thm)], ['298', '299', '300'])).
% 6.73/7.00  thf('302', plain, ((v2_funct_1 @ sk_C)),
% 6.73/7.00      inference('simplify', [status(thm)], ['156'])).
% 6.73/7.00  thf('303', plain, ((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)),
% 6.73/7.00      inference('demod', [status(thm)], ['301', '302'])).
% 6.73/7.00  thf('304', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_A))),
% 6.73/7.00      inference('demod', [status(thm)], ['290', '303'])).
% 6.73/7.00  thf('305', plain,
% 6.73/7.00      (![X21 : $i]:
% 6.73/7.00         ((v1_relat_1 @ (k2_funct_1 @ X21))
% 6.73/7.00          | ~ (v1_funct_1 @ X21)
% 6.73/7.00          | ~ (v1_relat_1 @ X21))),
% 6.73/7.00      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.73/7.00  thf('306', plain,
% 6.73/7.00      (![X28 : $i]:
% 6.73/7.00         (~ (v2_funct_1 @ X28)
% 6.73/7.00          | ((k2_relat_1 @ X28) = (k1_relat_1 @ (k2_funct_1 @ X28)))
% 6.73/7.00          | ~ (v1_funct_1 @ X28)
% 6.73/7.00          | ~ (v1_relat_1 @ X28))),
% 6.73/7.00      inference('cnf', [status(esa)], [t55_funct_1])).
% 6.73/7.00  thf('307', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         (~ (v1_relat_1 @ X0)
% 6.73/7.00          | (m1_subset_1 @ X0 @ 
% 6.73/7.00             (k1_zfmisc_1 @ 
% 6.73/7.00              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 6.73/7.00      inference('sup-', [status(thm)], ['170', '171'])).
% 6.73/7.00  thf('308', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 6.73/7.00           (k1_zfmisc_1 @ 
% 6.73/7.00            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 6.73/7.00          | ~ (v1_relat_1 @ X0)
% 6.73/7.00          | ~ (v1_funct_1 @ X0)
% 6.73/7.00          | ~ (v2_funct_1 @ X0)
% 6.73/7.00          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 6.73/7.00      inference('sup+', [status(thm)], ['306', '307'])).
% 6.73/7.00  thf('309', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         (~ (v1_relat_1 @ X0)
% 6.73/7.00          | ~ (v1_funct_1 @ X0)
% 6.73/7.00          | ~ (v2_funct_1 @ X0)
% 6.73/7.00          | ~ (v1_funct_1 @ X0)
% 6.73/7.00          | ~ (v1_relat_1 @ X0)
% 6.73/7.00          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 6.73/7.00             (k1_zfmisc_1 @ 
% 6.73/7.00              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 6.73/7.00               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 6.73/7.00      inference('sup-', [status(thm)], ['305', '308'])).
% 6.73/7.00  thf('310', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 6.73/7.00           (k1_zfmisc_1 @ 
% 6.73/7.00            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 6.73/7.00          | ~ (v2_funct_1 @ X0)
% 6.73/7.00          | ~ (v1_funct_1 @ X0)
% 6.73/7.00          | ~ (v1_relat_1 @ X0))),
% 6.73/7.00      inference('simplify', [status(thm)], ['309'])).
% 6.73/7.00  thf('311', plain,
% 6.73/7.00      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.73/7.00         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ sk_A)))
% 6.73/7.00        | ~ (v1_relat_1 @ sk_C)
% 6.73/7.00        | ~ (v1_funct_1 @ sk_C)
% 6.73/7.00        | ~ (v2_funct_1 @ sk_C))),
% 6.73/7.00      inference('sup+', [status(thm)], ['304', '310'])).
% 6.73/7.00  thf('312', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 6.73/7.00      inference('sup+', [status(thm)], ['126', '142'])).
% 6.73/7.00  thf('313', plain, ((v1_relat_1 @ sk_C)),
% 6.73/7.00      inference('demod', [status(thm)], ['24', '25'])).
% 6.73/7.00  thf('314', plain, ((v1_funct_1 @ sk_C)),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('315', plain, ((v2_funct_1 @ sk_C)),
% 6.73/7.00      inference('simplify', [status(thm)], ['156'])).
% 6.73/7.00  thf('316', plain,
% 6.73/7.00      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.73/7.00        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.73/7.00      inference('demod', [status(thm)], ['311', '312', '313', '314', '315'])).
% 6.73/7.00  thf('317', plain,
% 6.73/7.00      (![X6 : $i, X7 : $i]:
% 6.73/7.00         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 6.73/7.00          | (v1_relat_1 @ X6)
% 6.73/7.00          | ~ (v1_relat_1 @ X7))),
% 6.73/7.00      inference('cnf', [status(esa)], [cc2_relat_1])).
% 6.73/7.00  thf('318', plain,
% 6.73/7.00      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 6.73/7.00        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 6.73/7.00      inference('sup-', [status(thm)], ['316', '317'])).
% 6.73/7.00  thf('319', plain,
% 6.73/7.00      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 6.73/7.00      inference('cnf', [status(esa)], [fc6_relat_1])).
% 6.73/7.00  thf('320', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 6.73/7.00      inference('demod', [status(thm)], ['318', '319'])).
% 6.73/7.00  thf('321', plain, ((v1_relat_1 @ sk_B)),
% 6.73/7.00      inference('demod', [status(thm)], ['65', '66'])).
% 6.73/7.00  thf('322', plain, ((v1_funct_1 @ sk_B)),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('323', plain, ((v2_funct_1 @ sk_B)),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('324', plain, ((v2_funct_1 @ sk_C)),
% 6.73/7.00      inference('simplify', [status(thm)], ['156'])).
% 6.73/7.00  thf('325', plain, ((v1_funct_1 @ sk_C)),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('326', plain, ((v1_relat_1 @ sk_C)),
% 6.73/7.00      inference('demod', [status(thm)], ['24', '25'])).
% 6.73/7.00  thf('327', plain,
% 6.73/7.00      ((r1_tarski @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ (k2_funct_1 @ sk_C)) @ 
% 6.73/7.00        (k2_zfmisc_1 @ 
% 6.73/7.00         (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ (k2_funct_1 @ sk_C))) @ 
% 6.73/7.00         sk_A))),
% 6.73/7.00      inference('demod', [status(thm)],
% 6.73/7.00                ['168', '194', '225', '246', '247', '320', '321', '322', 
% 6.73/7.00                 '323', '324', '325', '326'])).
% 6.73/7.00  thf('328', plain,
% 6.73/7.00      (((r1_tarski @ 
% 6.73/7.00         (k5_relat_1 @ (k2_funct_1 @ sk_B) @ (k2_funct_1 @ sk_C)) @ 
% 6.73/7.00         (k2_zfmisc_1 @ 
% 6.73/7.00          (k1_relat_1 @ (k2_funct_1 @ (k5_relat_1 @ sk_C @ sk_B))) @ sk_A))
% 6.73/7.00        | ~ (v1_relat_1 @ sk_C)
% 6.73/7.00        | ~ (v1_funct_1 @ sk_C)
% 6.73/7.00        | ~ (v2_funct_1 @ sk_C)
% 6.73/7.00        | ~ (v2_funct_1 @ sk_B)
% 6.73/7.00        | ~ (v1_funct_1 @ sk_B)
% 6.73/7.00        | ~ (v1_relat_1 @ sk_B))),
% 6.73/7.00      inference('sup+', [status(thm)], ['161', '327'])).
% 6.73/7.00  thf('329', plain, (((k5_relat_1 @ sk_C @ sk_B) = (sk_B))),
% 6.73/7.00      inference('demod', [status(thm)], ['122', '123'])).
% 6.73/7.00  thf('330', plain, ((v1_relat_1 @ sk_C)),
% 6.73/7.00      inference('demod', [status(thm)], ['24', '25'])).
% 6.73/7.00  thf('331', plain, ((v1_funct_1 @ sk_C)),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('332', plain, ((v2_funct_1 @ sk_C)),
% 6.73/7.00      inference('simplify', [status(thm)], ['156'])).
% 6.73/7.00  thf('333', plain, ((v2_funct_1 @ sk_B)),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('334', plain, ((v1_funct_1 @ sk_B)),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('335', plain, ((v1_relat_1 @ sk_B)),
% 6.73/7.00      inference('demod', [status(thm)], ['65', '66'])).
% 6.73/7.00  thf('336', plain,
% 6.73/7.00      ((r1_tarski @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ (k2_funct_1 @ sk_C)) @ 
% 6.73/7.00        (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_B)) @ sk_A))),
% 6.73/7.00      inference('demod', [status(thm)],
% 6.73/7.00                ['328', '329', '330', '331', '332', '333', '334', '335'])).
% 6.73/7.00  thf('337', plain,
% 6.73/7.00      (((r1_tarski @ 
% 6.73/7.00         (k5_relat_1 @ (k2_funct_1 @ sk_B) @ (k2_funct_1 @ sk_C)) @ 
% 6.73/7.00         (k2_zfmisc_1 @ (k2_relat_1 @ sk_B) @ sk_A))
% 6.73/7.00        | ~ (v1_relat_1 @ sk_B)
% 6.73/7.00        | ~ (v1_funct_1 @ sk_B)
% 6.73/7.00        | ~ (v2_funct_1 @ sk_B))),
% 6.73/7.00      inference('sup+', [status(thm)], ['160', '336'])).
% 6.73/7.00  thf('338', plain, ((v1_relat_1 @ sk_B)),
% 6.73/7.00      inference('demod', [status(thm)], ['65', '66'])).
% 6.73/7.00  thf('339', plain, ((v1_funct_1 @ sk_B)),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('340', plain, ((v2_funct_1 @ sk_B)),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('341', plain,
% 6.73/7.00      ((r1_tarski @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ (k2_funct_1 @ sk_C)) @ 
% 6.73/7.00        (k2_zfmisc_1 @ (k2_relat_1 @ sk_B) @ sk_A))),
% 6.73/7.00      inference('demod', [status(thm)], ['337', '338', '339', '340'])).
% 6.73/7.00  thf('342', plain,
% 6.73/7.00      (![X3 : $i, X5 : $i]:
% 6.73/7.00         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 6.73/7.00      inference('cnf', [status(esa)], [t3_subset])).
% 6.73/7.00  thf('343', plain,
% 6.73/7.00      ((m1_subset_1 @ 
% 6.73/7.00        (k5_relat_1 @ (k2_funct_1 @ sk_B) @ (k2_funct_1 @ sk_C)) @ 
% 6.73/7.00        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_B) @ sk_A)))),
% 6.73/7.00      inference('sup-', [status(thm)], ['341', '342'])).
% 6.73/7.00  thf('344', plain,
% 6.73/7.00      (![X32 : $i, X33 : $i, X34 : $i]:
% 6.73/7.00         ((v4_relat_1 @ X32 @ X33)
% 6.73/7.00          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 6.73/7.00      inference('cnf', [status(esa)], [cc2_relset_1])).
% 6.73/7.00  thf('345', plain,
% 6.73/7.00      ((v4_relat_1 @ 
% 6.73/7.00        (k5_relat_1 @ (k2_funct_1 @ sk_B) @ (k2_funct_1 @ sk_C)) @ 
% 6.73/7.00        (k2_relat_1 @ sk_B))),
% 6.73/7.00      inference('sup-', [status(thm)], ['343', '344'])).
% 6.73/7.00  thf('346', plain,
% 6.73/7.00      (![X16 : $i, X17 : $i]:
% 6.73/7.00         (((X16) = (k7_relat_1 @ X16 @ X17))
% 6.73/7.00          | ~ (v4_relat_1 @ X16 @ X17)
% 6.73/7.00          | ~ (v1_relat_1 @ X16))),
% 6.73/7.00      inference('cnf', [status(esa)], [t209_relat_1])).
% 6.73/7.00  thf('347', plain,
% 6.73/7.00      ((~ (v1_relat_1 @ 
% 6.73/7.00           (k5_relat_1 @ (k2_funct_1 @ sk_B) @ (k2_funct_1 @ sk_C)))
% 6.73/7.00        | ((k5_relat_1 @ (k2_funct_1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 6.73/7.00            = (k7_relat_1 @ 
% 6.73/7.00               (k5_relat_1 @ (k2_funct_1 @ sk_B) @ (k2_funct_1 @ sk_C)) @ 
% 6.73/7.00               (k2_relat_1 @ sk_B))))),
% 6.73/7.00      inference('sup-', [status(thm)], ['345', '346'])).
% 6.73/7.00  thf('348', plain,
% 6.73/7.00      ((m1_subset_1 @ 
% 6.73/7.00        (k5_relat_1 @ (k2_funct_1 @ sk_B) @ (k2_funct_1 @ sk_C)) @ 
% 6.73/7.00        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_B) @ sk_A)))),
% 6.73/7.00      inference('sup-', [status(thm)], ['341', '342'])).
% 6.73/7.00  thf('349', plain,
% 6.73/7.00      (![X6 : $i, X7 : $i]:
% 6.73/7.00         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 6.73/7.00          | (v1_relat_1 @ X6)
% 6.73/7.00          | ~ (v1_relat_1 @ X7))),
% 6.73/7.00      inference('cnf', [status(esa)], [cc2_relat_1])).
% 6.73/7.00  thf('350', plain,
% 6.73/7.00      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_B) @ sk_A))
% 6.73/7.00        | (v1_relat_1 @ 
% 6.73/7.00           (k5_relat_1 @ (k2_funct_1 @ sk_B) @ (k2_funct_1 @ sk_C))))),
% 6.73/7.00      inference('sup-', [status(thm)], ['348', '349'])).
% 6.73/7.00  thf('351', plain,
% 6.73/7.00      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 6.73/7.00      inference('cnf', [status(esa)], [fc6_relat_1])).
% 6.73/7.00  thf('352', plain,
% 6.73/7.00      ((v1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ (k2_funct_1 @ sk_C)))),
% 6.73/7.00      inference('demod', [status(thm)], ['350', '351'])).
% 6.73/7.00  thf('353', plain,
% 6.73/7.00      (((k5_relat_1 @ (k2_funct_1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 6.73/7.00         = (k7_relat_1 @ 
% 6.73/7.00            (k5_relat_1 @ (k2_funct_1 @ sk_B) @ (k2_funct_1 @ sk_C)) @ 
% 6.73/7.00            (k2_relat_1 @ sk_B)))),
% 6.73/7.00      inference('demod', [status(thm)], ['347', '352'])).
% 6.73/7.00  thf('354', plain,
% 6.73/7.00      ((((k5_relat_1 @ (k2_funct_1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 6.73/7.00          = (k7_relat_1 @ (k2_funct_1 @ (k5_relat_1 @ sk_C @ sk_B)) @ 
% 6.73/7.00             (k2_relat_1 @ sk_B)))
% 6.73/7.00        | ~ (v1_relat_1 @ sk_C)
% 6.73/7.00        | ~ (v1_funct_1 @ sk_C)
% 6.73/7.00        | ~ (v2_funct_1 @ sk_C)
% 6.73/7.00        | ~ (v2_funct_1 @ sk_B)
% 6.73/7.00        | ~ (v1_funct_1 @ sk_B)
% 6.73/7.00        | ~ (v1_relat_1 @ sk_B))),
% 6.73/7.00      inference('sup+', [status(thm)], ['159', '353'])).
% 6.73/7.00  thf('355', plain, (((k5_relat_1 @ sk_C @ sk_B) = (sk_B))),
% 6.73/7.00      inference('demod', [status(thm)], ['122', '123'])).
% 6.73/7.00  thf('356', plain,
% 6.73/7.00      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 6.73/7.00        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_B) @ sk_A)))),
% 6.73/7.00      inference('simplify', [status(thm)], ['189'])).
% 6.73/7.00  thf('357', plain,
% 6.73/7.00      (![X32 : $i, X33 : $i, X34 : $i]:
% 6.73/7.00         ((v4_relat_1 @ X32 @ X33)
% 6.73/7.00          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 6.73/7.00      inference('cnf', [status(esa)], [cc2_relset_1])).
% 6.73/7.00  thf('358', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_B) @ (k2_relat_1 @ sk_B))),
% 6.73/7.00      inference('sup-', [status(thm)], ['356', '357'])).
% 6.73/7.00  thf('359', plain,
% 6.73/7.00      (![X16 : $i, X17 : $i]:
% 6.73/7.00         (((X16) = (k7_relat_1 @ X16 @ X17))
% 6.73/7.00          | ~ (v4_relat_1 @ X16 @ X17)
% 6.73/7.00          | ~ (v1_relat_1 @ X16))),
% 6.73/7.00      inference('cnf', [status(esa)], [t209_relat_1])).
% 6.73/7.00  thf('360', plain,
% 6.73/7.00      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 6.73/7.00        | ((k2_funct_1 @ sk_B)
% 6.73/7.00            = (k7_relat_1 @ (k2_funct_1 @ sk_B) @ (k2_relat_1 @ sk_B))))),
% 6.73/7.00      inference('sup-', [status(thm)], ['358', '359'])).
% 6.73/7.00  thf('361', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 6.73/7.00      inference('demod', [status(thm)], ['192', '193'])).
% 6.73/7.00  thf('362', plain,
% 6.73/7.00      (((k2_funct_1 @ sk_B)
% 6.73/7.00         = (k7_relat_1 @ (k2_funct_1 @ sk_B) @ (k2_relat_1 @ sk_B)))),
% 6.73/7.00      inference('demod', [status(thm)], ['360', '361'])).
% 6.73/7.00  thf('363', plain, ((v1_relat_1 @ sk_C)),
% 6.73/7.00      inference('demod', [status(thm)], ['24', '25'])).
% 6.73/7.00  thf('364', plain, ((v1_funct_1 @ sk_C)),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('365', plain, ((v2_funct_1 @ sk_C)),
% 6.73/7.00      inference('simplify', [status(thm)], ['156'])).
% 6.73/7.00  thf('366', plain, ((v2_funct_1 @ sk_B)),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('367', plain, ((v1_funct_1 @ sk_B)),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('368', plain, ((v1_relat_1 @ sk_B)),
% 6.73/7.00      inference('demod', [status(thm)], ['65', '66'])).
% 6.73/7.00  thf('369', plain,
% 6.73/7.00      (((k5_relat_1 @ (k2_funct_1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 6.73/7.00         = (k2_funct_1 @ sk_B))),
% 6.73/7.00      inference('demod', [status(thm)],
% 6.73/7.00                ['354', '355', '362', '363', '364', '365', '366', '367', '368'])).
% 6.73/7.00  thf('370', plain,
% 6.73/7.00      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.73/7.00        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.73/7.00      inference('demod', [status(thm)], ['311', '312', '313', '314', '315'])).
% 6.73/7.00  thf('371', plain,
% 6.73/7.00      (![X62 : $i, X63 : $i]:
% 6.73/7.00         (((k1_relset_1 @ X62 @ X62 @ X63) = (X62))
% 6.73/7.00          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X62 @ X62)))
% 6.73/7.00          | ~ (v1_funct_2 @ X63 @ X62 @ X62)
% 6.73/7.00          | ~ (v1_funct_1 @ X63))),
% 6.73/7.00      inference('cnf', [status(esa)], [t67_funct_2])).
% 6.73/7.00  thf('372', plain,
% 6.73/7.00      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 6.73/7.00        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_A @ sk_A)
% 6.73/7.00        | ((k1_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ sk_C)) = (sk_A)))),
% 6.73/7.00      inference('sup-', [status(thm)], ['370', '371'])).
% 6.73/7.00  thf('373', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 6.73/7.00      inference('demod', [status(thm)], ['9', '10', '11', '14'])).
% 6.73/7.00  thf('374', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         (~ (v1_relat_1 @ X0)
% 6.73/7.00          | (m1_subset_1 @ X0 @ 
% 6.73/7.00             (k1_zfmisc_1 @ 
% 6.73/7.00              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 6.73/7.00      inference('sup-', [status(thm)], ['170', '171'])).
% 6.73/7.00  thf('375', plain,
% 6.73/7.00      (((m1_subset_1 @ sk_C @ 
% 6.73/7.00         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C))))
% 6.73/7.00        | ~ (v1_relat_1 @ sk_C))),
% 6.73/7.00      inference('sup+', [status(thm)], ['373', '374'])).
% 6.73/7.00  thf('376', plain, ((v1_relat_1 @ sk_C)),
% 6.73/7.00      inference('demod', [status(thm)], ['24', '25'])).
% 6.73/7.00  thf('377', plain,
% 6.73/7.00      ((m1_subset_1 @ sk_C @ 
% 6.73/7.00        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C))))),
% 6.73/7.00      inference('demod', [status(thm)], ['375', '376'])).
% 6.73/7.00  thf('378', plain,
% 6.73/7.00      (![X58 : $i, X59 : $i, X60 : $i]:
% 6.73/7.00         (~ (v2_funct_1 @ X58)
% 6.73/7.00          | ((k2_relset_1 @ X60 @ X59 @ X58) != (X59))
% 6.73/7.00          | (v1_funct_1 @ (k2_funct_1 @ X58))
% 6.73/7.00          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X60 @ X59)))
% 6.73/7.00          | ~ (v1_funct_2 @ X58 @ X60 @ X59)
% 6.73/7.00          | ~ (v1_funct_1 @ X58))),
% 6.73/7.00      inference('cnf', [status(esa)], [t31_funct_2])).
% 6.73/7.00  thf('379', plain,
% 6.73/7.00      ((~ (v1_funct_1 @ sk_C)
% 6.73/7.00        | ~ (v1_funct_2 @ sk_C @ sk_A @ (k2_relat_1 @ sk_C))
% 6.73/7.00        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 6.73/7.00        | ((k2_relset_1 @ sk_A @ (k2_relat_1 @ sk_C) @ sk_C)
% 6.73/7.00            != (k2_relat_1 @ sk_C))
% 6.73/7.00        | ~ (v2_funct_1 @ sk_C))),
% 6.73/7.00      inference('sup-', [status(thm)], ['377', '378'])).
% 6.73/7.00  thf('380', plain, ((v1_funct_1 @ sk_C)),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('381', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 6.73/7.00      inference('demod', [status(thm)], ['9', '10', '11', '14'])).
% 6.73/7.00  thf('382', plain,
% 6.73/7.00      (![X61 : $i]:
% 6.73/7.00         ((v1_funct_2 @ X61 @ (k1_relat_1 @ X61) @ (k2_relat_1 @ X61))
% 6.73/7.00          | ~ (v1_funct_1 @ X61)
% 6.73/7.00          | ~ (v1_relat_1 @ X61))),
% 6.73/7.00      inference('cnf', [status(esa)], [t3_funct_2])).
% 6.73/7.00  thf('383', plain,
% 6.73/7.00      (((v1_funct_2 @ sk_C @ sk_A @ (k2_relat_1 @ sk_C))
% 6.73/7.00        | ~ (v1_relat_1 @ sk_C)
% 6.73/7.00        | ~ (v1_funct_1 @ sk_C))),
% 6.73/7.00      inference('sup+', [status(thm)], ['381', '382'])).
% 6.73/7.00  thf('384', plain, ((v1_relat_1 @ sk_C)),
% 6.73/7.00      inference('demod', [status(thm)], ['24', '25'])).
% 6.73/7.00  thf('385', plain, ((v1_funct_1 @ sk_C)),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('386', plain, ((v1_funct_2 @ sk_C @ sk_A @ (k2_relat_1 @ sk_C))),
% 6.73/7.00      inference('demod', [status(thm)], ['383', '384', '385'])).
% 6.73/7.00  thf('387', plain,
% 6.73/7.00      ((m1_subset_1 @ sk_C @ 
% 6.73/7.00        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_C))))),
% 6.73/7.00      inference('demod', [status(thm)], ['375', '376'])).
% 6.73/7.00  thf('388', plain,
% 6.73/7.00      (![X38 : $i, X39 : $i, X40 : $i]:
% 6.73/7.00         (((k2_relset_1 @ X39 @ X40 @ X38) = (k2_relat_1 @ X38))
% 6.73/7.00          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40))))),
% 6.73/7.00      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 6.73/7.00  thf('389', plain,
% 6.73/7.00      (((k2_relset_1 @ sk_A @ (k2_relat_1 @ sk_C) @ sk_C) = (k2_relat_1 @ sk_C))),
% 6.73/7.00      inference('sup-', [status(thm)], ['387', '388'])).
% 6.73/7.00  thf('390', plain,
% 6.73/7.00      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 6.73/7.00        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 6.73/7.00        | ~ (v2_funct_1 @ sk_C))),
% 6.73/7.00      inference('demod', [status(thm)], ['379', '380', '386', '389'])).
% 6.73/7.00  thf('391', plain,
% 6.73/7.00      ((~ (v2_funct_1 @ sk_C) | (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 6.73/7.00      inference('simplify', [status(thm)], ['390'])).
% 6.73/7.00  thf('392', plain, ((v2_funct_1 @ sk_C)),
% 6.73/7.00      inference('simplify', [status(thm)], ['156'])).
% 6.73/7.00  thf('393', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 6.73/7.00      inference('demod', [status(thm)], ['391', '392'])).
% 6.73/7.00  thf('394', plain,
% 6.73/7.00      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('395', plain,
% 6.73/7.00      (![X58 : $i, X59 : $i, X60 : $i]:
% 6.73/7.00         (~ (v2_funct_1 @ X58)
% 6.73/7.00          | ((k2_relset_1 @ X60 @ X59 @ X58) != (X59))
% 6.73/7.00          | (v1_funct_2 @ (k2_funct_1 @ X58) @ X59 @ X60)
% 6.73/7.00          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X60 @ X59)))
% 6.73/7.00          | ~ (v1_funct_2 @ X58 @ X60 @ X59)
% 6.73/7.00          | ~ (v1_funct_1 @ X58))),
% 6.73/7.00      inference('cnf', [status(esa)], [t31_funct_2])).
% 6.73/7.00  thf('396', plain,
% 6.73/7.00      ((~ (v1_funct_1 @ sk_C)
% 6.73/7.00        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 6.73/7.00        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_A @ sk_A)
% 6.73/7.00        | ((k2_relset_1 @ sk_A @ sk_A @ sk_C) != (sk_A))
% 6.73/7.00        | ~ (v2_funct_1 @ sk_C))),
% 6.73/7.00      inference('sup-', [status(thm)], ['394', '395'])).
% 6.73/7.00  thf('397', plain, ((v1_funct_1 @ sk_C)),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('398', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('399', plain,
% 6.73/7.00      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('400', plain,
% 6.73/7.00      (![X38 : $i, X39 : $i, X40 : $i]:
% 6.73/7.00         (((k2_relset_1 @ X39 @ X40 @ X38) = (k2_relat_1 @ X38))
% 6.73/7.00          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40))))),
% 6.73/7.00      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 6.73/7.00  thf('401', plain,
% 6.73/7.00      (((k2_relset_1 @ sk_A @ sk_A @ sk_C) = (k2_relat_1 @ sk_C))),
% 6.73/7.00      inference('sup-', [status(thm)], ['399', '400'])).
% 6.73/7.00  thf('402', plain,
% 6.73/7.00      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_A @ sk_A)
% 6.73/7.00        | ((k2_relat_1 @ sk_C) != (sk_A))
% 6.73/7.00        | ~ (v2_funct_1 @ sk_C))),
% 6.73/7.00      inference('demod', [status(thm)], ['396', '397', '398', '401'])).
% 6.73/7.00  thf('403', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 6.73/7.00      inference('sup+', [status(thm)], ['126', '142'])).
% 6.73/7.00  thf('404', plain,
% 6.73/7.00      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_A @ sk_A)
% 6.73/7.00        | ((sk_A) != (sk_A))
% 6.73/7.00        | ~ (v2_funct_1 @ sk_C))),
% 6.73/7.00      inference('demod', [status(thm)], ['402', '403'])).
% 6.73/7.00  thf('405', plain,
% 6.73/7.00      ((~ (v2_funct_1 @ sk_C)
% 6.73/7.00        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_A @ sk_A))),
% 6.73/7.00      inference('simplify', [status(thm)], ['404'])).
% 6.73/7.00  thf('406', plain, ((v2_funct_1 @ sk_C)),
% 6.73/7.00      inference('simplify', [status(thm)], ['156'])).
% 6.73/7.00  thf('407', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_A @ sk_A)),
% 6.73/7.00      inference('demod', [status(thm)], ['405', '406'])).
% 6.73/7.00  thf('408', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 6.73/7.00      inference('sup+', [status(thm)], ['126', '142'])).
% 6.73/7.00  thf('409', plain,
% 6.73/7.00      (![X28 : $i]:
% 6.73/7.00         (~ (v2_funct_1 @ X28)
% 6.73/7.00          | ((k2_relat_1 @ X28) = (k1_relat_1 @ (k2_funct_1 @ X28)))
% 6.73/7.00          | ~ (v1_funct_1 @ X28)
% 6.73/7.00          | ~ (v1_relat_1 @ X28))),
% 6.73/7.00      inference('cnf', [status(esa)], [t55_funct_1])).
% 6.73/7.00  thf('410', plain,
% 6.73/7.00      (![X21 : $i]:
% 6.73/7.00         ((v1_relat_1 @ (k2_funct_1 @ X21))
% 6.73/7.00          | ~ (v1_funct_1 @ X21)
% 6.73/7.00          | ~ (v1_relat_1 @ X21))),
% 6.73/7.00      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.73/7.00  thf('411', plain,
% 6.73/7.00      (![X28 : $i]:
% 6.73/7.00         (~ (v2_funct_1 @ X28)
% 6.73/7.00          | ((k1_relat_1 @ X28) = (k2_relat_1 @ (k2_funct_1 @ X28)))
% 6.73/7.00          | ~ (v1_funct_1 @ X28)
% 6.73/7.00          | ~ (v1_relat_1 @ X28))),
% 6.73/7.00      inference('cnf', [status(esa)], [t55_funct_1])).
% 6.73/7.00  thf('412', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         (~ (v1_relat_1 @ X0)
% 6.73/7.00          | (m1_subset_1 @ X0 @ 
% 6.73/7.00             (k1_zfmisc_1 @ 
% 6.73/7.00              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 6.73/7.00      inference('sup-', [status(thm)], ['170', '171'])).
% 6.73/7.00  thf('413', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 6.73/7.00           (k1_zfmisc_1 @ 
% 6.73/7.00            (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))))
% 6.73/7.00          | ~ (v1_relat_1 @ X0)
% 6.73/7.00          | ~ (v1_funct_1 @ X0)
% 6.73/7.00          | ~ (v2_funct_1 @ X0)
% 6.73/7.00          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 6.73/7.00      inference('sup+', [status(thm)], ['411', '412'])).
% 6.73/7.00  thf('414', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         (~ (v1_relat_1 @ X0)
% 6.73/7.00          | ~ (v1_funct_1 @ X0)
% 6.73/7.00          | ~ (v2_funct_1 @ X0)
% 6.73/7.00          | ~ (v1_funct_1 @ X0)
% 6.73/7.00          | ~ (v1_relat_1 @ X0)
% 6.73/7.00          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 6.73/7.00             (k1_zfmisc_1 @ 
% 6.73/7.00              (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ 
% 6.73/7.00               (k1_relat_1 @ X0)))))),
% 6.73/7.00      inference('sup-', [status(thm)], ['410', '413'])).
% 6.73/7.00  thf('415', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 6.73/7.00           (k1_zfmisc_1 @ 
% 6.73/7.00            (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))))
% 6.73/7.00          | ~ (v2_funct_1 @ X0)
% 6.73/7.00          | ~ (v1_funct_1 @ X0)
% 6.73/7.00          | ~ (v1_relat_1 @ X0))),
% 6.73/7.00      inference('simplify', [status(thm)], ['414'])).
% 6.73/7.00  thf('416', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 6.73/7.00           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))))
% 6.73/7.00          | ~ (v1_relat_1 @ X0)
% 6.73/7.00          | ~ (v1_funct_1 @ X0)
% 6.73/7.00          | ~ (v2_funct_1 @ X0)
% 6.73/7.00          | ~ (v1_relat_1 @ X0)
% 6.73/7.00          | ~ (v1_funct_1 @ X0)
% 6.73/7.00          | ~ (v2_funct_1 @ X0))),
% 6.73/7.00      inference('sup+', [status(thm)], ['409', '415'])).
% 6.73/7.00  thf('417', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         (~ (v2_funct_1 @ X0)
% 6.73/7.00          | ~ (v1_funct_1 @ X0)
% 6.73/7.00          | ~ (v1_relat_1 @ X0)
% 6.73/7.00          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 6.73/7.00             (k1_zfmisc_1 @ 
% 6.73/7.00              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))))),
% 6.73/7.00      inference('simplify', [status(thm)], ['416'])).
% 6.73/7.00  thf('418', plain,
% 6.73/7.00      (![X35 : $i, X36 : $i, X37 : $i]:
% 6.73/7.00         (((k1_relset_1 @ X36 @ X37 @ X35) = (k1_relat_1 @ X35))
% 6.73/7.00          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 6.73/7.00      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 6.73/7.00  thf('419', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         (~ (v1_relat_1 @ X0)
% 6.73/7.00          | ~ (v1_funct_1 @ X0)
% 6.73/7.00          | ~ (v2_funct_1 @ X0)
% 6.73/7.00          | ((k1_relset_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0) @ 
% 6.73/7.00              (k2_funct_1 @ X0)) = (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 6.73/7.00      inference('sup-', [status(thm)], ['417', '418'])).
% 6.73/7.00  thf('420', plain,
% 6.73/7.00      ((((k1_relset_1 @ sk_A @ (k1_relat_1 @ sk_C) @ (k2_funct_1 @ sk_C))
% 6.73/7.00          = (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 6.73/7.00        | ~ (v2_funct_1 @ sk_C)
% 6.73/7.00        | ~ (v1_funct_1 @ sk_C)
% 6.73/7.00        | ~ (v1_relat_1 @ sk_C))),
% 6.73/7.00      inference('sup+', [status(thm)], ['408', '419'])).
% 6.73/7.00  thf('421', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 6.73/7.00      inference('demod', [status(thm)], ['9', '10', '11', '14'])).
% 6.73/7.00  thf('422', plain, ((v2_funct_1 @ sk_C)),
% 6.73/7.00      inference('simplify', [status(thm)], ['156'])).
% 6.73/7.00  thf('423', plain, ((v1_funct_1 @ sk_C)),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('424', plain, ((v1_relat_1 @ sk_C)),
% 6.73/7.00      inference('demod', [status(thm)], ['24', '25'])).
% 6.73/7.00  thf('425', plain,
% 6.73/7.00      (((k1_relset_1 @ sk_A @ sk_A @ (k2_funct_1 @ sk_C))
% 6.73/7.00         = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 6.73/7.00      inference('demod', [status(thm)], ['420', '421', '422', '423', '424'])).
% 6.73/7.00  thf('426', plain, (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_A))),
% 6.73/7.00      inference('demod', [status(thm)], ['372', '393', '407', '425'])).
% 6.73/7.00  thf('427', plain,
% 6.73/7.00      (![X24 : $i, X25 : $i]:
% 6.73/7.00         (~ (v1_relat_1 @ X24)
% 6.73/7.00          | ~ (v1_funct_1 @ X24)
% 6.73/7.00          | ((X24) = (k6_partfun1 @ (k1_relat_1 @ X24)))
% 6.73/7.00          | ((k5_relat_1 @ X25 @ X24) != (X25))
% 6.73/7.00          | ((k2_relat_1 @ X25) != (k1_relat_1 @ X24))
% 6.73/7.00          | ~ (v1_funct_1 @ X25)
% 6.73/7.00          | ~ (v1_relat_1 @ X25))),
% 6.73/7.00      inference('demod', [status(thm)], ['16', '17'])).
% 6.73/7.00  thf('428', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         (((k2_relat_1 @ X0) != (sk_A))
% 6.73/7.00          | ~ (v1_relat_1 @ X0)
% 6.73/7.00          | ~ (v1_funct_1 @ X0)
% 6.73/7.00          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ sk_C)) != (X0))
% 6.73/7.00          | ((k2_funct_1 @ sk_C)
% 6.73/7.00              = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))
% 6.73/7.00          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 6.73/7.00          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 6.73/7.00      inference('sup-', [status(thm)], ['426', '427'])).
% 6.73/7.00  thf('429', plain, (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (sk_A))),
% 6.73/7.00      inference('demod', [status(thm)], ['372', '393', '407', '425'])).
% 6.73/7.00  thf('430', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 6.73/7.00      inference('demod', [status(thm)], ['391', '392'])).
% 6.73/7.00  thf('431', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 6.73/7.00      inference('demod', [status(thm)], ['318', '319'])).
% 6.73/7.00  thf('432', plain,
% 6.73/7.00      (![X0 : $i]:
% 6.73/7.00         (((k2_relat_1 @ X0) != (sk_A))
% 6.73/7.00          | ~ (v1_relat_1 @ X0)
% 6.73/7.00          | ~ (v1_funct_1 @ X0)
% 6.73/7.00          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ sk_C)) != (X0))
% 6.73/7.00          | ((k2_funct_1 @ sk_C) = (k6_partfun1 @ sk_A)))),
% 6.73/7.00      inference('demod', [status(thm)], ['428', '429', '430', '431'])).
% 6.73/7.00  thf('433', plain,
% 6.73/7.00      ((((k2_funct_1 @ sk_B) != (k2_funct_1 @ sk_B))
% 6.73/7.00        | ((k2_funct_1 @ sk_C) = (k6_partfun1 @ sk_A))
% 6.73/7.00        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 6.73/7.00        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 6.73/7.00        | ((k2_relat_1 @ (k2_funct_1 @ sk_B)) != (sk_A)))),
% 6.73/7.00      inference('sup-', [status(thm)], ['369', '432'])).
% 6.73/7.00  thf('434', plain,
% 6.73/7.00      ((m1_subset_1 @ sk_B @ 
% 6.73/7.00        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B))))),
% 6.73/7.00      inference('demod', [status(thm)], ['173', '174'])).
% 6.73/7.00  thf('435', plain,
% 6.73/7.00      (![X58 : $i, X59 : $i, X60 : $i]:
% 6.73/7.00         (~ (v2_funct_1 @ X58)
% 6.73/7.00          | ((k2_relset_1 @ X60 @ X59 @ X58) != (X59))
% 6.73/7.00          | (v1_funct_1 @ (k2_funct_1 @ X58))
% 6.73/7.00          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X60 @ X59)))
% 6.73/7.00          | ~ (v1_funct_2 @ X58 @ X60 @ X59)
% 6.73/7.00          | ~ (v1_funct_1 @ X58))),
% 6.73/7.00      inference('cnf', [status(esa)], [t31_funct_2])).
% 6.73/7.00  thf('436', plain,
% 6.73/7.00      ((~ (v1_funct_1 @ sk_B)
% 6.73/7.00        | ~ (v1_funct_2 @ sk_B @ sk_A @ (k2_relat_1 @ sk_B))
% 6.73/7.00        | (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 6.73/7.00        | ((k2_relset_1 @ sk_A @ (k2_relat_1 @ sk_B) @ sk_B)
% 6.73/7.00            != (k2_relat_1 @ sk_B))
% 6.73/7.00        | ~ (v2_funct_1 @ sk_B))),
% 6.73/7.00      inference('sup-', [status(thm)], ['434', '435'])).
% 6.73/7.00  thf('437', plain, ((v1_funct_1 @ sk_B)),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('438', plain, ((v1_funct_2 @ sk_B @ sk_A @ (k2_relat_1 @ sk_B))),
% 6.73/7.00      inference('demod', [status(thm)], ['181', '182', '183'])).
% 6.73/7.00  thf('439', plain,
% 6.73/7.00      (((k2_relset_1 @ sk_A @ (k2_relat_1 @ sk_B) @ sk_B) = (k2_relat_1 @ sk_B))),
% 6.73/7.00      inference('sup-', [status(thm)], ['185', '186'])).
% 6.73/7.00  thf('440', plain, ((v2_funct_1 @ sk_B)),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('441', plain,
% 6.73/7.00      (((v1_funct_1 @ (k2_funct_1 @ sk_B))
% 6.73/7.00        | ((k2_relat_1 @ sk_B) != (k2_relat_1 @ sk_B)))),
% 6.73/7.00      inference('demod', [status(thm)], ['436', '437', '438', '439', '440'])).
% 6.73/7.00  thf('442', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 6.73/7.00      inference('simplify', [status(thm)], ['441'])).
% 6.73/7.00  thf('443', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 6.73/7.00      inference('demod', [status(thm)], ['192', '193'])).
% 6.73/7.00  thf('444', plain, (((sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_B)))),
% 6.73/7.00      inference('demod', [status(thm)],
% 6.73/7.00                ['219', '220', '221', '222', '223', '224'])).
% 6.73/7.00  thf('445', plain,
% 6.73/7.00      ((((k2_funct_1 @ sk_B) != (k2_funct_1 @ sk_B))
% 6.73/7.00        | ((k2_funct_1 @ sk_C) = (k6_partfun1 @ sk_A))
% 6.73/7.00        | ((sk_A) != (sk_A)))),
% 6.73/7.00      inference('demod', [status(thm)], ['433', '442', '443', '444'])).
% 6.73/7.00  thf('446', plain, (((k2_funct_1 @ sk_C) = (k6_partfun1 @ sk_A))),
% 6.73/7.00      inference('simplify', [status(thm)], ['445'])).
% 6.73/7.00  thf('447', plain,
% 6.73/7.00      ((((sk_C) = (k6_partfun1 @ sk_A))
% 6.73/7.00        | ((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A)))),
% 6.73/7.00      inference('demod', [status(thm)], ['158', '446'])).
% 6.73/7.00  thf('448', plain, (((sk_C) = (k6_partfun1 @ sk_A))),
% 6.73/7.00      inference('simplify', [status(thm)], ['447'])).
% 6.73/7.00  thf('449', plain,
% 6.73/7.00      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 6.73/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.73/7.00  thf('450', plain,
% 6.73/7.00      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 6.73/7.00         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 6.73/7.00          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 6.73/7.00          | (r2_relset_1 @ X42 @ X43 @ X41 @ X44)
% 6.73/7.00          | ((X41) != (X44)))),
% 6.73/7.00      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 6.73/7.00  thf('451', plain,
% 6.73/7.00      (![X42 : $i, X43 : $i, X44 : $i]:
% 6.73/7.00         ((r2_relset_1 @ X42 @ X43 @ X44 @ X44)
% 6.73/7.00          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43))))),
% 6.73/7.00      inference('simplify', [status(thm)], ['450'])).
% 6.73/7.00  thf('452', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C)),
% 6.73/7.00      inference('sup-', [status(thm)], ['449', '451'])).
% 6.73/7.00  thf('453', plain, ($false),
% 6.73/7.00      inference('demod', [status(thm)], ['0', '448', '452'])).
% 6.73/7.00  
% 6.73/7.00  % SZS output end Refutation
% 6.73/7.00  
% 6.73/7.01  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
