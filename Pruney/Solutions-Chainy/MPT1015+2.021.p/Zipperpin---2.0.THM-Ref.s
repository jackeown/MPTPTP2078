%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IQtrkOLJnJ

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:50 EST 2020

% Result     : Theorem 9.20s
% Output     : Refutation 9.20s
% Verified   : 
% Statistics : Number of formulae       :  256 (7129 expanded)
%              Number of leaves         :   43 (2184 expanded)
%              Depth                    :   25
%              Number of atoms          : 2787 (146049 expanded)
%              Number of equality atoms :  112 (1899 expanded)
%              Maximal formula depth    :   25 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

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

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('2',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X54: $i,X55: $i] :
      ( ( ( k1_relset_1 @ X54 @ X54 @ X55 )
        = X54 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X54 ) ) )
      | ~ ( v1_funct_2 @ X55 @ X54 @ X54 )
      | ~ ( v1_funct_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('5',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('9',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k1_relset_1 @ X11 @ X12 @ X10 )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('10',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['5','6','7','10'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X53: $i] :
      ( ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X53 ) @ ( k2_relat_1 @ X53 ) ) ) )
      | ~ ( v1_funct_1 @ X53 )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('13',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('18',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','18','19'])).

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

thf('21',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( v2_funct_1 @ X50 )
      | ( ( k2_relset_1 @ X52 @ X51 @ X50 )
       != X51 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X50 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X51 ) ) )
      | ~ ( v1_funct_2 @ X50 @ X52 @ X51 )
      | ~ ( v1_funct_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('22',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ ( k2_relat_1 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ ( k2_relat_1 @ sk_B ) @ sk_B )
     != ( k2_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['5','6','7','10'])).

thf('25',plain,(
    ! [X53: $i] :
      ( ( v1_funct_2 @ X53 @ ( k1_relat_1 @ X53 ) @ ( k2_relat_1 @ X53 ) )
      | ~ ( v1_funct_1 @ X53 )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('26',plain,
    ( ( v1_funct_2 @ sk_B @ sk_A @ ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['16','17'])).

thf('28',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_2 @ sk_B @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['5','6','7','10'])).

thf('31',plain,(
    ! [X53: $i] :
      ( ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X53 ) @ ( k2_relat_1 @ X53 ) ) ) )
      | ~ ( v1_funct_1 @ X53 )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('32',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k2_relset_1 @ sk_A @ ( k2_relat_1 @ sk_B ) @ sk_B )
      = ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('35',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['16','17'])).

thf('37',plain,
    ( ( k2_relset_1 @ sk_A @ ( k2_relat_1 @ sk_B ) @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ) )
    | ( ( k2_relat_1 @ sk_B )
     != ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','23','29','37','38'])).

thf('40',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('42',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_B ) @ sk_A ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('44',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['42','43'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('45',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k5_relat_1 @ X9 @ ( k2_funct_1 @ X9 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('46',plain,(
    ! [X53: $i] :
      ( ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X53 ) @ ( k2_relat_1 @ X53 ) ) ) )
      | ~ ( v1_funct_1 @ X53 )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('47',plain,(
    ! [X53: $i] :
      ( ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X53 ) @ ( k2_relat_1 @ X53 ) ) ) )
      | ~ ( v1_funct_1 @ X53 )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('48',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( ( k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37 )
        = ( k5_relat_1 @ X34 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_partfun1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X3 @ X2 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) )
      | ( ( k1_partfun1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X3 @ X2 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_partfun1 @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X1 @ X0 )
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_partfun1 @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X1 @ X0 )
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X53: $i] :
      ( ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X53 ) @ ( k2_relat_1 @ X53 ) ) ) )
      | ~ ( v1_funct_1 @ X53 )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('54',plain,(
    ! [X53: $i] :
      ( ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X53 ) @ ( k2_relat_1 @ X53 ) ) ) )
      | ~ ( v1_funct_1 @ X53 )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('55',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( v1_funct_1 @ ( k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_funct_1 @ ( k1_partfun1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X3 @ X2 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) )
      | ( v1_funct_1 @ ( k1_partfun1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X3 @ X2 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v1_funct_1 @ ( k1_partfun1 @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['52','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ( v1_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','63'])).

thf('65',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['5','6','7','10'])).

thf('66',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['16','17'])).

thf('67',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','18','19'])).

thf('70',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( v2_funct_1 @ X50 )
      | ( ( k2_relset_1 @ X52 @ X51 @ X50 )
       != X51 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X50 ) )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X51 ) ) )
      | ~ ( v1_funct_2 @ X50 @ X52 @ X51 )
      | ~ ( v1_funct_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('71',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ ( k2_relat_1 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k2_relset_1 @ sk_A @ ( k2_relat_1 @ sk_B ) @ sk_B )
     != ( k2_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_2 @ sk_B @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('74',plain,
    ( ( k2_relset_1 @ sk_A @ ( k2_relat_1 @ sk_B ) @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('75',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k2_relat_1 @ sk_B )
     != ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['71','72','73','74','75'])).

thf('77',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    v1_funct_1 @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['64','65','66','67','68','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('80',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('81',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('82',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( ( k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37 )
        = ( k5_relat_1 @ X34 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_partfun1 @ X0 @ X0 @ X3 @ X2 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ ( k6_relat_1 @ X0 ) @ sk_B )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['79','84'])).

thf('86',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ ( k6_relat_1 @ X0 ) @ sk_B )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ sk_B )
    = ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['78','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t23_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( r2_relset_1 @ A @ B @ ( k4_relset_1 @ A @ A @ A @ B @ ( k6_partfun1 @ A ) @ C ) @ C )
        & ( r2_relset_1 @ A @ B @ ( k4_relset_1 @ A @ B @ B @ B @ C @ ( k6_partfun1 @ B ) ) @ C ) ) ) )).

thf('90',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( r2_relset_1 @ X41 @ X42 @ ( k4_relset_1 @ X41 @ X41 @ X41 @ X42 @ ( k6_partfun1 @ X41 ) @ X43 ) @ X43 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[t23_funct_2])).

thf('91',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('92',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( r2_relset_1 @ X41 @ X42 @ ( k4_relset_1 @ X41 @ X41 @ X41 @ X42 @ ( k6_relat_1 @ X41 ) @ X43 ) @ X43 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ sk_B ),
    inference('sup-',[status(thm)],['89','92'])).

thf('94',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('96',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( ( k4_relset_1 @ X17 @ X18 @ X20 @ X21 @ X16 @ X19 )
        = ( k5_relat_1 @ X16 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_relset_1 @ X0 @ X0 @ X3 @ X2 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k4_relset_1 @ X0 @ X0 @ sk_A @ sk_A @ ( k6_relat_1 @ X0 ) @ sk_B )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['94','97'])).

thf('99',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['93','98'])).

thf('100',plain,(
    v1_funct_1 @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['64','65','66','67','68','77'])).

thf('101',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('103',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ X0 @ X0 @ X3 @ X1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ( m1_subset_1 @ ( k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ ( k6_relat_1 @ X0 ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['101','104'])).

thf('106',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ ( k6_relat_1 @ X0 ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['100','107'])).

thf('109',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ sk_B )
    = ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['78','87'])).

thf('110',plain,(
    m1_subset_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('111',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( X22 = X25 )
      | ~ ( r2_relset_1 @ X23 @ X24 @ X22 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['99','112'])).

thf('114',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['88','115'])).

thf('117',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( ( k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37 )
        = ( k5_relat_1 @ X34 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('120',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
      = ( k5_relat_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['117','122'])).

thf('124',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
    = ( k5_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
    = ( k5_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('128',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('132',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['129','134'])).

thf('136',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
    = ( k5_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('139',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( X22 = X25 )
      | ~ ( r2_relset_1 @ X23 @ X24 @ X22 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('141',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_B ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_B )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['128','141'])).

thf('143',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ( k5_relat_1 @ sk_C @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['125','144'])).

thf('146',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t27_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ~ ( ( A != k1_xboole_0 )
          & ( B != k1_xboole_0 )
          & ~ ( ( v2_funct_1 @ C )
            <=> ! [D: $i,E: $i] :
                  ( ( ( v1_funct_1 @ E )
                    & ( v1_funct_2 @ E @ D @ A )
                    & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ A ) ) ) )
                 => ! [F: $i] :
                      ( ( ( v1_funct_1 @ F )
                        & ( v1_funct_2 @ F @ D @ A )
                        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ A ) ) ) )
                     => ( ( r2_relset_1 @ D @ B @ ( k1_partfun1 @ D @ A @ A @ B @ E @ C ) @ ( k1_partfun1 @ D @ A @ A @ B @ F @ C ) )
                       => ( r2_relset_1 @ D @ A @ E @ F ) ) ) ) ) ) ) )).

thf('147',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ( X44 = k1_xboole_0 )
      | ( X45 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X45 @ X44 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_funct_2 @ X47 @ X48 @ X45 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X45 ) ) )
      | ~ ( r2_relset_1 @ X48 @ X44 @ ( k1_partfun1 @ X48 @ X45 @ X45 @ X44 @ X47 @ X46 ) @ ( k1_partfun1 @ X48 @ X45 @ X45 @ X44 @ X49 @ X46 ) )
      | ( r2_relset_1 @ X48 @ X45 @ X47 @ X49 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X45 ) ) )
      | ~ ( v1_funct_2 @ X49 @ X48 @ X45 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v2_funct_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t27_funct_2])).

thf('148',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v2_funct_1 @ sk_B )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_A ) ) )
      | ( r2_relset_1 @ X1 @ sk_A @ X2 @ X0 )
      | ~ ( r2_relset_1 @ X1 @ sk_A @ ( k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X2 @ sk_B ) @ ( k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X2 @ X1 @ sk_A )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_B )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_A ) ) )
      | ( r2_relset_1 @ X1 @ sk_A @ X2 @ X0 )
      | ~ ( r2_relset_1 @ X1 @ sk_A @ ( k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X2 @ sk_B ) @ ( k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X2 @ X1 @ sk_A )
      | ~ ( v1_funct_1 @ X2 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['148','149','150','151'])).

thf('153',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ X1 @ sk_A )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_A ) ) )
      | ~ ( r2_relset_1 @ X1 @ sk_A @ ( k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X2 @ sk_B ) @ ( k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X0 @ sk_B ) )
      | ( r2_relset_1 @ X1 @ sk_A @ X2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_A )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['145','153'])).

thf('155',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['154','155','156','157'])).

thf('159',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B )
    | ( sk_A = k1_xboole_0 )
    | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k6_relat_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k6_relat_1 @ sk_A ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['116','158'])).

thf('160',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( r2_relset_1 @ X23 @ X24 @ X22 @ X25 )
      | ( X22 != X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('162',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r2_relset_1 @ X23 @ X24 @ X25 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B ),
    inference('sup-',[status(thm)],['160','162'])).

thf('164',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('165',plain,(
    v1_funct_1 @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['64','65','66','67','68','77'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('166',plain,(
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('167',plain,(
    ! [X53: $i] :
      ( ( v1_funct_2 @ X53 @ ( k1_relat_1 @ X53 ) @ ( k2_relat_1 @ X53 ) )
      | ~ ( v1_funct_1 @ X53 )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('168',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k6_relat_1 @ X0 ) @ X0 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['166','167'])).

thf('169',plain,(
    ! [X6: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X6 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('170',plain,(
    ! [X7: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k6_relat_1 @ X0 ) @ X0 @ X0 )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['168','169','170'])).

thf('172',plain,(
    v1_funct_2 @ ( k6_relat_1 @ sk_A ) @ sk_A @ sk_A ),
    inference('sup-',[status(thm)],['165','171'])).

thf('173',plain,(
    v1_funct_1 @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['64','65','66','67','68','77'])).

thf('174',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['159','163','164','172','173'])).

thf('175',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('176',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['174','175'])).

thf('177',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['174','175'])).

thf('178',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['174','175'])).

thf('179',plain,(
    ! [X5: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('180',plain,(
    ! [X4: $i] :
      ( ( ( k1_relat_1 @ X4 )
       != k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('181',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k6_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,(
    ! [X7: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('183',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( k6_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['181','182'])).

thf('184',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['183'])).

thf('185',plain,(
    ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','176','177','178','184'])).

thf('186',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    ! [X54: $i,X55: $i] :
      ( ( ( k1_relset_1 @ X54 @ X54 @ X55 )
        = X54 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X54 ) ) )
      | ~ ( v1_funct_2 @ X55 @ X54 @ X54 )
      | ~ ( v1_funct_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('188',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_C )
      = sk_A ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k1_relset_1 @ X11 @ X12 @ X10 )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('193',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['191','192'])).

thf('194',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['188','189','190','193'])).

thf('195',plain,(
    ! [X4: $i] :
      ( ( ( k1_relat_1 @ X4 )
       != k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('196',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('199',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['197','198'])).

thf('200',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('201',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['199','200'])).

thf('202',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['196','201'])).

thf('203',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['174','175'])).

thf('204',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['202','203'])).

thf('205',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['204'])).

thf('206',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['183'])).

thf('207',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('208',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['206','207'])).

thf('209',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r2_relset_1 @ X23 @ X24 @ X25 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('210',plain,(
    r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['208','209'])).

thf('211',plain,(
    $false ),
    inference(demod,[status(thm)],['185','205','210'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IQtrkOLJnJ
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:31:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 9.20/9.41  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 9.20/9.41  % Solved by: fo/fo7.sh
% 9.20/9.41  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 9.20/9.41  % done 9729 iterations in 8.950s
% 9.20/9.41  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 9.20/9.41  % SZS output start Refutation
% 9.20/9.41  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 9.20/9.41  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 9.20/9.41  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 9.20/9.41  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 9.20/9.41  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 9.20/9.41  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 9.20/9.41  thf(sk_C_type, type, sk_C: $i).
% 9.20/9.41  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 9.20/9.41  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 9.20/9.41  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 9.20/9.41  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 9.20/9.41  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 9.20/9.41  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 9.20/9.41  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 9.20/9.41  thf(sk_A_type, type, sk_A: $i).
% 9.20/9.41  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 9.20/9.41  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 9.20/9.41  thf(sk_B_type, type, sk_B: $i).
% 9.20/9.41  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 9.20/9.41  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 9.20/9.41  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 9.20/9.41  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 9.20/9.41  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 9.20/9.41  thf(t76_funct_2, conjecture,
% 9.20/9.41    (![A:$i,B:$i]:
% 9.20/9.41     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 9.20/9.41         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 9.20/9.41       ( ![C:$i]:
% 9.20/9.41         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 9.20/9.41             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 9.20/9.41           ( ( ( r2_relset_1 @
% 9.20/9.41                 A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ C @ B ) @ B ) & 
% 9.20/9.41               ( v2_funct_1 @ B ) ) =>
% 9.20/9.41             ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ))).
% 9.20/9.41  thf(zf_stmt_0, negated_conjecture,
% 9.20/9.41    (~( ![A:$i,B:$i]:
% 9.20/9.41        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 9.20/9.41            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 9.20/9.41          ( ![C:$i]:
% 9.20/9.41            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 9.20/9.41                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 9.20/9.41              ( ( ( r2_relset_1 @
% 9.20/9.41                    A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ C @ B ) @ B ) & 
% 9.20/9.41                  ( v2_funct_1 @ B ) ) =>
% 9.20/9.41                ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ) )),
% 9.20/9.41    inference('cnf.neg', [status(esa)], [t76_funct_2])).
% 9.20/9.41  thf('0', plain,
% 9.20/9.41      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_partfun1 @ sk_A))),
% 9.20/9.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.20/9.41  thf(redefinition_k6_partfun1, axiom,
% 9.20/9.41    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 9.20/9.41  thf('1', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 9.20/9.41      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 9.20/9.41  thf('2', plain, (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_relat_1 @ sk_A))),
% 9.20/9.41      inference('demod', [status(thm)], ['0', '1'])).
% 9.20/9.41  thf('3', plain,
% 9.20/9.41      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.20/9.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.20/9.41  thf(t67_funct_2, axiom,
% 9.20/9.41    (![A:$i,B:$i]:
% 9.20/9.41     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 9.20/9.41         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 9.20/9.41       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 9.20/9.41  thf('4', plain,
% 9.20/9.41      (![X54 : $i, X55 : $i]:
% 9.20/9.41         (((k1_relset_1 @ X54 @ X54 @ X55) = (X54))
% 9.20/9.41          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X54)))
% 9.20/9.41          | ~ (v1_funct_2 @ X55 @ X54 @ X54)
% 9.20/9.41          | ~ (v1_funct_1 @ X55))),
% 9.20/9.41      inference('cnf', [status(esa)], [t67_funct_2])).
% 9.20/9.41  thf('5', plain,
% 9.20/9.41      ((~ (v1_funct_1 @ sk_B)
% 9.20/9.41        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 9.20/9.41        | ((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A)))),
% 9.20/9.41      inference('sup-', [status(thm)], ['3', '4'])).
% 9.20/9.41  thf('6', plain, ((v1_funct_1 @ sk_B)),
% 9.20/9.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.20/9.41  thf('7', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 9.20/9.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.20/9.41  thf('8', plain,
% 9.20/9.41      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.20/9.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.20/9.41  thf(redefinition_k1_relset_1, axiom,
% 9.20/9.41    (![A:$i,B:$i,C:$i]:
% 9.20/9.41     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 9.20/9.41       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 9.20/9.41  thf('9', plain,
% 9.20/9.41      (![X10 : $i, X11 : $i, X12 : $i]:
% 9.20/9.41         (((k1_relset_1 @ X11 @ X12 @ X10) = (k1_relat_1 @ X10))
% 9.20/9.41          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 9.20/9.41      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 9.20/9.41  thf('10', plain,
% 9.20/9.41      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 9.20/9.41      inference('sup-', [status(thm)], ['8', '9'])).
% 9.20/9.41  thf('11', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 9.20/9.41      inference('demod', [status(thm)], ['5', '6', '7', '10'])).
% 9.20/9.41  thf(t3_funct_2, axiom,
% 9.20/9.41    (![A:$i]:
% 9.20/9.41     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 9.20/9.41       ( ( v1_funct_1 @ A ) & 
% 9.20/9.41         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 9.20/9.41         ( m1_subset_1 @
% 9.20/9.41           A @ 
% 9.20/9.41           ( k1_zfmisc_1 @
% 9.20/9.41             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 9.20/9.41  thf('12', plain,
% 9.20/9.41      (![X53 : $i]:
% 9.20/9.41         ((m1_subset_1 @ X53 @ 
% 9.20/9.41           (k1_zfmisc_1 @ 
% 9.20/9.41            (k2_zfmisc_1 @ (k1_relat_1 @ X53) @ (k2_relat_1 @ X53))))
% 9.20/9.41          | ~ (v1_funct_1 @ X53)
% 9.20/9.41          | ~ (v1_relat_1 @ X53))),
% 9.20/9.41      inference('cnf', [status(esa)], [t3_funct_2])).
% 9.20/9.41  thf('13', plain,
% 9.20/9.41      (((m1_subset_1 @ sk_B @ 
% 9.20/9.41         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B))))
% 9.20/9.41        | ~ (v1_relat_1 @ sk_B)
% 9.20/9.41        | ~ (v1_funct_1 @ sk_B))),
% 9.20/9.41      inference('sup+', [status(thm)], ['11', '12'])).
% 9.20/9.41  thf('14', plain,
% 9.20/9.41      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.20/9.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.20/9.41  thf(cc2_relat_1, axiom,
% 9.20/9.41    (![A:$i]:
% 9.20/9.41     ( ( v1_relat_1 @ A ) =>
% 9.20/9.41       ( ![B:$i]:
% 9.20/9.41         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 9.20/9.41  thf('15', plain,
% 9.20/9.41      (![X0 : $i, X1 : $i]:
% 9.20/9.41         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 9.20/9.41          | (v1_relat_1 @ X0)
% 9.20/9.41          | ~ (v1_relat_1 @ X1))),
% 9.20/9.41      inference('cnf', [status(esa)], [cc2_relat_1])).
% 9.20/9.41  thf('16', plain,
% 9.20/9.41      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 9.20/9.41      inference('sup-', [status(thm)], ['14', '15'])).
% 9.20/9.41  thf(fc6_relat_1, axiom,
% 9.20/9.41    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 9.20/9.41  thf('17', plain,
% 9.20/9.41      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 9.20/9.41      inference('cnf', [status(esa)], [fc6_relat_1])).
% 9.20/9.41  thf('18', plain, ((v1_relat_1 @ sk_B)),
% 9.20/9.41      inference('demod', [status(thm)], ['16', '17'])).
% 9.20/9.41  thf('19', plain, ((v1_funct_1 @ sk_B)),
% 9.20/9.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.20/9.41  thf('20', plain,
% 9.20/9.41      ((m1_subset_1 @ sk_B @ 
% 9.20/9.41        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B))))),
% 9.20/9.41      inference('demod', [status(thm)], ['13', '18', '19'])).
% 9.20/9.41  thf(t31_funct_2, axiom,
% 9.20/9.41    (![A:$i,B:$i,C:$i]:
% 9.20/9.41     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 9.20/9.41         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 9.20/9.41       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 9.20/9.41         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 9.20/9.41           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 9.20/9.41           ( m1_subset_1 @
% 9.20/9.41             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 9.20/9.41  thf('21', plain,
% 9.20/9.41      (![X50 : $i, X51 : $i, X52 : $i]:
% 9.20/9.41         (~ (v2_funct_1 @ X50)
% 9.20/9.41          | ((k2_relset_1 @ X52 @ X51 @ X50) != (X51))
% 9.20/9.41          | (m1_subset_1 @ (k2_funct_1 @ X50) @ 
% 9.20/9.41             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52)))
% 9.20/9.41          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X51)))
% 9.20/9.41          | ~ (v1_funct_2 @ X50 @ X52 @ X51)
% 9.20/9.41          | ~ (v1_funct_1 @ X50))),
% 9.20/9.41      inference('cnf', [status(esa)], [t31_funct_2])).
% 9.20/9.41  thf('22', plain,
% 9.20/9.41      ((~ (v1_funct_1 @ sk_B)
% 9.20/9.41        | ~ (v1_funct_2 @ sk_B @ sk_A @ (k2_relat_1 @ sk_B))
% 9.20/9.41        | (m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 9.20/9.41           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_B) @ sk_A)))
% 9.20/9.41        | ((k2_relset_1 @ sk_A @ (k2_relat_1 @ sk_B) @ sk_B)
% 9.20/9.41            != (k2_relat_1 @ sk_B))
% 9.20/9.41        | ~ (v2_funct_1 @ sk_B))),
% 9.20/9.41      inference('sup-', [status(thm)], ['20', '21'])).
% 9.20/9.41  thf('23', plain, ((v1_funct_1 @ sk_B)),
% 9.20/9.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.20/9.41  thf('24', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 9.20/9.41      inference('demod', [status(thm)], ['5', '6', '7', '10'])).
% 9.20/9.41  thf('25', plain,
% 9.20/9.41      (![X53 : $i]:
% 9.20/9.41         ((v1_funct_2 @ X53 @ (k1_relat_1 @ X53) @ (k2_relat_1 @ X53))
% 9.20/9.41          | ~ (v1_funct_1 @ X53)
% 9.20/9.41          | ~ (v1_relat_1 @ X53))),
% 9.20/9.41      inference('cnf', [status(esa)], [t3_funct_2])).
% 9.20/9.41  thf('26', plain,
% 9.20/9.41      (((v1_funct_2 @ sk_B @ sk_A @ (k2_relat_1 @ sk_B))
% 9.20/9.41        | ~ (v1_relat_1 @ sk_B)
% 9.20/9.41        | ~ (v1_funct_1 @ sk_B))),
% 9.20/9.41      inference('sup+', [status(thm)], ['24', '25'])).
% 9.20/9.41  thf('27', plain, ((v1_relat_1 @ sk_B)),
% 9.20/9.41      inference('demod', [status(thm)], ['16', '17'])).
% 9.20/9.41  thf('28', plain, ((v1_funct_1 @ sk_B)),
% 9.20/9.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.20/9.41  thf('29', plain, ((v1_funct_2 @ sk_B @ sk_A @ (k2_relat_1 @ sk_B))),
% 9.20/9.41      inference('demod', [status(thm)], ['26', '27', '28'])).
% 9.20/9.41  thf('30', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 9.20/9.41      inference('demod', [status(thm)], ['5', '6', '7', '10'])).
% 9.20/9.41  thf('31', plain,
% 9.20/9.41      (![X53 : $i]:
% 9.20/9.41         ((m1_subset_1 @ X53 @ 
% 9.20/9.41           (k1_zfmisc_1 @ 
% 9.20/9.41            (k2_zfmisc_1 @ (k1_relat_1 @ X53) @ (k2_relat_1 @ X53))))
% 9.20/9.41          | ~ (v1_funct_1 @ X53)
% 9.20/9.41          | ~ (v1_relat_1 @ X53))),
% 9.20/9.41      inference('cnf', [status(esa)], [t3_funct_2])).
% 9.20/9.41  thf(redefinition_k2_relset_1, axiom,
% 9.20/9.41    (![A:$i,B:$i,C:$i]:
% 9.20/9.41     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 9.20/9.41       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 9.20/9.41  thf('32', plain,
% 9.20/9.41      (![X13 : $i, X14 : $i, X15 : $i]:
% 9.20/9.41         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 9.20/9.41          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 9.20/9.41      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 9.20/9.41  thf('33', plain,
% 9.20/9.41      (![X0 : $i]:
% 9.20/9.41         (~ (v1_relat_1 @ X0)
% 9.20/9.41          | ~ (v1_funct_1 @ X0)
% 9.20/9.41          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 9.20/9.41              = (k2_relat_1 @ X0)))),
% 9.20/9.41      inference('sup-', [status(thm)], ['31', '32'])).
% 9.20/9.41  thf('34', plain,
% 9.20/9.41      ((((k2_relset_1 @ sk_A @ (k2_relat_1 @ sk_B) @ sk_B)
% 9.20/9.41          = (k2_relat_1 @ sk_B))
% 9.20/9.41        | ~ (v1_funct_1 @ sk_B)
% 9.20/9.41        | ~ (v1_relat_1 @ sk_B))),
% 9.20/9.41      inference('sup+', [status(thm)], ['30', '33'])).
% 9.20/9.41  thf('35', plain, ((v1_funct_1 @ sk_B)),
% 9.20/9.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.20/9.41  thf('36', plain, ((v1_relat_1 @ sk_B)),
% 9.20/9.41      inference('demod', [status(thm)], ['16', '17'])).
% 9.20/9.41  thf('37', plain,
% 9.20/9.41      (((k2_relset_1 @ sk_A @ (k2_relat_1 @ sk_B) @ sk_B) = (k2_relat_1 @ sk_B))),
% 9.20/9.41      inference('demod', [status(thm)], ['34', '35', '36'])).
% 9.20/9.41  thf('38', plain, ((v2_funct_1 @ sk_B)),
% 9.20/9.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.20/9.41  thf('39', plain,
% 9.20/9.41      (((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 9.20/9.41         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_B) @ sk_A)))
% 9.20/9.41        | ((k2_relat_1 @ sk_B) != (k2_relat_1 @ sk_B)))),
% 9.20/9.41      inference('demod', [status(thm)], ['22', '23', '29', '37', '38'])).
% 9.20/9.41  thf('40', plain,
% 9.20/9.41      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 9.20/9.41        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_B) @ sk_A)))),
% 9.20/9.41      inference('simplify', [status(thm)], ['39'])).
% 9.20/9.41  thf('41', plain,
% 9.20/9.41      (![X0 : $i, X1 : $i]:
% 9.20/9.41         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 9.20/9.41          | (v1_relat_1 @ X0)
% 9.20/9.41          | ~ (v1_relat_1 @ X1))),
% 9.20/9.41      inference('cnf', [status(esa)], [cc2_relat_1])).
% 9.20/9.41  thf('42', plain,
% 9.20/9.41      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_B) @ sk_A))
% 9.20/9.41        | (v1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 9.20/9.41      inference('sup-', [status(thm)], ['40', '41'])).
% 9.20/9.41  thf('43', plain,
% 9.20/9.41      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 9.20/9.41      inference('cnf', [status(esa)], [fc6_relat_1])).
% 9.20/9.41  thf('44', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 9.20/9.41      inference('demod', [status(thm)], ['42', '43'])).
% 9.20/9.41  thf(t61_funct_1, axiom,
% 9.20/9.41    (![A:$i]:
% 9.20/9.41     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 9.20/9.41       ( ( v2_funct_1 @ A ) =>
% 9.20/9.41         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 9.20/9.41             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 9.20/9.41           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 9.20/9.41             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 9.20/9.41  thf('45', plain,
% 9.20/9.41      (![X9 : $i]:
% 9.20/9.41         (~ (v2_funct_1 @ X9)
% 9.20/9.41          | ((k5_relat_1 @ X9 @ (k2_funct_1 @ X9))
% 9.20/9.41              = (k6_relat_1 @ (k1_relat_1 @ X9)))
% 9.20/9.41          | ~ (v1_funct_1 @ X9)
% 9.20/9.41          | ~ (v1_relat_1 @ X9))),
% 9.20/9.41      inference('cnf', [status(esa)], [t61_funct_1])).
% 9.20/9.41  thf('46', plain,
% 9.20/9.41      (![X53 : $i]:
% 9.20/9.41         ((m1_subset_1 @ X53 @ 
% 9.20/9.41           (k1_zfmisc_1 @ 
% 9.20/9.41            (k2_zfmisc_1 @ (k1_relat_1 @ X53) @ (k2_relat_1 @ X53))))
% 9.20/9.41          | ~ (v1_funct_1 @ X53)
% 9.20/9.41          | ~ (v1_relat_1 @ X53))),
% 9.20/9.41      inference('cnf', [status(esa)], [t3_funct_2])).
% 9.20/9.41  thf('47', plain,
% 9.20/9.41      (![X53 : $i]:
% 9.20/9.41         ((m1_subset_1 @ X53 @ 
% 9.20/9.41           (k1_zfmisc_1 @ 
% 9.20/9.41            (k2_zfmisc_1 @ (k1_relat_1 @ X53) @ (k2_relat_1 @ X53))))
% 9.20/9.41          | ~ (v1_funct_1 @ X53)
% 9.20/9.41          | ~ (v1_relat_1 @ X53))),
% 9.20/9.41      inference('cnf', [status(esa)], [t3_funct_2])).
% 9.20/9.41  thf(redefinition_k1_partfun1, axiom,
% 9.20/9.41    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 9.20/9.41     ( ( ( v1_funct_1 @ E ) & 
% 9.20/9.41         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 9.20/9.41         ( v1_funct_1 @ F ) & 
% 9.20/9.41         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 9.20/9.41       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 9.20/9.41  thf('48', plain,
% 9.20/9.41      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 9.20/9.41         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 9.20/9.41          | ~ (v1_funct_1 @ X34)
% 9.20/9.41          | ~ (v1_funct_1 @ X37)
% 9.20/9.41          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 9.20/9.41          | ((k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37)
% 9.20/9.41              = (k5_relat_1 @ X34 @ X37)))),
% 9.20/9.41      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 9.20/9.41  thf('49', plain,
% 9.20/9.41      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 9.20/9.41         (~ (v1_relat_1 @ X0)
% 9.20/9.41          | ~ (v1_funct_1 @ X0)
% 9.20/9.41          | ((k1_partfun1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X3 @ X2 @ 
% 9.20/9.41              X0 @ X1) = (k5_relat_1 @ X0 @ X1))
% 9.20/9.41          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2)))
% 9.20/9.41          | ~ (v1_funct_1 @ X1)
% 9.20/9.41          | ~ (v1_funct_1 @ X0))),
% 9.20/9.41      inference('sup-', [status(thm)], ['47', '48'])).
% 9.20/9.41  thf('50', plain,
% 9.20/9.41      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 9.20/9.41         (~ (v1_funct_1 @ X1)
% 9.20/9.41          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2)))
% 9.20/9.41          | ((k1_partfun1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X3 @ X2 @ 
% 9.20/9.41              X0 @ X1) = (k5_relat_1 @ X0 @ X1))
% 9.20/9.41          | ~ (v1_funct_1 @ X0)
% 9.20/9.41          | ~ (v1_relat_1 @ X0))),
% 9.20/9.41      inference('simplify', [status(thm)], ['49'])).
% 9.20/9.41  thf('51', plain,
% 9.20/9.41      (![X0 : $i, X1 : $i]:
% 9.20/9.41         (~ (v1_relat_1 @ X0)
% 9.20/9.41          | ~ (v1_funct_1 @ X0)
% 9.20/9.41          | ~ (v1_relat_1 @ X1)
% 9.20/9.41          | ~ (v1_funct_1 @ X1)
% 9.20/9.41          | ((k1_partfun1 @ (k1_relat_1 @ X1) @ (k2_relat_1 @ X1) @ 
% 9.20/9.41              (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X1 @ X0)
% 9.20/9.41              = (k5_relat_1 @ X1 @ X0))
% 9.20/9.41          | ~ (v1_funct_1 @ X0))),
% 9.20/9.41      inference('sup-', [status(thm)], ['46', '50'])).
% 9.20/9.41  thf('52', plain,
% 9.20/9.41      (![X0 : $i, X1 : $i]:
% 9.20/9.41         (((k1_partfun1 @ (k1_relat_1 @ X1) @ (k2_relat_1 @ X1) @ 
% 9.20/9.41            (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X1 @ X0)
% 9.20/9.41            = (k5_relat_1 @ X1 @ X0))
% 9.20/9.41          | ~ (v1_funct_1 @ X1)
% 9.20/9.41          | ~ (v1_relat_1 @ X1)
% 9.20/9.41          | ~ (v1_funct_1 @ X0)
% 9.20/9.41          | ~ (v1_relat_1 @ X0))),
% 9.20/9.41      inference('simplify', [status(thm)], ['51'])).
% 9.20/9.41  thf('53', plain,
% 9.20/9.41      (![X53 : $i]:
% 9.20/9.41         ((m1_subset_1 @ X53 @ 
% 9.20/9.41           (k1_zfmisc_1 @ 
% 9.20/9.41            (k2_zfmisc_1 @ (k1_relat_1 @ X53) @ (k2_relat_1 @ X53))))
% 9.20/9.41          | ~ (v1_funct_1 @ X53)
% 9.20/9.41          | ~ (v1_relat_1 @ X53))),
% 9.20/9.41      inference('cnf', [status(esa)], [t3_funct_2])).
% 9.20/9.41  thf('54', plain,
% 9.20/9.41      (![X53 : $i]:
% 9.20/9.41         ((m1_subset_1 @ X53 @ 
% 9.20/9.41           (k1_zfmisc_1 @ 
% 9.20/9.41            (k2_zfmisc_1 @ (k1_relat_1 @ X53) @ (k2_relat_1 @ X53))))
% 9.20/9.41          | ~ (v1_funct_1 @ X53)
% 9.20/9.41          | ~ (v1_relat_1 @ X53))),
% 9.20/9.41      inference('cnf', [status(esa)], [t3_funct_2])).
% 9.20/9.41  thf(dt_k1_partfun1, axiom,
% 9.20/9.41    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 9.20/9.41     ( ( ( v1_funct_1 @ E ) & 
% 9.20/9.41         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 9.20/9.41         ( v1_funct_1 @ F ) & 
% 9.20/9.41         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 9.20/9.41       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 9.20/9.41         ( m1_subset_1 @
% 9.20/9.41           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 9.20/9.41           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 9.20/9.41  thf('55', plain,
% 9.20/9.41      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 9.20/9.41         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 9.20/9.41          | ~ (v1_funct_1 @ X26)
% 9.20/9.41          | ~ (v1_funct_1 @ X29)
% 9.20/9.41          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 9.20/9.41          | (v1_funct_1 @ (k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29)))),
% 9.20/9.41      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 9.20/9.41  thf('56', plain,
% 9.20/9.41      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 9.20/9.41         (~ (v1_relat_1 @ X0)
% 9.20/9.41          | ~ (v1_funct_1 @ X0)
% 9.20/9.41          | (v1_funct_1 @ 
% 9.20/9.41             (k1_partfun1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X3 @ X2 @ 
% 9.20/9.41              X0 @ X1))
% 9.20/9.41          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2)))
% 9.20/9.41          | ~ (v1_funct_1 @ X1)
% 9.20/9.41          | ~ (v1_funct_1 @ X0))),
% 9.20/9.41      inference('sup-', [status(thm)], ['54', '55'])).
% 9.20/9.41  thf('57', plain,
% 9.20/9.41      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 9.20/9.41         (~ (v1_funct_1 @ X1)
% 9.20/9.41          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2)))
% 9.20/9.41          | (v1_funct_1 @ 
% 9.20/9.41             (k1_partfun1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X3 @ X2 @ 
% 9.20/9.41              X0 @ X1))
% 9.20/9.41          | ~ (v1_funct_1 @ X0)
% 9.20/9.41          | ~ (v1_relat_1 @ X0))),
% 9.20/9.41      inference('simplify', [status(thm)], ['56'])).
% 9.20/9.41  thf('58', plain,
% 9.20/9.41      (![X0 : $i, X1 : $i]:
% 9.20/9.41         (~ (v1_relat_1 @ X0)
% 9.20/9.41          | ~ (v1_funct_1 @ X0)
% 9.20/9.41          | ~ (v1_relat_1 @ X1)
% 9.20/9.41          | ~ (v1_funct_1 @ X1)
% 9.20/9.41          | (v1_funct_1 @ 
% 9.20/9.41             (k1_partfun1 @ (k1_relat_1 @ X1) @ (k2_relat_1 @ X1) @ 
% 9.20/9.41              (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X1 @ X0))
% 9.20/9.41          | ~ (v1_funct_1 @ X0))),
% 9.20/9.41      inference('sup-', [status(thm)], ['53', '57'])).
% 9.20/9.41  thf('59', plain,
% 9.20/9.41      (![X0 : $i, X1 : $i]:
% 9.20/9.41         ((v1_funct_1 @ 
% 9.20/9.41           (k1_partfun1 @ (k1_relat_1 @ X1) @ (k2_relat_1 @ X1) @ 
% 9.20/9.41            (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X1 @ X0))
% 9.20/9.41          | ~ (v1_funct_1 @ X1)
% 9.20/9.41          | ~ (v1_relat_1 @ X1)
% 9.20/9.41          | ~ (v1_funct_1 @ X0)
% 9.20/9.41          | ~ (v1_relat_1 @ X0))),
% 9.20/9.41      inference('simplify', [status(thm)], ['58'])).
% 9.20/9.41  thf('60', plain,
% 9.20/9.41      (![X0 : $i, X1 : $i]:
% 9.20/9.41         ((v1_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 9.20/9.41          | ~ (v1_relat_1 @ X0)
% 9.20/9.41          | ~ (v1_funct_1 @ X0)
% 9.20/9.41          | ~ (v1_relat_1 @ X1)
% 9.20/9.41          | ~ (v1_funct_1 @ X1)
% 9.20/9.41          | ~ (v1_relat_1 @ X0)
% 9.20/9.41          | ~ (v1_funct_1 @ X0)
% 9.20/9.41          | ~ (v1_relat_1 @ X1)
% 9.20/9.41          | ~ (v1_funct_1 @ X1))),
% 9.20/9.41      inference('sup+', [status(thm)], ['52', '59'])).
% 9.20/9.41  thf('61', plain,
% 9.20/9.41      (![X0 : $i, X1 : $i]:
% 9.20/9.41         (~ (v1_funct_1 @ X1)
% 9.20/9.41          | ~ (v1_relat_1 @ X1)
% 9.20/9.41          | ~ (v1_funct_1 @ X0)
% 9.20/9.41          | ~ (v1_relat_1 @ X0)
% 9.20/9.41          | (v1_funct_1 @ (k5_relat_1 @ X1 @ X0)))),
% 9.20/9.41      inference('simplify', [status(thm)], ['60'])).
% 9.20/9.41  thf('62', plain,
% 9.20/9.41      (![X0 : $i]:
% 9.20/9.41         ((v1_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 9.20/9.41          | ~ (v1_relat_1 @ X0)
% 9.20/9.41          | ~ (v1_funct_1 @ X0)
% 9.20/9.41          | ~ (v2_funct_1 @ X0)
% 9.20/9.41          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 9.20/9.41          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 9.20/9.41          | ~ (v1_relat_1 @ X0)
% 9.20/9.41          | ~ (v1_funct_1 @ X0))),
% 9.20/9.41      inference('sup+', [status(thm)], ['45', '61'])).
% 9.20/9.41  thf('63', plain,
% 9.20/9.41      (![X0 : $i]:
% 9.20/9.41         (~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 9.20/9.41          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 9.20/9.41          | ~ (v2_funct_1 @ X0)
% 9.20/9.41          | ~ (v1_funct_1 @ X0)
% 9.20/9.41          | ~ (v1_relat_1 @ X0)
% 9.20/9.41          | (v1_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ X0))))),
% 9.20/9.41      inference('simplify', [status(thm)], ['62'])).
% 9.20/9.41  thf('64', plain,
% 9.20/9.41      (((v1_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 9.20/9.41        | ~ (v1_relat_1 @ sk_B)
% 9.20/9.41        | ~ (v1_funct_1 @ sk_B)
% 9.20/9.41        | ~ (v2_funct_1 @ sk_B)
% 9.20/9.41        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 9.20/9.41      inference('sup-', [status(thm)], ['44', '63'])).
% 9.20/9.41  thf('65', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 9.20/9.41      inference('demod', [status(thm)], ['5', '6', '7', '10'])).
% 9.20/9.41  thf('66', plain, ((v1_relat_1 @ sk_B)),
% 9.20/9.41      inference('demod', [status(thm)], ['16', '17'])).
% 9.20/9.41  thf('67', plain, ((v1_funct_1 @ sk_B)),
% 9.20/9.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.20/9.41  thf('68', plain, ((v2_funct_1 @ sk_B)),
% 9.20/9.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.20/9.41  thf('69', plain,
% 9.20/9.41      ((m1_subset_1 @ sk_B @ 
% 9.20/9.41        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B))))),
% 9.20/9.41      inference('demod', [status(thm)], ['13', '18', '19'])).
% 9.20/9.41  thf('70', plain,
% 9.20/9.41      (![X50 : $i, X51 : $i, X52 : $i]:
% 9.20/9.41         (~ (v2_funct_1 @ X50)
% 9.20/9.41          | ((k2_relset_1 @ X52 @ X51 @ X50) != (X51))
% 9.20/9.41          | (v1_funct_1 @ (k2_funct_1 @ X50))
% 9.20/9.41          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X51)))
% 9.20/9.41          | ~ (v1_funct_2 @ X50 @ X52 @ X51)
% 9.20/9.41          | ~ (v1_funct_1 @ X50))),
% 9.20/9.41      inference('cnf', [status(esa)], [t31_funct_2])).
% 9.20/9.41  thf('71', plain,
% 9.20/9.41      ((~ (v1_funct_1 @ sk_B)
% 9.20/9.41        | ~ (v1_funct_2 @ sk_B @ sk_A @ (k2_relat_1 @ sk_B))
% 9.20/9.41        | (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 9.20/9.41        | ((k2_relset_1 @ sk_A @ (k2_relat_1 @ sk_B) @ sk_B)
% 9.20/9.41            != (k2_relat_1 @ sk_B))
% 9.20/9.41        | ~ (v2_funct_1 @ sk_B))),
% 9.20/9.41      inference('sup-', [status(thm)], ['69', '70'])).
% 9.20/9.41  thf('72', plain, ((v1_funct_1 @ sk_B)),
% 9.20/9.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.20/9.41  thf('73', plain, ((v1_funct_2 @ sk_B @ sk_A @ (k2_relat_1 @ sk_B))),
% 9.20/9.41      inference('demod', [status(thm)], ['26', '27', '28'])).
% 9.20/9.41  thf('74', plain,
% 9.20/9.41      (((k2_relset_1 @ sk_A @ (k2_relat_1 @ sk_B) @ sk_B) = (k2_relat_1 @ sk_B))),
% 9.20/9.41      inference('demod', [status(thm)], ['34', '35', '36'])).
% 9.20/9.41  thf('75', plain, ((v2_funct_1 @ sk_B)),
% 9.20/9.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.20/9.41  thf('76', plain,
% 9.20/9.41      (((v1_funct_1 @ (k2_funct_1 @ sk_B))
% 9.20/9.41        | ((k2_relat_1 @ sk_B) != (k2_relat_1 @ sk_B)))),
% 9.20/9.41      inference('demod', [status(thm)], ['71', '72', '73', '74', '75'])).
% 9.20/9.41  thf('77', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 9.20/9.41      inference('simplify', [status(thm)], ['76'])).
% 9.20/9.41  thf('78', plain, ((v1_funct_1 @ (k6_relat_1 @ sk_A))),
% 9.20/9.41      inference('demod', [status(thm)], ['64', '65', '66', '67', '68', '77'])).
% 9.20/9.41  thf('79', plain,
% 9.20/9.41      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.20/9.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.20/9.41  thf(dt_k6_partfun1, axiom,
% 9.20/9.41    (![A:$i]:
% 9.20/9.41     ( ( m1_subset_1 @
% 9.20/9.41         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 9.20/9.41       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 9.20/9.41  thf('80', plain,
% 9.20/9.41      (![X33 : $i]:
% 9.20/9.41         (m1_subset_1 @ (k6_partfun1 @ X33) @ 
% 9.20/9.41          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))),
% 9.20/9.41      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 9.20/9.41  thf('81', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 9.20/9.41      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 9.20/9.41  thf('82', plain,
% 9.20/9.41      (![X33 : $i]:
% 9.20/9.41         (m1_subset_1 @ (k6_relat_1 @ X33) @ 
% 9.20/9.41          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))),
% 9.20/9.41      inference('demod', [status(thm)], ['80', '81'])).
% 9.20/9.41  thf('83', plain,
% 9.20/9.41      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 9.20/9.41         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 9.20/9.41          | ~ (v1_funct_1 @ X34)
% 9.20/9.41          | ~ (v1_funct_1 @ X37)
% 9.20/9.41          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 9.20/9.41          | ((k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37)
% 9.20/9.41              = (k5_relat_1 @ X34 @ X37)))),
% 9.20/9.41      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 9.20/9.41  thf('84', plain,
% 9.20/9.41      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 9.20/9.41         (((k1_partfun1 @ X0 @ X0 @ X3 @ X2 @ (k6_relat_1 @ X0) @ X1)
% 9.20/9.41            = (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 9.20/9.41          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2)))
% 9.20/9.41          | ~ (v1_funct_1 @ X1)
% 9.20/9.41          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 9.20/9.41      inference('sup-', [status(thm)], ['82', '83'])).
% 9.20/9.41  thf('85', plain,
% 9.20/9.41      (![X0 : $i]:
% 9.20/9.41         (~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 9.20/9.41          | ~ (v1_funct_1 @ sk_B)
% 9.20/9.41          | ((k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ (k6_relat_1 @ X0) @ sk_B)
% 9.20/9.41              = (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_B)))),
% 9.20/9.41      inference('sup-', [status(thm)], ['79', '84'])).
% 9.20/9.41  thf('86', plain, ((v1_funct_1 @ sk_B)),
% 9.20/9.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.20/9.41  thf('87', plain,
% 9.20/9.41      (![X0 : $i]:
% 9.20/9.41         (~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 9.20/9.41          | ((k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ (k6_relat_1 @ X0) @ sk_B)
% 9.20/9.41              = (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_B)))),
% 9.20/9.41      inference('demod', [status(thm)], ['85', '86'])).
% 9.20/9.41  thf('88', plain,
% 9.20/9.41      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ sk_B)
% 9.20/9.41         = (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 9.20/9.41      inference('sup-', [status(thm)], ['78', '87'])).
% 9.20/9.41  thf('89', plain,
% 9.20/9.41      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.20/9.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.20/9.41  thf(t23_funct_2, axiom,
% 9.20/9.41    (![A:$i,B:$i,C:$i]:
% 9.20/9.41     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 9.20/9.41       ( ( r2_relset_1 @
% 9.20/9.41           A @ B @ ( k4_relset_1 @ A @ A @ A @ B @ ( k6_partfun1 @ A ) @ C ) @ 
% 9.20/9.41           C ) & 
% 9.20/9.41         ( r2_relset_1 @
% 9.20/9.41           A @ B @ ( k4_relset_1 @ A @ B @ B @ B @ C @ ( k6_partfun1 @ B ) ) @ 
% 9.20/9.41           C ) ) ))).
% 9.20/9.41  thf('90', plain,
% 9.20/9.41      (![X41 : $i, X42 : $i, X43 : $i]:
% 9.20/9.41         ((r2_relset_1 @ X41 @ X42 @ 
% 9.20/9.41           (k4_relset_1 @ X41 @ X41 @ X41 @ X42 @ (k6_partfun1 @ X41) @ X43) @ 
% 9.20/9.41           X43)
% 9.20/9.41          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42))))),
% 9.20/9.41      inference('cnf', [status(esa)], [t23_funct_2])).
% 9.20/9.41  thf('91', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 9.20/9.41      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 9.20/9.41  thf('92', plain,
% 9.20/9.41      (![X41 : $i, X42 : $i, X43 : $i]:
% 9.20/9.41         ((r2_relset_1 @ X41 @ X42 @ 
% 9.20/9.41           (k4_relset_1 @ X41 @ X41 @ X41 @ X42 @ (k6_relat_1 @ X41) @ X43) @ 
% 9.20/9.41           X43)
% 9.20/9.41          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42))))),
% 9.20/9.41      inference('demod', [status(thm)], ['90', '91'])).
% 9.20/9.41  thf('93', plain,
% 9.20/9.41      ((r2_relset_1 @ sk_A @ sk_A @ 
% 9.20/9.41        (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ sk_B) @ 
% 9.20/9.41        sk_B)),
% 9.20/9.41      inference('sup-', [status(thm)], ['89', '92'])).
% 9.20/9.41  thf('94', plain,
% 9.20/9.41      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.20/9.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.20/9.41  thf('95', plain,
% 9.20/9.41      (![X33 : $i]:
% 9.20/9.41         (m1_subset_1 @ (k6_relat_1 @ X33) @ 
% 9.20/9.41          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))),
% 9.20/9.41      inference('demod', [status(thm)], ['80', '81'])).
% 9.20/9.41  thf(redefinition_k4_relset_1, axiom,
% 9.20/9.41    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 9.20/9.41     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 9.20/9.41         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 9.20/9.41       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 9.20/9.41  thf('96', plain,
% 9.20/9.41      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 9.20/9.41         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 9.20/9.41          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 9.20/9.41          | ((k4_relset_1 @ X17 @ X18 @ X20 @ X21 @ X16 @ X19)
% 9.20/9.41              = (k5_relat_1 @ X16 @ X19)))),
% 9.20/9.41      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 9.20/9.41  thf('97', plain,
% 9.20/9.41      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 9.20/9.41         (((k4_relset_1 @ X0 @ X0 @ X3 @ X2 @ (k6_relat_1 @ X0) @ X1)
% 9.20/9.41            = (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 9.20/9.41          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2))))),
% 9.20/9.41      inference('sup-', [status(thm)], ['95', '96'])).
% 9.20/9.41  thf('98', plain,
% 9.20/9.41      (![X0 : $i]:
% 9.20/9.41         ((k4_relset_1 @ X0 @ X0 @ sk_A @ sk_A @ (k6_relat_1 @ X0) @ sk_B)
% 9.20/9.41           = (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_B))),
% 9.20/9.41      inference('sup-', [status(thm)], ['94', '97'])).
% 9.20/9.41  thf('99', plain,
% 9.20/9.41      ((r2_relset_1 @ sk_A @ sk_A @ 
% 9.20/9.41        (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) @ sk_B)),
% 9.20/9.41      inference('demod', [status(thm)], ['93', '98'])).
% 9.20/9.41  thf('100', plain, ((v1_funct_1 @ (k6_relat_1 @ sk_A))),
% 9.20/9.41      inference('demod', [status(thm)], ['64', '65', '66', '67', '68', '77'])).
% 9.20/9.41  thf('101', plain,
% 9.20/9.41      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.20/9.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.20/9.41  thf('102', plain,
% 9.20/9.41      (![X33 : $i]:
% 9.20/9.41         (m1_subset_1 @ (k6_relat_1 @ X33) @ 
% 9.20/9.41          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))),
% 9.20/9.41      inference('demod', [status(thm)], ['80', '81'])).
% 9.20/9.41  thf('103', plain,
% 9.20/9.41      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 9.20/9.41         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 9.20/9.41          | ~ (v1_funct_1 @ X26)
% 9.20/9.41          | ~ (v1_funct_1 @ X29)
% 9.20/9.41          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 9.20/9.41          | (m1_subset_1 @ (k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29) @ 
% 9.20/9.41             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X31))))),
% 9.20/9.41      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 9.20/9.41  thf('104', plain,
% 9.20/9.41      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 9.20/9.41         ((m1_subset_1 @ 
% 9.20/9.41           (k1_partfun1 @ X0 @ X0 @ X3 @ X1 @ (k6_relat_1 @ X0) @ X2) @ 
% 9.20/9.41           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 9.20/9.41          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X1)))
% 9.20/9.41          | ~ (v1_funct_1 @ X2)
% 9.20/9.41          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 9.20/9.41      inference('sup-', [status(thm)], ['102', '103'])).
% 9.20/9.41  thf('105', plain,
% 9.20/9.41      (![X0 : $i]:
% 9.20/9.41         (~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 9.20/9.41          | ~ (v1_funct_1 @ sk_B)
% 9.20/9.41          | (m1_subset_1 @ 
% 9.20/9.41             (k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ (k6_relat_1 @ X0) @ sk_B) @ 
% 9.20/9.41             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_A))))),
% 9.20/9.41      inference('sup-', [status(thm)], ['101', '104'])).
% 9.20/9.41  thf('106', plain, ((v1_funct_1 @ sk_B)),
% 9.20/9.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.20/9.41  thf('107', plain,
% 9.20/9.41      (![X0 : $i]:
% 9.20/9.41         (~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 9.20/9.41          | (m1_subset_1 @ 
% 9.20/9.41             (k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ (k6_relat_1 @ X0) @ sk_B) @ 
% 9.20/9.41             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_A))))),
% 9.20/9.41      inference('demod', [status(thm)], ['105', '106'])).
% 9.20/9.41  thf('108', plain,
% 9.20/9.41      ((m1_subset_1 @ 
% 9.20/9.41        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ sk_B) @ 
% 9.20/9.41        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.20/9.41      inference('sup-', [status(thm)], ['100', '107'])).
% 9.20/9.41  thf('109', plain,
% 9.20/9.41      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ sk_B)
% 9.20/9.41         = (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 9.20/9.41      inference('sup-', [status(thm)], ['78', '87'])).
% 9.20/9.41  thf('110', plain,
% 9.20/9.41      ((m1_subset_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) @ 
% 9.20/9.41        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.20/9.41      inference('demod', [status(thm)], ['108', '109'])).
% 9.20/9.41  thf(redefinition_r2_relset_1, axiom,
% 9.20/9.41    (![A:$i,B:$i,C:$i,D:$i]:
% 9.20/9.41     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 9.20/9.41         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 9.20/9.41       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 9.20/9.41  thf('111', plain,
% 9.20/9.41      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 9.20/9.41         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 9.20/9.41          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 9.20/9.41          | ((X22) = (X25))
% 9.20/9.41          | ~ (r2_relset_1 @ X23 @ X24 @ X22 @ X25))),
% 9.20/9.41      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 9.20/9.41  thf('112', plain,
% 9.20/9.41      (![X0 : $i]:
% 9.20/9.41         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 9.20/9.41             (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) @ X0)
% 9.20/9.41          | ((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (X0))
% 9.20/9.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 9.20/9.41      inference('sup-', [status(thm)], ['110', '111'])).
% 9.20/9.41  thf('113', plain,
% 9.20/9.41      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 9.20/9.41        | ((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (sk_B)))),
% 9.20/9.41      inference('sup-', [status(thm)], ['99', '112'])).
% 9.20/9.41  thf('114', plain,
% 9.20/9.41      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.20/9.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.20/9.41  thf('115', plain, (((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (sk_B))),
% 9.20/9.41      inference('demod', [status(thm)], ['113', '114'])).
% 9.20/9.41  thf('116', plain,
% 9.20/9.41      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ sk_B)
% 9.20/9.41         = (sk_B))),
% 9.20/9.41      inference('demod', [status(thm)], ['88', '115'])).
% 9.20/9.41  thf('117', plain,
% 9.20/9.41      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.20/9.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.20/9.41  thf('118', plain,
% 9.20/9.41      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.20/9.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.20/9.41  thf('119', plain,
% 9.20/9.41      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 9.20/9.41         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 9.20/9.41          | ~ (v1_funct_1 @ X34)
% 9.20/9.41          | ~ (v1_funct_1 @ X37)
% 9.20/9.41          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 9.20/9.41          | ((k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37)
% 9.20/9.41              = (k5_relat_1 @ X34 @ X37)))),
% 9.20/9.41      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 9.20/9.41  thf('120', plain,
% 9.20/9.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.20/9.41         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0)
% 9.20/9.41            = (k5_relat_1 @ sk_C @ X0))
% 9.20/9.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 9.20/9.41          | ~ (v1_funct_1 @ X0)
% 9.20/9.41          | ~ (v1_funct_1 @ sk_C))),
% 9.20/9.41      inference('sup-', [status(thm)], ['118', '119'])).
% 9.20/9.41  thf('121', plain, ((v1_funct_1 @ sk_C)),
% 9.20/9.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.20/9.41  thf('122', plain,
% 9.20/9.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.20/9.41         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0)
% 9.20/9.41            = (k5_relat_1 @ sk_C @ X0))
% 9.20/9.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 9.20/9.41          | ~ (v1_funct_1 @ X0))),
% 9.20/9.41      inference('demod', [status(thm)], ['120', '121'])).
% 9.20/9.41  thf('123', plain,
% 9.20/9.41      ((~ (v1_funct_1 @ sk_B)
% 9.20/9.41        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)
% 9.20/9.41            = (k5_relat_1 @ sk_C @ sk_B)))),
% 9.20/9.41      inference('sup-', [status(thm)], ['117', '122'])).
% 9.20/9.41  thf('124', plain, ((v1_funct_1 @ sk_B)),
% 9.20/9.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.20/9.41  thf('125', plain,
% 9.20/9.41      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)
% 9.20/9.41         = (k5_relat_1 @ sk_C @ sk_B))),
% 9.20/9.41      inference('demod', [status(thm)], ['123', '124'])).
% 9.20/9.41  thf('126', plain,
% 9.20/9.41      ((r2_relset_1 @ sk_A @ sk_A @ 
% 9.20/9.41        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) @ sk_B)),
% 9.20/9.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.20/9.41  thf('127', plain,
% 9.20/9.41      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)
% 9.20/9.41         = (k5_relat_1 @ sk_C @ sk_B))),
% 9.20/9.41      inference('demod', [status(thm)], ['123', '124'])).
% 9.20/9.41  thf('128', plain,
% 9.20/9.41      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_B) @ sk_B)),
% 9.20/9.41      inference('demod', [status(thm)], ['126', '127'])).
% 9.20/9.41  thf('129', plain,
% 9.20/9.41      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.20/9.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.20/9.41  thf('130', plain,
% 9.20/9.41      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.20/9.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.20/9.41  thf('131', plain,
% 9.20/9.41      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 9.20/9.41         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 9.20/9.41          | ~ (v1_funct_1 @ X26)
% 9.20/9.41          | ~ (v1_funct_1 @ X29)
% 9.20/9.41          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 9.20/9.41          | (m1_subset_1 @ (k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29) @ 
% 9.20/9.41             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X31))))),
% 9.20/9.41      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 9.20/9.41  thf('132', plain,
% 9.20/9.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.20/9.41         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1) @ 
% 9.20/9.41           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 9.20/9.41          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 9.20/9.41          | ~ (v1_funct_1 @ X1)
% 9.20/9.41          | ~ (v1_funct_1 @ sk_C))),
% 9.20/9.41      inference('sup-', [status(thm)], ['130', '131'])).
% 9.20/9.41  thf('133', plain, ((v1_funct_1 @ sk_C)),
% 9.20/9.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.20/9.41  thf('134', plain,
% 9.20/9.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.20/9.41         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1) @ 
% 9.20/9.41           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 9.20/9.41          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 9.20/9.41          | ~ (v1_funct_1 @ X1))),
% 9.20/9.41      inference('demod', [status(thm)], ['132', '133'])).
% 9.20/9.41  thf('135', plain,
% 9.20/9.41      ((~ (v1_funct_1 @ sk_B)
% 9.20/9.41        | (m1_subset_1 @ 
% 9.20/9.41           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) @ 
% 9.20/9.41           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 9.20/9.41      inference('sup-', [status(thm)], ['129', '134'])).
% 9.20/9.41  thf('136', plain, ((v1_funct_1 @ sk_B)),
% 9.20/9.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.20/9.41  thf('137', plain,
% 9.20/9.41      ((m1_subset_1 @ 
% 9.20/9.41        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) @ 
% 9.20/9.41        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.20/9.41      inference('demod', [status(thm)], ['135', '136'])).
% 9.20/9.41  thf('138', plain,
% 9.20/9.41      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)
% 9.20/9.41         = (k5_relat_1 @ sk_C @ sk_B))),
% 9.20/9.41      inference('demod', [status(thm)], ['123', '124'])).
% 9.20/9.41  thf('139', plain,
% 9.20/9.41      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_B) @ 
% 9.20/9.41        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.20/9.41      inference('demod', [status(thm)], ['137', '138'])).
% 9.20/9.41  thf('140', plain,
% 9.20/9.41      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 9.20/9.41         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 9.20/9.41          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 9.20/9.41          | ((X22) = (X25))
% 9.20/9.41          | ~ (r2_relset_1 @ X23 @ X24 @ X22 @ X25))),
% 9.20/9.41      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 9.20/9.41  thf('141', plain,
% 9.20/9.41      (![X0 : $i]:
% 9.20/9.41         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_B) @ X0)
% 9.20/9.41          | ((k5_relat_1 @ sk_C @ sk_B) = (X0))
% 9.20/9.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 9.20/9.41      inference('sup-', [status(thm)], ['139', '140'])).
% 9.20/9.41  thf('142', plain,
% 9.20/9.41      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 9.20/9.41        | ((k5_relat_1 @ sk_C @ sk_B) = (sk_B)))),
% 9.20/9.41      inference('sup-', [status(thm)], ['128', '141'])).
% 9.20/9.41  thf('143', plain,
% 9.20/9.41      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.20/9.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.20/9.41  thf('144', plain, (((k5_relat_1 @ sk_C @ sk_B) = (sk_B))),
% 9.20/9.41      inference('demod', [status(thm)], ['142', '143'])).
% 9.20/9.41  thf('145', plain,
% 9.20/9.41      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) = (sk_B))),
% 9.20/9.41      inference('demod', [status(thm)], ['125', '144'])).
% 9.20/9.41  thf('146', plain,
% 9.20/9.41      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.20/9.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.20/9.41  thf(t27_funct_2, axiom,
% 9.20/9.41    (![A:$i,B:$i,C:$i]:
% 9.20/9.41     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 9.20/9.41         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 9.20/9.41       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 9.20/9.41            ( ~( ( v2_funct_1 @ C ) <=>
% 9.20/9.41                 ( ![D:$i,E:$i]:
% 9.20/9.41                   ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ D @ A ) & 
% 9.20/9.41                       ( m1_subset_1 @
% 9.20/9.41                         E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ A ) ) ) ) =>
% 9.20/9.41                     ( ![F:$i]:
% 9.20/9.41                       ( ( ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ A ) & 
% 9.20/9.41                           ( m1_subset_1 @
% 9.20/9.41                             F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ A ) ) ) ) =>
% 9.20/9.41                         ( ( r2_relset_1 @
% 9.20/9.41                             D @ B @ ( k1_partfun1 @ D @ A @ A @ B @ E @ C ) @ 
% 9.20/9.41                             ( k1_partfun1 @ D @ A @ A @ B @ F @ C ) ) =>
% 9.20/9.41                           ( r2_relset_1 @ D @ A @ E @ F ) ) ) ) ) ) ) ) ) ) ))).
% 9.20/9.41  thf('147', plain,
% 9.20/9.41      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 9.20/9.41         (((X44) = (k1_xboole_0))
% 9.20/9.41          | ((X45) = (k1_xboole_0))
% 9.20/9.41          | ~ (v1_funct_1 @ X46)
% 9.20/9.41          | ~ (v1_funct_2 @ X46 @ X45 @ X44)
% 9.20/9.41          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44)))
% 9.20/9.41          | ~ (v1_funct_1 @ X47)
% 9.20/9.41          | ~ (v1_funct_2 @ X47 @ X48 @ X45)
% 9.20/9.41          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X45)))
% 9.20/9.41          | ~ (r2_relset_1 @ X48 @ X44 @ 
% 9.20/9.41               (k1_partfun1 @ X48 @ X45 @ X45 @ X44 @ X47 @ X46) @ 
% 9.20/9.41               (k1_partfun1 @ X48 @ X45 @ X45 @ X44 @ X49 @ X46))
% 9.20/9.41          | (r2_relset_1 @ X48 @ X45 @ X47 @ X49)
% 9.20/9.41          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X45)))
% 9.20/9.41          | ~ (v1_funct_2 @ X49 @ X48 @ X45)
% 9.20/9.41          | ~ (v1_funct_1 @ X49)
% 9.20/9.41          | ~ (v2_funct_1 @ X46))),
% 9.20/9.41      inference('cnf', [status(esa)], [t27_funct_2])).
% 9.20/9.41  thf('148', plain,
% 9.20/9.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.20/9.41         (~ (v2_funct_1 @ sk_B)
% 9.20/9.41          | ~ (v1_funct_1 @ X0)
% 9.20/9.41          | ~ (v1_funct_2 @ X0 @ X1 @ sk_A)
% 9.20/9.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 9.20/9.41          | (r2_relset_1 @ X1 @ sk_A @ X2 @ X0)
% 9.20/9.41          | ~ (r2_relset_1 @ X1 @ sk_A @ 
% 9.20/9.41               (k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X2 @ sk_B) @ 
% 9.20/9.41               (k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X0 @ sk_B))
% 9.20/9.41          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 9.20/9.41          | ~ (v1_funct_2 @ X2 @ X1 @ sk_A)
% 9.20/9.41          | ~ (v1_funct_1 @ X2)
% 9.20/9.41          | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 9.20/9.41          | ~ (v1_funct_1 @ sk_B)
% 9.20/9.41          | ((sk_A) = (k1_xboole_0))
% 9.20/9.41          | ((sk_A) = (k1_xboole_0)))),
% 9.20/9.41      inference('sup-', [status(thm)], ['146', '147'])).
% 9.20/9.41  thf('149', plain, ((v2_funct_1 @ sk_B)),
% 9.20/9.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.20/9.41  thf('150', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 9.20/9.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.20/9.41  thf('151', plain, ((v1_funct_1 @ sk_B)),
% 9.20/9.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.20/9.41  thf('152', plain,
% 9.20/9.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.20/9.41         (~ (v1_funct_1 @ X0)
% 9.20/9.41          | ~ (v1_funct_2 @ X0 @ X1 @ sk_A)
% 9.20/9.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 9.20/9.41          | (r2_relset_1 @ X1 @ sk_A @ X2 @ X0)
% 9.20/9.41          | ~ (r2_relset_1 @ X1 @ sk_A @ 
% 9.20/9.41               (k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X2 @ sk_B) @ 
% 9.20/9.41               (k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X0 @ sk_B))
% 9.20/9.41          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 9.20/9.41          | ~ (v1_funct_2 @ X2 @ X1 @ sk_A)
% 9.20/9.41          | ~ (v1_funct_1 @ X2)
% 9.20/9.41          | ((sk_A) = (k1_xboole_0))
% 9.20/9.41          | ((sk_A) = (k1_xboole_0)))),
% 9.20/9.41      inference('demod', [status(thm)], ['148', '149', '150', '151'])).
% 9.20/9.41  thf('153', plain,
% 9.20/9.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.20/9.41         (((sk_A) = (k1_xboole_0))
% 9.20/9.41          | ~ (v1_funct_1 @ X2)
% 9.20/9.41          | ~ (v1_funct_2 @ X2 @ X1 @ sk_A)
% 9.20/9.41          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 9.20/9.41          | ~ (r2_relset_1 @ X1 @ sk_A @ 
% 9.20/9.41               (k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X2 @ sk_B) @ 
% 9.20/9.41               (k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X0 @ sk_B))
% 9.20/9.41          | (r2_relset_1 @ X1 @ sk_A @ X2 @ X0)
% 9.20/9.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 9.20/9.41          | ~ (v1_funct_2 @ X0 @ X1 @ sk_A)
% 9.20/9.41          | ~ (v1_funct_1 @ X0))),
% 9.20/9.41      inference('simplify', [status(thm)], ['152'])).
% 9.20/9.41  thf('154', plain,
% 9.20/9.41      (![X0 : $i]:
% 9.20/9.41         (~ (r2_relset_1 @ sk_A @ sk_A @ sk_B @ 
% 9.20/9.41             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_B))
% 9.20/9.41          | ~ (v1_funct_1 @ X0)
% 9.20/9.41          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 9.20/9.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 9.20/9.41          | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ X0)
% 9.20/9.41          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 9.20/9.41          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 9.20/9.41          | ~ (v1_funct_1 @ sk_C)
% 9.20/9.41          | ((sk_A) = (k1_xboole_0)))),
% 9.20/9.41      inference('sup-', [status(thm)], ['145', '153'])).
% 9.20/9.41  thf('155', plain,
% 9.20/9.41      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.20/9.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.20/9.41  thf('156', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 9.20/9.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.20/9.41  thf('157', plain, ((v1_funct_1 @ sk_C)),
% 9.20/9.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.20/9.41  thf('158', plain,
% 9.20/9.41      (![X0 : $i]:
% 9.20/9.41         (~ (r2_relset_1 @ sk_A @ sk_A @ sk_B @ 
% 9.20/9.41             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_B))
% 9.20/9.41          | ~ (v1_funct_1 @ X0)
% 9.20/9.41          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 9.20/9.41          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 9.20/9.41          | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ X0)
% 9.20/9.41          | ((sk_A) = (k1_xboole_0)))),
% 9.20/9.41      inference('demod', [status(thm)], ['154', '155', '156', '157'])).
% 9.20/9.41  thf('159', plain,
% 9.20/9.41      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B)
% 9.20/9.41        | ((sk_A) = (k1_xboole_0))
% 9.20/9.41        | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_relat_1 @ sk_A))
% 9.20/9.41        | ~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 9.20/9.41             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 9.20/9.41        | ~ (v1_funct_2 @ (k6_relat_1 @ sk_A) @ sk_A @ sk_A)
% 9.20/9.41        | ~ (v1_funct_1 @ (k6_relat_1 @ sk_A)))),
% 9.20/9.41      inference('sup-', [status(thm)], ['116', '158'])).
% 9.20/9.41  thf('160', plain,
% 9.20/9.41      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.20/9.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.20/9.41  thf('161', plain,
% 9.20/9.41      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 9.20/9.41         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 9.20/9.41          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 9.20/9.41          | (r2_relset_1 @ X23 @ X24 @ X22 @ X25)
% 9.20/9.41          | ((X22) != (X25)))),
% 9.20/9.41      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 9.20/9.41  thf('162', plain,
% 9.20/9.41      (![X23 : $i, X24 : $i, X25 : $i]:
% 9.20/9.41         ((r2_relset_1 @ X23 @ X24 @ X25 @ X25)
% 9.20/9.41          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 9.20/9.41      inference('simplify', [status(thm)], ['161'])).
% 9.20/9.41  thf('163', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B)),
% 9.20/9.41      inference('sup-', [status(thm)], ['160', '162'])).
% 9.20/9.41  thf('164', plain,
% 9.20/9.41      (![X33 : $i]:
% 9.20/9.41         (m1_subset_1 @ (k6_relat_1 @ X33) @ 
% 9.20/9.41          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))),
% 9.20/9.41      inference('demod', [status(thm)], ['80', '81'])).
% 9.20/9.41  thf('165', plain, ((v1_funct_1 @ (k6_relat_1 @ sk_A))),
% 9.20/9.41      inference('demod', [status(thm)], ['64', '65', '66', '67', '68', '77'])).
% 9.20/9.41  thf(t71_relat_1, axiom,
% 9.20/9.41    (![A:$i]:
% 9.20/9.41     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 9.20/9.41       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 9.20/9.41  thf('166', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X5)) = (X5))),
% 9.20/9.41      inference('cnf', [status(esa)], [t71_relat_1])).
% 9.20/9.41  thf('167', plain,
% 9.20/9.41      (![X53 : $i]:
% 9.20/9.41         ((v1_funct_2 @ X53 @ (k1_relat_1 @ X53) @ (k2_relat_1 @ X53))
% 9.20/9.41          | ~ (v1_funct_1 @ X53)
% 9.20/9.41          | ~ (v1_relat_1 @ X53))),
% 9.20/9.41      inference('cnf', [status(esa)], [t3_funct_2])).
% 9.20/9.41  thf('168', plain,
% 9.20/9.41      (![X0 : $i]:
% 9.20/9.41         ((v1_funct_2 @ (k6_relat_1 @ X0) @ X0 @ 
% 9.20/9.41           (k2_relat_1 @ (k6_relat_1 @ X0)))
% 9.20/9.41          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 9.20/9.41          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 9.20/9.41      inference('sup+', [status(thm)], ['166', '167'])).
% 9.20/9.41  thf('169', plain, (![X6 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X6)) = (X6))),
% 9.20/9.41      inference('cnf', [status(esa)], [t71_relat_1])).
% 9.20/9.41  thf(fc4_funct_1, axiom,
% 9.20/9.41    (![A:$i]:
% 9.20/9.41     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 9.20/9.41       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 9.20/9.41  thf('170', plain, (![X7 : $i]: (v1_relat_1 @ (k6_relat_1 @ X7))),
% 9.20/9.41      inference('cnf', [status(esa)], [fc4_funct_1])).
% 9.20/9.41  thf('171', plain,
% 9.20/9.41      (![X0 : $i]:
% 9.20/9.41         ((v1_funct_2 @ (k6_relat_1 @ X0) @ X0 @ X0)
% 9.20/9.41          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 9.20/9.41      inference('demod', [status(thm)], ['168', '169', '170'])).
% 9.20/9.41  thf('172', plain, ((v1_funct_2 @ (k6_relat_1 @ sk_A) @ sk_A @ sk_A)),
% 9.20/9.41      inference('sup-', [status(thm)], ['165', '171'])).
% 9.20/9.41  thf('173', plain, ((v1_funct_1 @ (k6_relat_1 @ sk_A))),
% 9.20/9.41      inference('demod', [status(thm)], ['64', '65', '66', '67', '68', '77'])).
% 9.20/9.41  thf('174', plain,
% 9.20/9.41      ((((sk_A) = (k1_xboole_0))
% 9.20/9.41        | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_relat_1 @ sk_A)))),
% 9.20/9.41      inference('demod', [status(thm)], ['159', '163', '164', '172', '173'])).
% 9.20/9.41  thf('175', plain,
% 9.20/9.41      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_relat_1 @ sk_A))),
% 9.20/9.41      inference('demod', [status(thm)], ['0', '1'])).
% 9.20/9.41  thf('176', plain, (((sk_A) = (k1_xboole_0))),
% 9.20/9.41      inference('clc', [status(thm)], ['174', '175'])).
% 9.20/9.41  thf('177', plain, (((sk_A) = (k1_xboole_0))),
% 9.20/9.41      inference('clc', [status(thm)], ['174', '175'])).
% 9.20/9.41  thf('178', plain, (((sk_A) = (k1_xboole_0))),
% 9.20/9.41      inference('clc', [status(thm)], ['174', '175'])).
% 9.20/9.41  thf('179', plain, (![X5 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X5)) = (X5))),
% 9.20/9.41      inference('cnf', [status(esa)], [t71_relat_1])).
% 9.20/9.41  thf(t64_relat_1, axiom,
% 9.20/9.41    (![A:$i]:
% 9.20/9.41     ( ( v1_relat_1 @ A ) =>
% 9.20/9.41       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 9.20/9.41           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 9.20/9.41         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 9.20/9.41  thf('180', plain,
% 9.20/9.41      (![X4 : $i]:
% 9.20/9.41         (((k1_relat_1 @ X4) != (k1_xboole_0))
% 9.20/9.41          | ((X4) = (k1_xboole_0))
% 9.20/9.41          | ~ (v1_relat_1 @ X4))),
% 9.20/9.41      inference('cnf', [status(esa)], [t64_relat_1])).
% 9.20/9.41  thf('181', plain,
% 9.20/9.41      (![X0 : $i]:
% 9.20/9.41         (((X0) != (k1_xboole_0))
% 9.20/9.41          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 9.20/9.41          | ((k6_relat_1 @ X0) = (k1_xboole_0)))),
% 9.20/9.41      inference('sup-', [status(thm)], ['179', '180'])).
% 9.20/9.41  thf('182', plain, (![X7 : $i]: (v1_relat_1 @ (k6_relat_1 @ X7))),
% 9.20/9.41      inference('cnf', [status(esa)], [fc4_funct_1])).
% 9.20/9.41  thf('183', plain,
% 9.20/9.41      (![X0 : $i]:
% 9.20/9.41         (((X0) != (k1_xboole_0)) | ((k6_relat_1 @ X0) = (k1_xboole_0)))),
% 9.20/9.41      inference('demod', [status(thm)], ['181', '182'])).
% 9.20/9.41  thf('184', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 9.20/9.41      inference('simplify', [status(thm)], ['183'])).
% 9.20/9.41  thf('185', plain,
% 9.20/9.41      (~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ k1_xboole_0)),
% 9.20/9.41      inference('demod', [status(thm)], ['2', '176', '177', '178', '184'])).
% 9.20/9.41  thf('186', plain,
% 9.20/9.41      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.20/9.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.20/9.41  thf('187', plain,
% 9.20/9.41      (![X54 : $i, X55 : $i]:
% 9.20/9.41         (((k1_relset_1 @ X54 @ X54 @ X55) = (X54))
% 9.20/9.41          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X54)))
% 9.20/9.41          | ~ (v1_funct_2 @ X55 @ X54 @ X54)
% 9.20/9.41          | ~ (v1_funct_1 @ X55))),
% 9.20/9.41      inference('cnf', [status(esa)], [t67_funct_2])).
% 9.20/9.41  thf('188', plain,
% 9.20/9.41      ((~ (v1_funct_1 @ sk_C)
% 9.20/9.41        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 9.20/9.41        | ((k1_relset_1 @ sk_A @ sk_A @ sk_C) = (sk_A)))),
% 9.20/9.41      inference('sup-', [status(thm)], ['186', '187'])).
% 9.20/9.41  thf('189', plain, ((v1_funct_1 @ sk_C)),
% 9.20/9.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.20/9.41  thf('190', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 9.20/9.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.20/9.41  thf('191', plain,
% 9.20/9.41      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.20/9.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.20/9.41  thf('192', plain,
% 9.20/9.41      (![X10 : $i, X11 : $i, X12 : $i]:
% 9.20/9.41         (((k1_relset_1 @ X11 @ X12 @ X10) = (k1_relat_1 @ X10))
% 9.20/9.41          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 9.20/9.41      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 9.20/9.41  thf('193', plain,
% 9.20/9.41      (((k1_relset_1 @ sk_A @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 9.20/9.41      inference('sup-', [status(thm)], ['191', '192'])).
% 9.20/9.41  thf('194', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 9.20/9.41      inference('demod', [status(thm)], ['188', '189', '190', '193'])).
% 9.20/9.41  thf('195', plain,
% 9.20/9.41      (![X4 : $i]:
% 9.20/9.41         (((k1_relat_1 @ X4) != (k1_xboole_0))
% 9.20/9.41          | ((X4) = (k1_xboole_0))
% 9.20/9.41          | ~ (v1_relat_1 @ X4))),
% 9.20/9.41      inference('cnf', [status(esa)], [t64_relat_1])).
% 9.20/9.41  thf('196', plain,
% 9.20/9.41      ((((sk_A) != (k1_xboole_0))
% 9.20/9.41        | ~ (v1_relat_1 @ sk_C)
% 9.20/9.41        | ((sk_C) = (k1_xboole_0)))),
% 9.20/9.41      inference('sup-', [status(thm)], ['194', '195'])).
% 9.20/9.41  thf('197', plain,
% 9.20/9.41      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.20/9.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.20/9.41  thf('198', plain,
% 9.20/9.41      (![X0 : $i, X1 : $i]:
% 9.20/9.41         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 9.20/9.41          | (v1_relat_1 @ X0)
% 9.20/9.41          | ~ (v1_relat_1 @ X1))),
% 9.20/9.41      inference('cnf', [status(esa)], [cc2_relat_1])).
% 9.20/9.41  thf('199', plain,
% 9.20/9.41      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_C))),
% 9.20/9.41      inference('sup-', [status(thm)], ['197', '198'])).
% 9.20/9.41  thf('200', plain,
% 9.20/9.41      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 9.20/9.41      inference('cnf', [status(esa)], [fc6_relat_1])).
% 9.20/9.41  thf('201', plain, ((v1_relat_1 @ sk_C)),
% 9.20/9.41      inference('demod', [status(thm)], ['199', '200'])).
% 9.20/9.41  thf('202', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 9.20/9.41      inference('demod', [status(thm)], ['196', '201'])).
% 9.20/9.41  thf('203', plain, (((sk_A) = (k1_xboole_0))),
% 9.20/9.41      inference('clc', [status(thm)], ['174', '175'])).
% 9.20/9.41  thf('204', plain,
% 9.20/9.41      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 9.20/9.41      inference('demod', [status(thm)], ['202', '203'])).
% 9.20/9.41  thf('205', plain, (((sk_C) = (k1_xboole_0))),
% 9.20/9.41      inference('simplify', [status(thm)], ['204'])).
% 9.20/9.41  thf('206', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 9.20/9.41      inference('simplify', [status(thm)], ['183'])).
% 9.20/9.41  thf('207', plain,
% 9.20/9.41      (![X33 : $i]:
% 9.20/9.41         (m1_subset_1 @ (k6_relat_1 @ X33) @ 
% 9.20/9.41          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))),
% 9.20/9.41      inference('demod', [status(thm)], ['80', '81'])).
% 9.20/9.41  thf('208', plain,
% 9.20/9.41      ((m1_subset_1 @ k1_xboole_0 @ 
% 9.20/9.41        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 9.20/9.41      inference('sup+', [status(thm)], ['206', '207'])).
% 9.20/9.41  thf('209', plain,
% 9.20/9.41      (![X23 : $i, X24 : $i, X25 : $i]:
% 9.20/9.41         ((r2_relset_1 @ X23 @ X24 @ X25 @ X25)
% 9.20/9.41          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 9.20/9.41      inference('simplify', [status(thm)], ['161'])).
% 9.20/9.41  thf('210', plain,
% 9.20/9.41      ((r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 9.20/9.41      inference('sup-', [status(thm)], ['208', '209'])).
% 9.20/9.41  thf('211', plain, ($false),
% 9.20/9.41      inference('demod', [status(thm)], ['185', '205', '210'])).
% 9.20/9.41  
% 9.20/9.41  % SZS output end Refutation
% 9.20/9.41  
% 9.20/9.42  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
