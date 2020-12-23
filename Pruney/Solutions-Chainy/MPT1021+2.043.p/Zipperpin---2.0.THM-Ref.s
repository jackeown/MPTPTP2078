%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.243UDR3dwP

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 475 expanded)
%              Number of leaves         :   40 ( 159 expanded)
%              Depth                    :   19
%              Number of atoms          : 1453 (10144 expanded)
%              Number of equality atoms :   50 (  97 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(t88_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ ( k6_partfun1 @ A ) )
        & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ ( k6_partfun1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( v3_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ ( k6_partfun1 @ A ) )
          & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ ( k6_partfun1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t88_funct_2])).

thf('1',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('3',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('4',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
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

thf('6',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k2_funct_2 @ X31 @ X30 )
        = ( k2_funct_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) )
      | ~ ( v3_funct_2 @ X30 @ X31 @ X31 )
      | ~ ( v1_funct_2 @ X30 @ X31 @ X31 )
      | ~ ( v1_funct_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('7',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_B )
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('12',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('15',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v2_funct_1 @ X33 )
      | ( ( k2_relset_1 @ X35 @ X34 @ X33 )
       != X34 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X35 @ X34 )
      | ~ ( v1_funct_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('16',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('20',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('21',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
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

thf('23',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_funct_1 @ X17 )
      | ~ ( v3_funct_2 @ X17 @ X18 @ X19 )
      | ( v2_funct_2 @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('24',plain,
    ( ( v2_funct_2 @ sk_B @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v2_funct_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['24','25','26'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('28',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v2_funct_2 @ X21 @ X20 )
      | ( ( k2_relat_1 @ X21 )
        = X20 )
      | ~ ( v5_relat_1 @ X21 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v5_relat_1 @ sk_B @ sk_A )
    | ( ( k2_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('31',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( v1_relat_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('32',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('34',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v5_relat_1 @ X4 @ X6 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('35',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['29','32','35'])).

thf('37',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['21','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_funct_1 @ X17 )
      | ~ ( v3_funct_2 @ X17 @ X18 @ X19 )
      | ( v2_funct_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('40',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( sk_A != sk_A ) ),
    inference(demod,[status(thm)],['16','17','18','37','43'])).

thf('45',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('47',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( ( k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27 )
        = ( k5_relat_1 @ X24 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['45','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v2_funct_1 @ X33 )
      | ( ( k2_relset_1 @ X35 @ X34 @ X33 )
       != X34 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X35 @ X34 )
      | ~ ( v1_funct_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('54',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['21','36'])).

thf('58',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('59',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( sk_A != sk_A ) ),
    inference(demod,[status(thm)],['54','55','56','57','58'])).

thf('60',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['51','60'])).

thf('62',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('63',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('64',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('65',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf('68',plain,
    ( ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('70',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k1_relset_1 @ X36 @ X36 @ X37 )
        = X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) )
      | ~ ( v1_funct_2 @ X37 @ X36 @ X36 )
      | ~ ( v1_funct_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('71',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('75',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X9 @ X7 )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('76',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['71','72','73','76'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('78',plain,(
    ! [X23: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('79',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('80',plain,(
    ! [X23: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('81',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( r2_relset_1 @ X14 @ X15 @ X13 @ X16 )
      | ( X13 != X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('82',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r2_relset_1 @ X14 @ X15 @ X16 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','82'])).

thf('84',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['30','31'])).

thf('85',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('87',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['68','77','83','84','85','86'])).

thf('88',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('89',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['87','88'])).

thf('90',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['12','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('93',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( ( k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27 )
        = ( k5_relat_1 @ X24 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['59'])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['91','96'])).

thf('98',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','99'])).

thf('101',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','100'])).

thf('102',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['29','32','35'])).

thf('103',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','82'])).

thf('104',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['30','31'])).

thf('105',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('107',plain,(
    $false ),
    inference(demod,[status(thm)],['101','102','103','104','105','106'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.243UDR3dwP
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:48:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 107 iterations in 0.052s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.21/0.52  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.21/0.52  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.21/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.52  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.21/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.52  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.21/0.52  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.52  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.21/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.52  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.52  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.52  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.52  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.21/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.52  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.21/0.52  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.21/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.52  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.52  thf(t61_funct_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.52       ( ( v2_funct_1 @ A ) =>
% 0.21/0.52         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.21/0.52             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.21/0.52           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.21/0.52             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (v2_funct_1 @ X0)
% 0.21/0.52          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.21/0.52              = (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.21/0.52          | ~ (v1_funct_1 @ X0)
% 0.21/0.52          | ~ (v1_relat_1 @ X0))),
% 0.21/0.52      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.21/0.52  thf(t88_funct_2, conjecture,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.21/0.52         ( v3_funct_2 @ B @ A @ A ) & 
% 0.21/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.52       ( ( r2_relset_1 @
% 0.21/0.52           A @ A @ 
% 0.21/0.52           ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 0.21/0.52           ( k6_partfun1 @ A ) ) & 
% 0.21/0.52         ( r2_relset_1 @
% 0.21/0.52           A @ A @ 
% 0.21/0.52           ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 0.21/0.52           ( k6_partfun1 @ A ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i,B:$i]:
% 0.21/0.52        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.21/0.52            ( v3_funct_2 @ B @ A @ A ) & 
% 0.21/0.52            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.52          ( ( r2_relset_1 @
% 0.21/0.52              A @ A @ 
% 0.21/0.52              ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 0.21/0.52              ( k6_partfun1 @ A ) ) & 
% 0.21/0.52            ( r2_relset_1 @
% 0.21/0.52              A @ A @ 
% 0.21/0.52              ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 0.21/0.52              ( k6_partfun1 @ A ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t88_funct_2])).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.21/0.52           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.21/0.52            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.21/0.52           (k6_partfun1 @ sk_A))
% 0.21/0.52        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.21/0.52             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.21/0.52              (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.21/0.52             (k6_partfun1 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.21/0.52           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.21/0.52            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.21/0.52           (k6_partfun1 @ sk_A)))
% 0.21/0.52         <= (~
% 0.21/0.52             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.21/0.52               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.21/0.52                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.21/0.52               (k6_partfun1 @ sk_A))))),
% 0.21/0.52      inference('split', [status(esa)], ['1'])).
% 0.21/0.52  thf(redefinition_k6_partfun1, axiom,
% 0.21/0.52    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.21/0.52  thf('3', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.21/0.52           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.21/0.52            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.21/0.52           (k6_relat_1 @ sk_A)))
% 0.21/0.52         <= (~
% 0.21/0.52             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.21/0.52               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.21/0.52                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.21/0.52               (k6_partfun1 @ sk_A))))),
% 0.21/0.52      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(redefinition_k2_funct_2, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.21/0.52         ( v3_funct_2 @ B @ A @ A ) & 
% 0.21/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.52       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      (![X30 : $i, X31 : $i]:
% 0.21/0.52         (((k2_funct_2 @ X31 @ X30) = (k2_funct_1 @ X30))
% 0.21/0.52          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))
% 0.21/0.52          | ~ (v3_funct_2 @ X30 @ X31 @ X31)
% 0.21/0.52          | ~ (v1_funct_2 @ X30 @ X31 @ X31)
% 0.21/0.52          | ~ (v1_funct_1 @ X30))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      ((~ (v1_funct_1 @ sk_B)
% 0.21/0.52        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.21/0.52        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.21/0.52        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.52  thf('8', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('9', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('10', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('11', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.21/0.52      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.21/0.52           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 0.21/0.52            sk_B) @ 
% 0.21/0.52           (k6_relat_1 @ sk_A)))
% 0.21/0.52         <= (~
% 0.21/0.52             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.21/0.52               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.21/0.52                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.21/0.52               (k6_partfun1 @ sk_A))))),
% 0.21/0.52      inference('demod', [status(thm)], ['4', '11'])).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (v2_funct_1 @ X0)
% 0.21/0.52          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.21/0.52              = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.21/0.52          | ~ (v1_funct_1 @ X0)
% 0.21/0.52          | ~ (v1_relat_1 @ X0))),
% 0.21/0.52      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.21/0.52  thf('14', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t31_funct_2, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.52       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.21/0.52         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.21/0.52           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.21/0.52           ( m1_subset_1 @
% 0.21/0.52             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.21/0.52         (~ (v2_funct_1 @ X33)
% 0.21/0.52          | ((k2_relset_1 @ X35 @ X34 @ X33) != (X34))
% 0.21/0.52          | (m1_subset_1 @ (k2_funct_1 @ X33) @ 
% 0.21/0.52             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.21/0.52          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 0.21/0.52          | ~ (v1_funct_2 @ X33 @ X35 @ X34)
% 0.21/0.52          | ~ (v1_funct_1 @ X33))),
% 0.21/0.52      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      ((~ (v1_funct_1 @ sk_B)
% 0.21/0.52        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.21/0.52        | (m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.21/0.52           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.21/0.52        | ((k2_relset_1 @ sk_A @ sk_A @ sk_B) != (sk_A))
% 0.21/0.52        | ~ (v2_funct_1 @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.52  thf('17', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('18', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.52       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.52         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 0.21/0.52          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (k2_relat_1 @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(cc2_funct_2, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.52       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.21/0.52         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.52         (~ (v1_funct_1 @ X17)
% 0.21/0.52          | ~ (v3_funct_2 @ X17 @ X18 @ X19)
% 0.21/0.52          | (v2_funct_2 @ X17 @ X19)
% 0.21/0.52          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.21/0.52      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.21/0.52  thf('24', plain,
% 0.21/0.52      (((v2_funct_2 @ sk_B @ sk_A)
% 0.21/0.52        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.21/0.52        | ~ (v1_funct_1 @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.52  thf('25', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('26', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('27', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 0.21/0.52      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.21/0.52  thf(d3_funct_2, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.21/0.52       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.21/0.52  thf('28', plain,
% 0.21/0.52      (![X20 : $i, X21 : $i]:
% 0.21/0.52         (~ (v2_funct_2 @ X21 @ X20)
% 0.21/0.52          | ((k2_relat_1 @ X21) = (X20))
% 0.21/0.52          | ~ (v5_relat_1 @ X21 @ X20)
% 0.21/0.52          | ~ (v1_relat_1 @ X21))),
% 0.21/0.52      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.21/0.52  thf('29', plain,
% 0.21/0.52      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.52        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 0.21/0.52        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.52  thf('30', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(cc1_relset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.52       ( v1_relat_1 @ C ) ))).
% 0.21/0.52  thf('31', plain,
% 0.21/0.52      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.52         ((v1_relat_1 @ X1)
% 0.21/0.52          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3))))),
% 0.21/0.52      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.52  thf('32', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.52      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.52  thf('33', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(cc2_relset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.52       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.52  thf('34', plain,
% 0.21/0.52      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.52         ((v5_relat_1 @ X4 @ X6)
% 0.21/0.52          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.21/0.52      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.52  thf('35', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 0.21/0.52      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.52  thf('36', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['29', '32', '35'])).
% 0.21/0.52  thf('37', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['21', '36'])).
% 0.21/0.52  thf('38', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('39', plain,
% 0.21/0.52      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.52         (~ (v1_funct_1 @ X17)
% 0.21/0.52          | ~ (v3_funct_2 @ X17 @ X18 @ X19)
% 0.21/0.52          | (v2_funct_1 @ X17)
% 0.21/0.52          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.21/0.52      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.21/0.52  thf('40', plain,
% 0.21/0.52      (((v2_funct_1 @ sk_B)
% 0.21/0.52        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.21/0.52        | ~ (v1_funct_1 @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.52  thf('41', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('42', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('43', plain, ((v2_funct_1 @ sk_B)),
% 0.21/0.52      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.21/0.52  thf('44', plain,
% 0.21/0.52      (((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.21/0.52         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.21/0.52        | ((sk_A) != (sk_A)))),
% 0.21/0.52      inference('demod', [status(thm)], ['16', '17', '18', '37', '43'])).
% 0.21/0.52  thf('45', plain,
% 0.21/0.52      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.21/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['44'])).
% 0.21/0.52  thf('46', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(redefinition_k1_partfun1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.21/0.52     ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.52         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.52         ( v1_funct_1 @ F ) & 
% 0.21/0.52         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.21/0.52       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.21/0.52  thf('47', plain,
% 0.21/0.52      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.21/0.52          | ~ (v1_funct_1 @ X24)
% 0.21/0.52          | ~ (v1_funct_1 @ X27)
% 0.21/0.52          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.21/0.52          | ((k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27)
% 0.21/0.52              = (k5_relat_1 @ X24 @ X27)))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.21/0.52  thf('48', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 0.21/0.52            = (k5_relat_1 @ sk_B @ X0))
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.21/0.52          | ~ (v1_funct_1 @ X0)
% 0.21/0.52          | ~ (v1_funct_1 @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['46', '47'])).
% 0.21/0.52  thf('49', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('50', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 0.21/0.52            = (k5_relat_1 @ sk_B @ X0))
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.21/0.52          | ~ (v1_funct_1 @ X0))),
% 0.21/0.52      inference('demod', [status(thm)], ['48', '49'])).
% 0.21/0.52  thf('51', plain,
% 0.21/0.52      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.21/0.52        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.21/0.52            (k2_funct_1 @ sk_B)) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['45', '50'])).
% 0.21/0.52  thf('52', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('53', plain,
% 0.21/0.52      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.21/0.52         (~ (v2_funct_1 @ X33)
% 0.21/0.52          | ((k2_relset_1 @ X35 @ X34 @ X33) != (X34))
% 0.21/0.52          | (v1_funct_1 @ (k2_funct_1 @ X33))
% 0.21/0.52          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 0.21/0.52          | ~ (v1_funct_2 @ X33 @ X35 @ X34)
% 0.21/0.52          | ~ (v1_funct_1 @ X33))),
% 0.21/0.52      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.21/0.52  thf('54', plain,
% 0.21/0.52      ((~ (v1_funct_1 @ sk_B)
% 0.21/0.52        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.21/0.52        | (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.21/0.52        | ((k2_relset_1 @ sk_A @ sk_A @ sk_B) != (sk_A))
% 0.21/0.52        | ~ (v2_funct_1 @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.52  thf('55', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('56', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('57', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['21', '36'])).
% 0.21/0.52  thf('58', plain, ((v2_funct_1 @ sk_B)),
% 0.21/0.52      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.21/0.52  thf('59', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_B)) | ((sk_A) != (sk_A)))),
% 0.21/0.52      inference('demod', [status(thm)], ['54', '55', '56', '57', '58'])).
% 0.21/0.52  thf('60', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.21/0.52      inference('simplify', [status(thm)], ['59'])).
% 0.21/0.52  thf('61', plain,
% 0.21/0.52      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B))
% 0.21/0.52         = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))),
% 0.21/0.52      inference('demod', [status(thm)], ['51', '60'])).
% 0.21/0.52  thf('62', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.21/0.52      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 0.21/0.52  thf('63', plain,
% 0.21/0.52      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.21/0.52           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.21/0.52            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.21/0.52           (k6_partfun1 @ sk_A)))
% 0.21/0.52         <= (~
% 0.21/0.52             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.21/0.52               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.21/0.52                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.21/0.52               (k6_partfun1 @ sk_A))))),
% 0.21/0.52      inference('split', [status(esa)], ['1'])).
% 0.21/0.52  thf('64', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.52  thf('65', plain,
% 0.21/0.52      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.21/0.52           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.21/0.52            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.21/0.52           (k6_relat_1 @ sk_A)))
% 0.21/0.52         <= (~
% 0.21/0.52             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.21/0.52               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.21/0.52                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.21/0.52               (k6_partfun1 @ sk_A))))),
% 0.21/0.52      inference('demod', [status(thm)], ['63', '64'])).
% 0.21/0.52  thf('66', plain,
% 0.21/0.52      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.21/0.52           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.21/0.52            (k2_funct_1 @ sk_B)) @ 
% 0.21/0.52           (k6_relat_1 @ sk_A)))
% 0.21/0.52         <= (~
% 0.21/0.52             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.21/0.52               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.21/0.52                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.21/0.52               (k6_partfun1 @ sk_A))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['62', '65'])).
% 0.21/0.52  thf('67', plain,
% 0.21/0.52      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.21/0.52           (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ (k6_relat_1 @ sk_A)))
% 0.21/0.52         <= (~
% 0.21/0.52             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.21/0.52               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.21/0.52                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.21/0.52               (k6_partfun1 @ sk_A))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['61', '66'])).
% 0.21/0.52  thf('68', plain,
% 0.21/0.52      (((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ 
% 0.21/0.52            (k6_relat_1 @ sk_A))
% 0.21/0.52         | ~ (v1_relat_1 @ sk_B)
% 0.21/0.52         | ~ (v1_funct_1 @ sk_B)
% 0.21/0.52         | ~ (v2_funct_1 @ sk_B)))
% 0.21/0.52         <= (~
% 0.21/0.52             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.21/0.52               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.21/0.52                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.21/0.52               (k6_partfun1 @ sk_A))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['13', '67'])).
% 0.21/0.52  thf('69', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t67_funct_2, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.21/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.52       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 0.21/0.52  thf('70', plain,
% 0.21/0.52      (![X36 : $i, X37 : $i]:
% 0.21/0.52         (((k1_relset_1 @ X36 @ X36 @ X37) = (X36))
% 0.21/0.52          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))
% 0.21/0.52          | ~ (v1_funct_2 @ X37 @ X36 @ X36)
% 0.21/0.52          | ~ (v1_funct_1 @ X37))),
% 0.21/0.52      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.21/0.52  thf('71', plain,
% 0.21/0.52      ((~ (v1_funct_1 @ sk_B)
% 0.21/0.52        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.21/0.52        | ((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['69', '70'])).
% 0.21/0.52  thf('72', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('73', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('74', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.52       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.52  thf('75', plain,
% 0.21/0.52      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.52         (((k1_relset_1 @ X8 @ X9 @ X7) = (k1_relat_1 @ X7))
% 0.21/0.52          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.52  thf('76', plain,
% 0.21/0.52      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['74', '75'])).
% 0.21/0.52  thf('77', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['71', '72', '73', '76'])).
% 0.21/0.52  thf(dt_k6_partfun1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( m1_subset_1 @
% 0.21/0.52         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.21/0.52       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.21/0.52  thf('78', plain,
% 0.21/0.52      (![X23 : $i]:
% 0.21/0.52         (m1_subset_1 @ (k6_partfun1 @ X23) @ 
% 0.21/0.52          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X23)))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.21/0.52  thf('79', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.52  thf('80', plain,
% 0.21/0.52      (![X23 : $i]:
% 0.21/0.52         (m1_subset_1 @ (k6_relat_1 @ X23) @ 
% 0.21/0.52          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X23)))),
% 0.21/0.52      inference('demod', [status(thm)], ['78', '79'])).
% 0.21/0.52  thf(redefinition_r2_relset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.52     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.52         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.52       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.21/0.52  thf('81', plain,
% 0.21/0.52      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.21/0.52          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.21/0.52          | (r2_relset_1 @ X14 @ X15 @ X13 @ X16)
% 0.21/0.52          | ((X13) != (X16)))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.21/0.52  thf('82', plain,
% 0.21/0.52      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.52         ((r2_relset_1 @ X14 @ X15 @ X16 @ X16)
% 0.21/0.52          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.21/0.52      inference('simplify', [status(thm)], ['81'])).
% 0.21/0.52  thf('83', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['80', '82'])).
% 0.21/0.52  thf('84', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.52      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.52  thf('85', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('86', plain, ((v2_funct_1 @ sk_B)),
% 0.21/0.52      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.21/0.52  thf('87', plain,
% 0.21/0.52      (((r2_relset_1 @ sk_A @ sk_A @ 
% 0.21/0.52         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.21/0.52          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.21/0.52         (k6_partfun1 @ sk_A)))),
% 0.21/0.52      inference('demod', [status(thm)], ['68', '77', '83', '84', '85', '86'])).
% 0.21/0.52  thf('88', plain,
% 0.21/0.52      (~
% 0.21/0.52       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.21/0.52         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.21/0.52          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.21/0.52         (k6_partfun1 @ sk_A))) | 
% 0.21/0.52       ~
% 0.21/0.52       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.21/0.52         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.21/0.52          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.21/0.52         (k6_partfun1 @ sk_A)))),
% 0.21/0.52      inference('split', [status(esa)], ['1'])).
% 0.21/0.52  thf('89', plain,
% 0.21/0.52      (~
% 0.21/0.52       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.21/0.52         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.21/0.52          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.21/0.52         (k6_partfun1 @ sk_A)))),
% 0.21/0.52      inference('sat_resolution*', [status(thm)], ['87', '88'])).
% 0.21/0.52  thf('90', plain,
% 0.21/0.52      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.21/0.52          (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.21/0.52          (k6_relat_1 @ sk_A))),
% 0.21/0.52      inference('simpl_trail', [status(thm)], ['12', '89'])).
% 0.21/0.52  thf('91', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('92', plain,
% 0.21/0.52      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.21/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['44'])).
% 0.21/0.52  thf('93', plain,
% 0.21/0.52      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.21/0.52          | ~ (v1_funct_1 @ X24)
% 0.21/0.52          | ~ (v1_funct_1 @ X27)
% 0.21/0.52          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.21/0.52          | ((k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27)
% 0.21/0.52              = (k5_relat_1 @ X24 @ X27)))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.21/0.52  thf('94', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 0.21/0.52            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.21/0.52          | ~ (v1_funct_1 @ X0)
% 0.21/0.52          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['92', '93'])).
% 0.21/0.52  thf('95', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.21/0.52      inference('simplify', [status(thm)], ['59'])).
% 0.21/0.52  thf('96', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 0.21/0.52            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.21/0.52          | ~ (v1_funct_1 @ X0))),
% 0.21/0.52      inference('demod', [status(thm)], ['94', '95'])).
% 0.21/0.52  thf('97', plain,
% 0.21/0.52      ((~ (v1_funct_1 @ sk_B)
% 0.21/0.52        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 0.21/0.52            sk_B) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['91', '96'])).
% 0.21/0.52  thf('98', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('99', plain,
% 0.21/0.52      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B)
% 0.21/0.52         = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))),
% 0.21/0.52      inference('demod', [status(thm)], ['97', '98'])).
% 0.21/0.52  thf('100', plain,
% 0.21/0.52      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.21/0.52          (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ (k6_relat_1 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['90', '99'])).
% 0.21/0.52  thf('101', plain,
% 0.21/0.52      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 0.21/0.52           (k6_relat_1 @ sk_A))
% 0.21/0.52        | ~ (v1_relat_1 @ sk_B)
% 0.21/0.52        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.52        | ~ (v2_funct_1 @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['0', '100'])).
% 0.21/0.52  thf('102', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['29', '32', '35'])).
% 0.21/0.52  thf('103', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['80', '82'])).
% 0.21/0.52  thf('104', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.52      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.52  thf('105', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('106', plain, ((v2_funct_1 @ sk_B)),
% 0.21/0.52      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.21/0.52  thf('107', plain, ($false),
% 0.21/0.52      inference('demod', [status(thm)],
% 0.21/0.52                ['101', '102', '103', '104', '105', '106'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
