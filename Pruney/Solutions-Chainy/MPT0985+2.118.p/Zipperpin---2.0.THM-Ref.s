%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zyoaTZQuDh

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:43 EST 2020

% Result     : Theorem 6.07s
% Output     : Refutation 6.07s
% Verified   : 
% Statistics : Number of formulae       :  249 (1560 expanded)
%              Number of leaves         :   36 ( 470 expanded)
%              Depth                    :   50
%              Number of atoms          : 2297 (26198 expanded)
%              Number of equality atoms :   85 ( 838 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X6: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v2_funct_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf(t31_funct_2,conjecture,(
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

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( v2_funct_1 @ C )
            & ( ( k2_relset_1 @ A @ B @ C )
              = B ) )
         => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
            & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
            & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_funct_2])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X11 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('3',plain,(
    m1_subset_1 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('5',plain,(
    r1_tarski @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X16 @ X14 )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('8',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['5','8'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('10',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k1_relat_1 @ X7 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('11',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X29 ) @ X30 )
      | ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X29 ) @ X30 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('15',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('16',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k1_relat_1 @ X7 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('20',plain,(
    ! [X6: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v2_funct_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('21',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v2_funct_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('22',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_relat_1 @ X7 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('23',plain,(
    ! [X28: $i] :
      ( ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X28 ) @ ( k2_relat_1 @ X28 ) ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['18','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('33',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('34',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['31','34','35','36'])).

thf('38',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('39',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['32','33'])).

thf('43',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['13','39','40','41','42'])).

thf('44',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_relat_1 @ X7 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('45',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['16','17'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('47',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X16 @ X14 )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relset_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) @ ( k2_funct_1 @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('50',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X11 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k1_relset_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) @ ( k2_funct_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['45','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['32','33'])).

thf('58',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['56','57','58','59'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('61',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('62',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['44','62'])).

thf('64',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['16','17'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('66',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['32','33'])).

thf('68',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['63','64','66','67','68','69'])).

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

thf('71',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('72',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('73',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_1 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('74',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['71','74'])).

thf('76',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ( X22
        = ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ~ ( zip_tseitin_1 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('78',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('80',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['75','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('83',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ sk_A ) ) )
    | ( sk_B = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['16','17'])).

thf('85',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['32','33'])).

thf('86',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['83','84','85','86','87'])).

thf('89',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['89'])).

thf('91',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['88','90'])).

thf('92',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['32','33'])).

thf('93',plain,(
    ! [X6: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v2_funct_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('94',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['89'])).

thf('95',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ~ ( v1_relat_1 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['92','98'])).

thf('100',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['89'])).

thf('101',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['75','80'])).

thf('102',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k1_relat_1 @ X7 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('103',plain,(
    ! [X6: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v2_funct_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('104',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v2_funct_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('105',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_relat_1 @ X7 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('106',plain,(
    ! [X28: $i] :
      ( ( v1_funct_2 @ X28 @ ( k1_relat_1 @ X28 ) @ ( k2_relat_1 @ X28 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['104','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['103','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['102','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_A )
    | ( sk_B = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['101','113'])).

thf('115',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['16','17'])).

thf('116',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['32','33'])).

thf('117',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['114','115','116','117','118'])).

thf('120',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['89'])).

thf('121',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['100','121'])).

thf('123',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('124',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['5','8'])).

thf('125',plain,(
    ! [X6: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v2_funct_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('126',plain,(
    ! [X6: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v2_funct_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('127',plain,(
    ! [X6: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v2_funct_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('128',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_relat_1 @ X7 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('129',plain,(
    ! [X6: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v2_funct_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('130',plain,(
    ! [X6: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v2_funct_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('131',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('132',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k1_relat_1 @ X7 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('133',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_relat_1 @ X7 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('134',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v2_funct_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('135',plain,(
    ! [X6: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v2_funct_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('136',plain,(
    ! [X6: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v2_funct_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('137',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k1_relat_1 @ X7 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('138',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['136','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( m1_subset_1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['135','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['134','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['133','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['132','150'])).

thf('152',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['131','154'])).

thf('156',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['32','33'])).

thf('157',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['155','156','157','158'])).

thf('160',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['130','159'])).

thf('161',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['32','33'])).

thf('162',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['160','161','162','163'])).

thf('165',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['129','164'])).

thf('166',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['32','33'])).

thf('167',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['165','166','167','168'])).

thf('170',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['128','169'])).

thf('171',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('172',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['170','171'])).

thf('173',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['127','172'])).

thf('174',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['32','33'])).

thf('175',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['173','174','175','176'])).

thf('178',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['126','177'])).

thf('179',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['32','33'])).

thf('180',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['178','179','180','181'])).

thf('183',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X29 ) @ X30 )
      | ( v1_funct_2 @ X29 @ ( k1_relat_1 @ X29 ) @ X30 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('184',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
      | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('186',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['63','64','66','67','68','69'])).

thf('187',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
      | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['184','185','186'])).

thf('188',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C )
      | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['125','187'])).

thf('189',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['32','33'])).

thf('190',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['188','189','190','191'])).

thf('193',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['124','192'])).

thf('194',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['123','193'])).

thf('195',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['122','194'])).

thf('196',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['89'])).

thf('197',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['99','195','196'])).

thf('198',plain,(
    sk_B = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['91','197'])).

thf('199',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['70','198'])).

thf('200',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['43','199'])).

thf('201',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['89'])).

thf('202',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['88','90'])).

thf('203',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['201','202'])).

thf('204',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['99','195','196'])).

thf('205',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['203','204'])).

thf('206',plain,(
    ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['200','205'])).

thf('207',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','206'])).

thf('208',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['32','33'])).

thf('209',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,(
    $false ),
    inference(demod,[status(thm)],['207','208','209','210'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zyoaTZQuDh
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:21:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 6.07/6.27  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.07/6.27  % Solved by: fo/fo7.sh
% 6.07/6.27  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.07/6.27  % done 3196 iterations in 5.820s
% 6.07/6.27  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.07/6.27  % SZS output start Refutation
% 6.07/6.27  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.07/6.27  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 6.07/6.27  thf(sk_C_type, type, sk_C: $i).
% 6.07/6.27  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 6.07/6.27  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.07/6.27  thf(sk_B_type, type, sk_B: $i).
% 6.07/6.27  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 6.07/6.27  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 6.07/6.27  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 6.07/6.27  thf(sk_A_type, type, sk_A: $i).
% 6.07/6.27  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 6.07/6.27  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 6.07/6.27  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.07/6.27  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.07/6.27  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 6.07/6.27  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 6.07/6.27  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 6.07/6.27  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 6.07/6.27  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 6.07/6.27  thf(fc6_funct_1, axiom,
% 6.07/6.27    (![A:$i]:
% 6.07/6.27     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 6.07/6.27       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 6.07/6.27         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 6.07/6.27         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 6.07/6.27  thf('0', plain,
% 6.07/6.27      (![X6 : $i]:
% 6.07/6.27         ((v1_funct_1 @ (k2_funct_1 @ X6))
% 6.07/6.27          | ~ (v2_funct_1 @ X6)
% 6.07/6.27          | ~ (v1_funct_1 @ X6)
% 6.07/6.27          | ~ (v1_relat_1 @ X6))),
% 6.07/6.27      inference('cnf', [status(esa)], [fc6_funct_1])).
% 6.07/6.27  thf(t31_funct_2, conjecture,
% 6.07/6.27    (![A:$i,B:$i,C:$i]:
% 6.07/6.27     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 6.07/6.27         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.07/6.27       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 6.07/6.27         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 6.07/6.27           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 6.07/6.27           ( m1_subset_1 @
% 6.07/6.27             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 6.07/6.27  thf(zf_stmt_0, negated_conjecture,
% 6.07/6.27    (~( ![A:$i,B:$i,C:$i]:
% 6.07/6.27        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 6.07/6.27            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.07/6.27          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 6.07/6.27            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 6.07/6.27              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 6.07/6.27              ( m1_subset_1 @
% 6.07/6.27                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 6.07/6.27    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 6.07/6.27  thf('1', plain,
% 6.07/6.27      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.07/6.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.07/6.27  thf(dt_k1_relset_1, axiom,
% 6.07/6.27    (![A:$i,B:$i,C:$i]:
% 6.07/6.27     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.07/6.27       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 6.07/6.27  thf('2', plain,
% 6.07/6.27      (![X11 : $i, X12 : $i, X13 : $i]:
% 6.07/6.27         ((m1_subset_1 @ (k1_relset_1 @ X11 @ X12 @ X13) @ (k1_zfmisc_1 @ X11))
% 6.07/6.27          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 6.07/6.27      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 6.07/6.27  thf('3', plain,
% 6.07/6.27      ((m1_subset_1 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 6.07/6.27      inference('sup-', [status(thm)], ['1', '2'])).
% 6.07/6.27  thf(t3_subset, axiom,
% 6.07/6.27    (![A:$i,B:$i]:
% 6.07/6.27     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 6.07/6.27  thf('4', plain,
% 6.07/6.27      (![X3 : $i, X4 : $i]:
% 6.07/6.27         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 6.07/6.27      inference('cnf', [status(esa)], [t3_subset])).
% 6.07/6.27  thf('5', plain, ((r1_tarski @ (k1_relset_1 @ sk_A @ sk_B @ sk_C) @ sk_A)),
% 6.07/6.27      inference('sup-', [status(thm)], ['3', '4'])).
% 6.07/6.27  thf('6', plain,
% 6.07/6.27      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.07/6.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.07/6.27  thf(redefinition_k1_relset_1, axiom,
% 6.07/6.27    (![A:$i,B:$i,C:$i]:
% 6.07/6.27     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.07/6.27       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 6.07/6.27  thf('7', plain,
% 6.07/6.27      (![X14 : $i, X15 : $i, X16 : $i]:
% 6.07/6.27         (((k1_relset_1 @ X15 @ X16 @ X14) = (k1_relat_1 @ X14))
% 6.07/6.27          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 6.07/6.27      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 6.07/6.27  thf('8', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 6.07/6.27      inference('sup-', [status(thm)], ['6', '7'])).
% 6.07/6.27  thf('9', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 6.07/6.27      inference('demod', [status(thm)], ['5', '8'])).
% 6.07/6.27  thf(t55_funct_1, axiom,
% 6.07/6.27    (![A:$i]:
% 6.07/6.27     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 6.07/6.27       ( ( v2_funct_1 @ A ) =>
% 6.07/6.27         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 6.07/6.27           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 6.07/6.27  thf('10', plain,
% 6.07/6.27      (![X7 : $i]:
% 6.07/6.27         (~ (v2_funct_1 @ X7)
% 6.07/6.27          | ((k1_relat_1 @ X7) = (k2_relat_1 @ (k2_funct_1 @ X7)))
% 6.07/6.27          | ~ (v1_funct_1 @ X7)
% 6.07/6.27          | ~ (v1_relat_1 @ X7))),
% 6.07/6.27      inference('cnf', [status(esa)], [t55_funct_1])).
% 6.07/6.27  thf(t4_funct_2, axiom,
% 6.07/6.27    (![A:$i,B:$i]:
% 6.07/6.27     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 6.07/6.27       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 6.07/6.27         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 6.07/6.27           ( m1_subset_1 @
% 6.07/6.27             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 6.07/6.27  thf('11', plain,
% 6.07/6.27      (![X29 : $i, X30 : $i]:
% 6.07/6.27         (~ (r1_tarski @ (k2_relat_1 @ X29) @ X30)
% 6.07/6.27          | (m1_subset_1 @ X29 @ 
% 6.07/6.27             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X29) @ X30)))
% 6.07/6.27          | ~ (v1_funct_1 @ X29)
% 6.07/6.27          | ~ (v1_relat_1 @ X29))),
% 6.07/6.27      inference('cnf', [status(esa)], [t4_funct_2])).
% 6.07/6.27  thf('12', plain,
% 6.07/6.27      (![X0 : $i, X1 : $i]:
% 6.07/6.27         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 6.07/6.27          | ~ (v1_relat_1 @ X0)
% 6.07/6.27          | ~ (v1_funct_1 @ X0)
% 6.07/6.27          | ~ (v2_funct_1 @ X0)
% 6.07/6.27          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 6.07/6.27          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.07/6.27          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 6.07/6.27             (k1_zfmisc_1 @ 
% 6.07/6.27              (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ X1))))),
% 6.07/6.27      inference('sup-', [status(thm)], ['10', '11'])).
% 6.07/6.27  thf('13', plain,
% 6.07/6.27      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.07/6.27         (k1_zfmisc_1 @ 
% 6.07/6.27          (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)))
% 6.07/6.27        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 6.07/6.27        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 6.07/6.27        | ~ (v2_funct_1 @ sk_C)
% 6.07/6.27        | ~ (v1_funct_1 @ sk_C)
% 6.07/6.27        | ~ (v1_relat_1 @ sk_C))),
% 6.07/6.27      inference('sup-', [status(thm)], ['9', '12'])).
% 6.07/6.27  thf('14', plain,
% 6.07/6.27      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.07/6.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.07/6.27  thf(redefinition_k2_relset_1, axiom,
% 6.07/6.27    (![A:$i,B:$i,C:$i]:
% 6.07/6.27     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.07/6.27       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 6.07/6.27  thf('15', plain,
% 6.07/6.27      (![X17 : $i, X18 : $i, X19 : $i]:
% 6.07/6.27         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 6.07/6.27          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 6.07/6.27      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 6.07/6.27  thf('16', plain,
% 6.07/6.27      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 6.07/6.27      inference('sup-', [status(thm)], ['14', '15'])).
% 6.07/6.27  thf('17', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 6.07/6.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.07/6.27  thf('18', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 6.07/6.27      inference('sup+', [status(thm)], ['16', '17'])).
% 6.07/6.27  thf('19', plain,
% 6.07/6.27      (![X7 : $i]:
% 6.07/6.27         (~ (v2_funct_1 @ X7)
% 6.07/6.27          | ((k1_relat_1 @ X7) = (k2_relat_1 @ (k2_funct_1 @ X7)))
% 6.07/6.27          | ~ (v1_funct_1 @ X7)
% 6.07/6.27          | ~ (v1_relat_1 @ X7))),
% 6.07/6.27      inference('cnf', [status(esa)], [t55_funct_1])).
% 6.07/6.27  thf('20', plain,
% 6.07/6.27      (![X6 : $i]:
% 6.07/6.27         ((v1_funct_1 @ (k2_funct_1 @ X6))
% 6.07/6.27          | ~ (v2_funct_1 @ X6)
% 6.07/6.27          | ~ (v1_funct_1 @ X6)
% 6.07/6.27          | ~ (v1_relat_1 @ X6))),
% 6.07/6.27      inference('cnf', [status(esa)], [fc6_funct_1])).
% 6.07/6.27  thf('21', plain,
% 6.07/6.27      (![X6 : $i]:
% 6.07/6.27         ((v1_relat_1 @ (k2_funct_1 @ X6))
% 6.07/6.27          | ~ (v2_funct_1 @ X6)
% 6.07/6.27          | ~ (v1_funct_1 @ X6)
% 6.07/6.27          | ~ (v1_relat_1 @ X6))),
% 6.07/6.27      inference('cnf', [status(esa)], [fc6_funct_1])).
% 6.07/6.27  thf('22', plain,
% 6.07/6.27      (![X7 : $i]:
% 6.07/6.27         (~ (v2_funct_1 @ X7)
% 6.07/6.27          | ((k2_relat_1 @ X7) = (k1_relat_1 @ (k2_funct_1 @ X7)))
% 6.07/6.27          | ~ (v1_funct_1 @ X7)
% 6.07/6.27          | ~ (v1_relat_1 @ X7))),
% 6.07/6.27      inference('cnf', [status(esa)], [t55_funct_1])).
% 6.07/6.27  thf(t3_funct_2, axiom,
% 6.07/6.27    (![A:$i]:
% 6.07/6.27     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 6.07/6.27       ( ( v1_funct_1 @ A ) & 
% 6.07/6.27         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 6.07/6.27         ( m1_subset_1 @
% 6.07/6.27           A @ 
% 6.07/6.27           ( k1_zfmisc_1 @
% 6.07/6.27             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 6.07/6.27  thf('23', plain,
% 6.07/6.27      (![X28 : $i]:
% 6.07/6.27         ((m1_subset_1 @ X28 @ 
% 6.07/6.27           (k1_zfmisc_1 @ 
% 6.07/6.27            (k2_zfmisc_1 @ (k1_relat_1 @ X28) @ (k2_relat_1 @ X28))))
% 6.07/6.27          | ~ (v1_funct_1 @ X28)
% 6.07/6.27          | ~ (v1_relat_1 @ X28))),
% 6.07/6.27      inference('cnf', [status(esa)], [t3_funct_2])).
% 6.07/6.27  thf('24', plain,
% 6.07/6.27      (![X0 : $i]:
% 6.07/6.27         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 6.07/6.27           (k1_zfmisc_1 @ 
% 6.07/6.27            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 6.07/6.27          | ~ (v1_relat_1 @ X0)
% 6.07/6.27          | ~ (v1_funct_1 @ X0)
% 6.07/6.27          | ~ (v2_funct_1 @ X0)
% 6.07/6.27          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 6.07/6.27          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 6.07/6.27      inference('sup+', [status(thm)], ['22', '23'])).
% 6.07/6.27  thf('25', plain,
% 6.07/6.27      (![X0 : $i]:
% 6.07/6.27         (~ (v1_relat_1 @ X0)
% 6.07/6.27          | ~ (v1_funct_1 @ X0)
% 6.07/6.27          | ~ (v2_funct_1 @ X0)
% 6.07/6.27          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.07/6.27          | ~ (v2_funct_1 @ X0)
% 6.07/6.27          | ~ (v1_funct_1 @ X0)
% 6.07/6.27          | ~ (v1_relat_1 @ X0)
% 6.07/6.27          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 6.07/6.27             (k1_zfmisc_1 @ 
% 6.07/6.27              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 6.07/6.27               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 6.07/6.27      inference('sup-', [status(thm)], ['21', '24'])).
% 6.07/6.27  thf('26', plain,
% 6.07/6.27      (![X0 : $i]:
% 6.07/6.27         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 6.07/6.27           (k1_zfmisc_1 @ 
% 6.07/6.27            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 6.07/6.27          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.07/6.27          | ~ (v2_funct_1 @ X0)
% 6.07/6.27          | ~ (v1_funct_1 @ X0)
% 6.07/6.27          | ~ (v1_relat_1 @ X0))),
% 6.07/6.27      inference('simplify', [status(thm)], ['25'])).
% 6.07/6.27  thf('27', plain,
% 6.07/6.27      (![X0 : $i]:
% 6.07/6.27         (~ (v1_relat_1 @ X0)
% 6.07/6.27          | ~ (v1_funct_1 @ X0)
% 6.07/6.27          | ~ (v2_funct_1 @ X0)
% 6.07/6.27          | ~ (v1_relat_1 @ X0)
% 6.07/6.27          | ~ (v1_funct_1 @ X0)
% 6.07/6.27          | ~ (v2_funct_1 @ X0)
% 6.07/6.27          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 6.07/6.27             (k1_zfmisc_1 @ 
% 6.07/6.27              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 6.07/6.27               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 6.07/6.27      inference('sup-', [status(thm)], ['20', '26'])).
% 6.07/6.27  thf('28', plain,
% 6.07/6.27      (![X0 : $i]:
% 6.07/6.27         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 6.07/6.27           (k1_zfmisc_1 @ 
% 6.07/6.27            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 6.07/6.27          | ~ (v2_funct_1 @ X0)
% 6.07/6.27          | ~ (v1_funct_1 @ X0)
% 6.07/6.27          | ~ (v1_relat_1 @ X0))),
% 6.07/6.27      inference('simplify', [status(thm)], ['27'])).
% 6.07/6.27  thf('29', plain,
% 6.07/6.27      (![X0 : $i]:
% 6.07/6.27         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 6.07/6.27           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))))
% 6.07/6.27          | ~ (v1_relat_1 @ X0)
% 6.07/6.27          | ~ (v1_funct_1 @ X0)
% 6.07/6.27          | ~ (v2_funct_1 @ X0)
% 6.07/6.27          | ~ (v1_relat_1 @ X0)
% 6.07/6.27          | ~ (v1_funct_1 @ X0)
% 6.07/6.27          | ~ (v2_funct_1 @ X0))),
% 6.07/6.27      inference('sup+', [status(thm)], ['19', '28'])).
% 6.07/6.27  thf('30', plain,
% 6.07/6.27      (![X0 : $i]:
% 6.07/6.27         (~ (v2_funct_1 @ X0)
% 6.07/6.27          | ~ (v1_funct_1 @ X0)
% 6.07/6.27          | ~ (v1_relat_1 @ X0)
% 6.07/6.27          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 6.07/6.27             (k1_zfmisc_1 @ 
% 6.07/6.27              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))))),
% 6.07/6.27      inference('simplify', [status(thm)], ['29'])).
% 6.07/6.27  thf('31', plain,
% 6.07/6.27      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.07/6.27         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C))))
% 6.07/6.27        | ~ (v1_relat_1 @ sk_C)
% 6.07/6.27        | ~ (v1_funct_1 @ sk_C)
% 6.07/6.27        | ~ (v2_funct_1 @ sk_C))),
% 6.07/6.27      inference('sup+', [status(thm)], ['18', '30'])).
% 6.07/6.27  thf('32', plain,
% 6.07/6.27      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.07/6.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.07/6.27  thf(cc1_relset_1, axiom,
% 6.07/6.27    (![A:$i,B:$i,C:$i]:
% 6.07/6.27     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.07/6.27       ( v1_relat_1 @ C ) ))).
% 6.07/6.27  thf('33', plain,
% 6.07/6.27      (![X8 : $i, X9 : $i, X10 : $i]:
% 6.07/6.27         ((v1_relat_1 @ X8)
% 6.07/6.27          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 6.07/6.27      inference('cnf', [status(esa)], [cc1_relset_1])).
% 6.07/6.27  thf('34', plain, ((v1_relat_1 @ sk_C)),
% 6.07/6.27      inference('sup-', [status(thm)], ['32', '33'])).
% 6.07/6.27  thf('35', plain, ((v1_funct_1 @ sk_C)),
% 6.07/6.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.07/6.27  thf('36', plain, ((v2_funct_1 @ sk_C)),
% 6.07/6.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.07/6.27  thf('37', plain,
% 6.07/6.27      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.07/6.27        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C))))),
% 6.07/6.27      inference('demod', [status(thm)], ['31', '34', '35', '36'])).
% 6.07/6.27  thf('38', plain,
% 6.07/6.27      (![X8 : $i, X9 : $i, X10 : $i]:
% 6.07/6.27         ((v1_relat_1 @ X8)
% 6.07/6.27          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 6.07/6.27      inference('cnf', [status(esa)], [cc1_relset_1])).
% 6.07/6.27  thf('39', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 6.07/6.27      inference('sup-', [status(thm)], ['37', '38'])).
% 6.07/6.27  thf('40', plain, ((v2_funct_1 @ sk_C)),
% 6.07/6.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.07/6.27  thf('41', plain, ((v1_funct_1 @ sk_C)),
% 6.07/6.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.07/6.27  thf('42', plain, ((v1_relat_1 @ sk_C)),
% 6.07/6.27      inference('sup-', [status(thm)], ['32', '33'])).
% 6.07/6.27  thf('43', plain,
% 6.07/6.27      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.07/6.27         (k1_zfmisc_1 @ 
% 6.07/6.27          (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)))
% 6.07/6.27        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 6.07/6.27      inference('demod', [status(thm)], ['13', '39', '40', '41', '42'])).
% 6.07/6.27  thf('44', plain,
% 6.07/6.27      (![X7 : $i]:
% 6.07/6.27         (~ (v2_funct_1 @ X7)
% 6.07/6.27          | ((k2_relat_1 @ X7) = (k1_relat_1 @ (k2_funct_1 @ X7)))
% 6.07/6.27          | ~ (v1_funct_1 @ X7)
% 6.07/6.27          | ~ (v1_relat_1 @ X7))),
% 6.07/6.27      inference('cnf', [status(esa)], [t55_funct_1])).
% 6.07/6.27  thf('45', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 6.07/6.27      inference('sup+', [status(thm)], ['16', '17'])).
% 6.07/6.27  thf('46', plain,
% 6.07/6.27      (![X0 : $i]:
% 6.07/6.27         (~ (v2_funct_1 @ X0)
% 6.07/6.27          | ~ (v1_funct_1 @ X0)
% 6.07/6.27          | ~ (v1_relat_1 @ X0)
% 6.07/6.27          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 6.07/6.27             (k1_zfmisc_1 @ 
% 6.07/6.27              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))))),
% 6.07/6.27      inference('simplify', [status(thm)], ['29'])).
% 6.07/6.27  thf('47', plain,
% 6.07/6.27      (![X14 : $i, X15 : $i, X16 : $i]:
% 6.07/6.27         (((k1_relset_1 @ X15 @ X16 @ X14) = (k1_relat_1 @ X14))
% 6.07/6.27          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 6.07/6.27      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 6.07/6.27  thf('48', plain,
% 6.07/6.27      (![X0 : $i]:
% 6.07/6.27         (~ (v1_relat_1 @ X0)
% 6.07/6.27          | ~ (v1_funct_1 @ X0)
% 6.07/6.27          | ~ (v2_funct_1 @ X0)
% 6.07/6.27          | ((k1_relset_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0) @ 
% 6.07/6.27              (k2_funct_1 @ X0)) = (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 6.07/6.27      inference('sup-', [status(thm)], ['46', '47'])).
% 6.07/6.27  thf('49', plain,
% 6.07/6.27      (![X0 : $i]:
% 6.07/6.27         (~ (v2_funct_1 @ X0)
% 6.07/6.27          | ~ (v1_funct_1 @ X0)
% 6.07/6.27          | ~ (v1_relat_1 @ X0)
% 6.07/6.27          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 6.07/6.27             (k1_zfmisc_1 @ 
% 6.07/6.27              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))))),
% 6.07/6.27      inference('simplify', [status(thm)], ['29'])).
% 6.07/6.27  thf('50', plain,
% 6.07/6.27      (![X11 : $i, X12 : $i, X13 : $i]:
% 6.07/6.27         ((m1_subset_1 @ (k1_relset_1 @ X11 @ X12 @ X13) @ (k1_zfmisc_1 @ X11))
% 6.07/6.27          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 6.07/6.27      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 6.07/6.27  thf('51', plain,
% 6.07/6.27      (![X0 : $i]:
% 6.07/6.27         (~ (v1_relat_1 @ X0)
% 6.07/6.27          | ~ (v1_funct_1 @ X0)
% 6.07/6.27          | ~ (v2_funct_1 @ X0)
% 6.07/6.27          | (m1_subset_1 @ 
% 6.07/6.27             (k1_relset_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0) @ 
% 6.07/6.27              (k2_funct_1 @ X0)) @ 
% 6.07/6.27             (k1_zfmisc_1 @ (k2_relat_1 @ X0))))),
% 6.07/6.27      inference('sup-', [status(thm)], ['49', '50'])).
% 6.07/6.27  thf('52', plain,
% 6.07/6.27      (![X0 : $i]:
% 6.07/6.27         ((m1_subset_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ 
% 6.07/6.27           (k1_zfmisc_1 @ (k2_relat_1 @ X0)))
% 6.07/6.27          | ~ (v2_funct_1 @ X0)
% 6.07/6.27          | ~ (v1_funct_1 @ X0)
% 6.07/6.27          | ~ (v1_relat_1 @ X0)
% 6.07/6.27          | ~ (v2_funct_1 @ X0)
% 6.07/6.27          | ~ (v1_funct_1 @ X0)
% 6.07/6.27          | ~ (v1_relat_1 @ X0))),
% 6.07/6.27      inference('sup+', [status(thm)], ['48', '51'])).
% 6.07/6.27  thf('53', plain,
% 6.07/6.27      (![X0 : $i]:
% 6.07/6.27         (~ (v1_relat_1 @ X0)
% 6.07/6.27          | ~ (v1_funct_1 @ X0)
% 6.07/6.27          | ~ (v2_funct_1 @ X0)
% 6.07/6.27          | (m1_subset_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ 
% 6.07/6.27             (k1_zfmisc_1 @ (k2_relat_1 @ X0))))),
% 6.07/6.27      inference('simplify', [status(thm)], ['52'])).
% 6.07/6.27  thf('54', plain,
% 6.07/6.27      (![X3 : $i, X4 : $i]:
% 6.07/6.27         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 6.07/6.27      inference('cnf', [status(esa)], [t3_subset])).
% 6.07/6.27  thf('55', plain,
% 6.07/6.27      (![X0 : $i]:
% 6.07/6.27         (~ (v2_funct_1 @ X0)
% 6.07/6.27          | ~ (v1_funct_1 @ X0)
% 6.07/6.27          | ~ (v1_relat_1 @ X0)
% 6.07/6.27          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0)))),
% 6.07/6.27      inference('sup-', [status(thm)], ['53', '54'])).
% 6.07/6.27  thf('56', plain,
% 6.07/6.27      (((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B)
% 6.07/6.27        | ~ (v1_relat_1 @ sk_C)
% 6.07/6.27        | ~ (v1_funct_1 @ sk_C)
% 6.07/6.27        | ~ (v2_funct_1 @ sk_C))),
% 6.07/6.27      inference('sup+', [status(thm)], ['45', '55'])).
% 6.07/6.27  thf('57', plain, ((v1_relat_1 @ sk_C)),
% 6.07/6.27      inference('sup-', [status(thm)], ['32', '33'])).
% 6.07/6.27  thf('58', plain, ((v1_funct_1 @ sk_C)),
% 6.07/6.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.07/6.27  thf('59', plain, ((v2_funct_1 @ sk_C)),
% 6.07/6.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.07/6.27  thf('60', plain, ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B)),
% 6.07/6.27      inference('demod', [status(thm)], ['56', '57', '58', '59'])).
% 6.07/6.27  thf(d10_xboole_0, axiom,
% 6.07/6.27    (![A:$i,B:$i]:
% 6.07/6.27     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 6.07/6.27  thf('61', plain,
% 6.07/6.27      (![X0 : $i, X2 : $i]:
% 6.07/6.27         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 6.07/6.27      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.07/6.27  thf('62', plain,
% 6.07/6.27      ((~ (r1_tarski @ sk_B @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 6.07/6.27        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 6.07/6.27      inference('sup-', [status(thm)], ['60', '61'])).
% 6.07/6.27  thf('63', plain,
% 6.07/6.27      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C))
% 6.07/6.27        | ~ (v1_relat_1 @ sk_C)
% 6.07/6.27        | ~ (v1_funct_1 @ sk_C)
% 6.07/6.27        | ~ (v2_funct_1 @ sk_C)
% 6.07/6.27        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 6.07/6.27      inference('sup-', [status(thm)], ['44', '62'])).
% 6.07/6.27  thf('64', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 6.07/6.27      inference('sup+', [status(thm)], ['16', '17'])).
% 6.07/6.27  thf('65', plain,
% 6.07/6.27      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 6.07/6.27      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.07/6.27  thf('66', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 6.07/6.27      inference('simplify', [status(thm)], ['65'])).
% 6.07/6.27  thf('67', plain, ((v1_relat_1 @ sk_C)),
% 6.07/6.27      inference('sup-', [status(thm)], ['32', '33'])).
% 6.07/6.27  thf('68', plain, ((v1_funct_1 @ sk_C)),
% 6.07/6.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.07/6.27  thf('69', plain, ((v2_funct_1 @ sk_C)),
% 6.07/6.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.07/6.27  thf('70', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 6.07/6.27      inference('demod', [status(thm)], ['63', '64', '66', '67', '68', '69'])).
% 6.07/6.27  thf(d1_funct_2, axiom,
% 6.07/6.27    (![A:$i,B:$i,C:$i]:
% 6.07/6.27     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.07/6.27       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 6.07/6.27           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 6.07/6.27             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 6.07/6.27         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 6.07/6.27           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 6.07/6.27             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 6.07/6.27  thf(zf_stmt_1, axiom,
% 6.07/6.27    (![B:$i,A:$i]:
% 6.07/6.27     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 6.07/6.27       ( zip_tseitin_0 @ B @ A ) ))).
% 6.07/6.27  thf('71', plain,
% 6.07/6.27      (![X20 : $i, X21 : $i]:
% 6.07/6.27         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 6.07/6.27      inference('cnf', [status(esa)], [zf_stmt_1])).
% 6.07/6.27  thf('72', plain,
% 6.07/6.27      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 6.07/6.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.07/6.27  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 6.07/6.27  thf(zf_stmt_3, axiom,
% 6.07/6.27    (![C:$i,B:$i,A:$i]:
% 6.07/6.27     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 6.07/6.27       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 6.07/6.27  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 6.07/6.27  thf(zf_stmt_5, axiom,
% 6.07/6.27    (![A:$i,B:$i,C:$i]:
% 6.07/6.27     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.07/6.27       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 6.07/6.27         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 6.07/6.27           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 6.07/6.27             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 6.07/6.27  thf('73', plain,
% 6.07/6.27      (![X25 : $i, X26 : $i, X27 : $i]:
% 6.07/6.27         (~ (zip_tseitin_0 @ X25 @ X26)
% 6.07/6.27          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 6.07/6.27          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 6.07/6.27      inference('cnf', [status(esa)], [zf_stmt_5])).
% 6.07/6.27  thf('74', plain,
% 6.07/6.27      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 6.07/6.27      inference('sup-', [status(thm)], ['72', '73'])).
% 6.07/6.27  thf('75', plain,
% 6.07/6.27      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 6.07/6.27      inference('sup-', [status(thm)], ['71', '74'])).
% 6.07/6.27  thf('76', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 6.07/6.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.07/6.27  thf('77', plain,
% 6.07/6.27      (![X22 : $i, X23 : $i, X24 : $i]:
% 6.07/6.27         (~ (v1_funct_2 @ X24 @ X22 @ X23)
% 6.07/6.27          | ((X22) = (k1_relset_1 @ X22 @ X23 @ X24))
% 6.07/6.27          | ~ (zip_tseitin_1 @ X24 @ X23 @ X22))),
% 6.07/6.27      inference('cnf', [status(esa)], [zf_stmt_3])).
% 6.07/6.27  thf('78', plain,
% 6.07/6.27      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 6.07/6.27        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 6.07/6.27      inference('sup-', [status(thm)], ['76', '77'])).
% 6.07/6.27  thf('79', plain,
% 6.07/6.27      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 6.07/6.27      inference('sup-', [status(thm)], ['6', '7'])).
% 6.07/6.27  thf('80', plain,
% 6.07/6.27      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 6.07/6.27      inference('demod', [status(thm)], ['78', '79'])).
% 6.07/6.27  thf('81', plain,
% 6.07/6.27      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 6.07/6.27      inference('sup-', [status(thm)], ['75', '80'])).
% 6.07/6.27  thf('82', plain,
% 6.07/6.27      (![X0 : $i]:
% 6.07/6.27         (~ (v2_funct_1 @ X0)
% 6.07/6.27          | ~ (v1_funct_1 @ X0)
% 6.07/6.27          | ~ (v1_relat_1 @ X0)
% 6.07/6.27          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 6.07/6.27             (k1_zfmisc_1 @ 
% 6.07/6.27              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))))),
% 6.07/6.27      inference('simplify', [status(thm)], ['29'])).
% 6.07/6.27  thf('83', plain,
% 6.07/6.27      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.07/6.27         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ sk_A)))
% 6.07/6.27        | ((sk_B) = (k1_xboole_0))
% 6.07/6.27        | ~ (v1_relat_1 @ sk_C)
% 6.07/6.27        | ~ (v1_funct_1 @ sk_C)
% 6.07/6.27        | ~ (v2_funct_1 @ sk_C))),
% 6.07/6.27      inference('sup+', [status(thm)], ['81', '82'])).
% 6.07/6.27  thf('84', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 6.07/6.27      inference('sup+', [status(thm)], ['16', '17'])).
% 6.07/6.27  thf('85', plain, ((v1_relat_1 @ sk_C)),
% 6.07/6.27      inference('sup-', [status(thm)], ['32', '33'])).
% 6.07/6.27  thf('86', plain, ((v1_funct_1 @ sk_C)),
% 6.07/6.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.07/6.27  thf('87', plain, ((v2_funct_1 @ sk_C)),
% 6.07/6.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.07/6.27  thf('88', plain,
% 6.07/6.27      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.07/6.27         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 6.07/6.27        | ((sk_B) = (k1_xboole_0)))),
% 6.07/6.27      inference('demod', [status(thm)], ['83', '84', '85', '86', '87'])).
% 6.07/6.27  thf('89', plain,
% 6.07/6.27      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 6.07/6.27        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 6.07/6.27        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.07/6.27             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 6.07/6.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.07/6.27  thf('90', plain,
% 6.07/6.27      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.07/6.27           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 6.07/6.27         <= (~
% 6.07/6.27             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.07/6.27               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 6.07/6.27      inference('split', [status(esa)], ['89'])).
% 6.07/6.27  thf('91', plain,
% 6.07/6.27      ((((sk_B) = (k1_xboole_0)))
% 6.07/6.27         <= (~
% 6.07/6.27             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.07/6.27               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 6.07/6.27      inference('sup-', [status(thm)], ['88', '90'])).
% 6.07/6.27  thf('92', plain, ((v1_relat_1 @ sk_C)),
% 6.07/6.27      inference('sup-', [status(thm)], ['32', '33'])).
% 6.07/6.27  thf('93', plain,
% 6.07/6.27      (![X6 : $i]:
% 6.07/6.27         ((v1_funct_1 @ (k2_funct_1 @ X6))
% 6.07/6.27          | ~ (v2_funct_1 @ X6)
% 6.07/6.27          | ~ (v1_funct_1 @ X6)
% 6.07/6.27          | ~ (v1_relat_1 @ X6))),
% 6.07/6.27      inference('cnf', [status(esa)], [fc6_funct_1])).
% 6.07/6.27  thf('94', plain,
% 6.07/6.27      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 6.07/6.27         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 6.07/6.27      inference('split', [status(esa)], ['89'])).
% 6.07/6.27  thf('95', plain,
% 6.07/6.27      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C) | ~ (v2_funct_1 @ sk_C)))
% 6.07/6.27         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 6.07/6.27      inference('sup-', [status(thm)], ['93', '94'])).
% 6.07/6.27  thf('96', plain, ((v1_funct_1 @ sk_C)),
% 6.07/6.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.07/6.27  thf('97', plain, ((v2_funct_1 @ sk_C)),
% 6.07/6.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.07/6.27  thf('98', plain,
% 6.07/6.27      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 6.07/6.27      inference('demod', [status(thm)], ['95', '96', '97'])).
% 6.07/6.27  thf('99', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 6.07/6.27      inference('sup-', [status(thm)], ['92', '98'])).
% 6.07/6.27  thf('100', plain,
% 6.07/6.27      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 6.07/6.27         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 6.07/6.27      inference('split', [status(esa)], ['89'])).
% 6.07/6.27  thf('101', plain,
% 6.07/6.27      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 6.07/6.27      inference('sup-', [status(thm)], ['75', '80'])).
% 6.07/6.27  thf('102', plain,
% 6.07/6.27      (![X7 : $i]:
% 6.07/6.27         (~ (v2_funct_1 @ X7)
% 6.07/6.27          | ((k1_relat_1 @ X7) = (k2_relat_1 @ (k2_funct_1 @ X7)))
% 6.07/6.27          | ~ (v1_funct_1 @ X7)
% 6.07/6.27          | ~ (v1_relat_1 @ X7))),
% 6.07/6.27      inference('cnf', [status(esa)], [t55_funct_1])).
% 6.07/6.27  thf('103', plain,
% 6.07/6.27      (![X6 : $i]:
% 6.07/6.27         ((v1_funct_1 @ (k2_funct_1 @ X6))
% 6.07/6.27          | ~ (v2_funct_1 @ X6)
% 6.07/6.27          | ~ (v1_funct_1 @ X6)
% 6.07/6.27          | ~ (v1_relat_1 @ X6))),
% 6.07/6.27      inference('cnf', [status(esa)], [fc6_funct_1])).
% 6.07/6.27  thf('104', plain,
% 6.07/6.27      (![X6 : $i]:
% 6.07/6.27         ((v1_relat_1 @ (k2_funct_1 @ X6))
% 6.07/6.27          | ~ (v2_funct_1 @ X6)
% 6.07/6.27          | ~ (v1_funct_1 @ X6)
% 6.07/6.27          | ~ (v1_relat_1 @ X6))),
% 6.07/6.27      inference('cnf', [status(esa)], [fc6_funct_1])).
% 6.07/6.27  thf('105', plain,
% 6.07/6.27      (![X7 : $i]:
% 6.07/6.27         (~ (v2_funct_1 @ X7)
% 6.07/6.27          | ((k2_relat_1 @ X7) = (k1_relat_1 @ (k2_funct_1 @ X7)))
% 6.07/6.27          | ~ (v1_funct_1 @ X7)
% 6.07/6.27          | ~ (v1_relat_1 @ X7))),
% 6.07/6.27      inference('cnf', [status(esa)], [t55_funct_1])).
% 6.07/6.27  thf('106', plain,
% 6.07/6.27      (![X28 : $i]:
% 6.07/6.27         ((v1_funct_2 @ X28 @ (k1_relat_1 @ X28) @ (k2_relat_1 @ X28))
% 6.07/6.27          | ~ (v1_funct_1 @ X28)
% 6.07/6.27          | ~ (v1_relat_1 @ X28))),
% 6.07/6.27      inference('cnf', [status(esa)], [t3_funct_2])).
% 6.07/6.27  thf('107', plain,
% 6.07/6.27      (![X0 : $i]:
% 6.07/6.27         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 6.07/6.27           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 6.07/6.27          | ~ (v1_relat_1 @ X0)
% 6.07/6.27          | ~ (v1_funct_1 @ X0)
% 6.07/6.27          | ~ (v2_funct_1 @ X0)
% 6.07/6.27          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 6.07/6.27          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 6.07/6.27      inference('sup+', [status(thm)], ['105', '106'])).
% 6.07/6.27  thf('108', plain,
% 6.07/6.27      (![X0 : $i]:
% 6.07/6.27         (~ (v1_relat_1 @ X0)
% 6.07/6.27          | ~ (v1_funct_1 @ X0)
% 6.07/6.27          | ~ (v2_funct_1 @ X0)
% 6.07/6.27          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.07/6.27          | ~ (v2_funct_1 @ X0)
% 6.07/6.27          | ~ (v1_funct_1 @ X0)
% 6.07/6.27          | ~ (v1_relat_1 @ X0)
% 6.07/6.27          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 6.07/6.27             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 6.07/6.27      inference('sup-', [status(thm)], ['104', '107'])).
% 6.07/6.27  thf('109', plain,
% 6.07/6.27      (![X0 : $i]:
% 6.07/6.27         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 6.07/6.27           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 6.07/6.27          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.07/6.27          | ~ (v2_funct_1 @ X0)
% 6.07/6.27          | ~ (v1_funct_1 @ X0)
% 6.07/6.27          | ~ (v1_relat_1 @ X0))),
% 6.07/6.27      inference('simplify', [status(thm)], ['108'])).
% 6.07/6.27  thf('110', plain,
% 6.07/6.27      (![X0 : $i]:
% 6.07/6.27         (~ (v1_relat_1 @ X0)
% 6.07/6.27          | ~ (v1_funct_1 @ X0)
% 6.07/6.27          | ~ (v2_funct_1 @ X0)
% 6.07/6.27          | ~ (v1_relat_1 @ X0)
% 6.07/6.27          | ~ (v1_funct_1 @ X0)
% 6.07/6.27          | ~ (v2_funct_1 @ X0)
% 6.07/6.27          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 6.07/6.27             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 6.07/6.27      inference('sup-', [status(thm)], ['103', '109'])).
% 6.07/6.27  thf('111', plain,
% 6.07/6.27      (![X0 : $i]:
% 6.07/6.27         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 6.07/6.27           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 6.07/6.27          | ~ (v2_funct_1 @ X0)
% 6.07/6.27          | ~ (v1_funct_1 @ X0)
% 6.07/6.27          | ~ (v1_relat_1 @ X0))),
% 6.07/6.27      inference('simplify', [status(thm)], ['110'])).
% 6.07/6.27  thf('112', plain,
% 6.07/6.27      (![X0 : $i]:
% 6.07/6.27         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 6.07/6.27           (k1_relat_1 @ X0))
% 6.07/6.27          | ~ (v1_relat_1 @ X0)
% 6.07/6.27          | ~ (v1_funct_1 @ X0)
% 6.07/6.27          | ~ (v2_funct_1 @ X0)
% 6.07/6.27          | ~ (v1_relat_1 @ X0)
% 6.07/6.27          | ~ (v1_funct_1 @ X0)
% 6.07/6.27          | ~ (v2_funct_1 @ X0))),
% 6.07/6.27      inference('sup+', [status(thm)], ['102', '111'])).
% 6.07/6.27  thf('113', plain,
% 6.07/6.27      (![X0 : $i]:
% 6.07/6.27         (~ (v2_funct_1 @ X0)
% 6.07/6.27          | ~ (v1_funct_1 @ X0)
% 6.07/6.27          | ~ (v1_relat_1 @ X0)
% 6.07/6.27          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 6.07/6.27             (k1_relat_1 @ X0)))),
% 6.07/6.27      inference('simplify', [status(thm)], ['112'])).
% 6.07/6.27  thf('114', plain,
% 6.07/6.27      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_A)
% 6.07/6.27        | ((sk_B) = (k1_xboole_0))
% 6.07/6.27        | ~ (v1_relat_1 @ sk_C)
% 6.07/6.27        | ~ (v1_funct_1 @ sk_C)
% 6.07/6.27        | ~ (v2_funct_1 @ sk_C))),
% 6.07/6.27      inference('sup+', [status(thm)], ['101', '113'])).
% 6.07/6.27  thf('115', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 6.07/6.27      inference('sup+', [status(thm)], ['16', '17'])).
% 6.07/6.27  thf('116', plain, ((v1_relat_1 @ sk_C)),
% 6.07/6.27      inference('sup-', [status(thm)], ['32', '33'])).
% 6.07/6.27  thf('117', plain, ((v1_funct_1 @ sk_C)),
% 6.07/6.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.07/6.27  thf('118', plain, ((v2_funct_1 @ sk_C)),
% 6.07/6.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.07/6.27  thf('119', plain,
% 6.07/6.27      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 6.07/6.27        | ((sk_B) = (k1_xboole_0)))),
% 6.07/6.27      inference('demod', [status(thm)], ['114', '115', '116', '117', '118'])).
% 6.07/6.27  thf('120', plain,
% 6.07/6.27      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 6.07/6.27         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 6.07/6.27      inference('split', [status(esa)], ['89'])).
% 6.07/6.27  thf('121', plain,
% 6.07/6.27      ((((sk_B) = (k1_xboole_0)))
% 6.07/6.27         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 6.07/6.27      inference('sup-', [status(thm)], ['119', '120'])).
% 6.07/6.27  thf('122', plain,
% 6.07/6.27      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ k1_xboole_0 @ sk_A))
% 6.07/6.27         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 6.07/6.27      inference('demod', [status(thm)], ['100', '121'])).
% 6.07/6.27  thf('123', plain,
% 6.07/6.27      ((((sk_B) = (k1_xboole_0)))
% 6.07/6.27         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 6.07/6.27      inference('sup-', [status(thm)], ['119', '120'])).
% 6.07/6.27  thf('124', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 6.07/6.27      inference('demod', [status(thm)], ['5', '8'])).
% 6.07/6.27  thf('125', plain,
% 6.07/6.27      (![X6 : $i]:
% 6.07/6.27         ((v1_funct_1 @ (k2_funct_1 @ X6))
% 6.07/6.27          | ~ (v2_funct_1 @ X6)
% 6.07/6.27          | ~ (v1_funct_1 @ X6)
% 6.07/6.27          | ~ (v1_relat_1 @ X6))),
% 6.07/6.27      inference('cnf', [status(esa)], [fc6_funct_1])).
% 6.07/6.27  thf('126', plain,
% 6.07/6.27      (![X6 : $i]:
% 6.07/6.27         ((v2_funct_1 @ (k2_funct_1 @ X6))
% 6.07/6.27          | ~ (v2_funct_1 @ X6)
% 6.07/6.27          | ~ (v1_funct_1 @ X6)
% 6.07/6.27          | ~ (v1_relat_1 @ X6))),
% 6.07/6.27      inference('cnf', [status(esa)], [fc6_funct_1])).
% 6.07/6.27  thf('127', plain,
% 6.07/6.27      (![X6 : $i]:
% 6.07/6.27         ((v1_funct_1 @ (k2_funct_1 @ X6))
% 6.07/6.27          | ~ (v2_funct_1 @ X6)
% 6.07/6.27          | ~ (v1_funct_1 @ X6)
% 6.07/6.27          | ~ (v1_relat_1 @ X6))),
% 6.07/6.27      inference('cnf', [status(esa)], [fc6_funct_1])).
% 6.07/6.27  thf('128', plain,
% 6.07/6.27      (![X7 : $i]:
% 6.07/6.27         (~ (v2_funct_1 @ X7)
% 6.07/6.27          | ((k2_relat_1 @ X7) = (k1_relat_1 @ (k2_funct_1 @ X7)))
% 6.07/6.27          | ~ (v1_funct_1 @ X7)
% 6.07/6.27          | ~ (v1_relat_1 @ X7))),
% 6.07/6.27      inference('cnf', [status(esa)], [t55_funct_1])).
% 6.07/6.27  thf('129', plain,
% 6.07/6.27      (![X6 : $i]:
% 6.07/6.27         ((v1_funct_1 @ (k2_funct_1 @ X6))
% 6.07/6.27          | ~ (v2_funct_1 @ X6)
% 6.07/6.27          | ~ (v1_funct_1 @ X6)
% 6.07/6.27          | ~ (v1_relat_1 @ X6))),
% 6.07/6.27      inference('cnf', [status(esa)], [fc6_funct_1])).
% 6.07/6.27  thf('130', plain,
% 6.07/6.27      (![X6 : $i]:
% 6.07/6.27         ((v2_funct_1 @ (k2_funct_1 @ X6))
% 6.07/6.27          | ~ (v2_funct_1 @ X6)
% 6.07/6.27          | ~ (v1_funct_1 @ X6)
% 6.07/6.27          | ~ (v1_relat_1 @ X6))),
% 6.07/6.27      inference('cnf', [status(esa)], [fc6_funct_1])).
% 6.07/6.27  thf('131', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 6.07/6.27      inference('sup-', [status(thm)], ['37', '38'])).
% 6.07/6.27  thf('132', plain,
% 6.07/6.27      (![X7 : $i]:
% 6.07/6.27         (~ (v2_funct_1 @ X7)
% 6.07/6.27          | ((k1_relat_1 @ X7) = (k2_relat_1 @ (k2_funct_1 @ X7)))
% 6.07/6.27          | ~ (v1_funct_1 @ X7)
% 6.07/6.27          | ~ (v1_relat_1 @ X7))),
% 6.07/6.27      inference('cnf', [status(esa)], [t55_funct_1])).
% 6.07/6.27  thf('133', plain,
% 6.07/6.27      (![X7 : $i]:
% 6.07/6.27         (~ (v2_funct_1 @ X7)
% 6.07/6.27          | ((k2_relat_1 @ X7) = (k1_relat_1 @ (k2_funct_1 @ X7)))
% 6.07/6.27          | ~ (v1_funct_1 @ X7)
% 6.07/6.27          | ~ (v1_relat_1 @ X7))),
% 6.07/6.27      inference('cnf', [status(esa)], [t55_funct_1])).
% 6.07/6.27  thf('134', plain,
% 6.07/6.27      (![X6 : $i]:
% 6.07/6.27         ((v1_relat_1 @ (k2_funct_1 @ X6))
% 6.07/6.27          | ~ (v2_funct_1 @ X6)
% 6.07/6.27          | ~ (v1_funct_1 @ X6)
% 6.07/6.27          | ~ (v1_relat_1 @ X6))),
% 6.07/6.27      inference('cnf', [status(esa)], [fc6_funct_1])).
% 6.07/6.27  thf('135', plain,
% 6.07/6.27      (![X6 : $i]:
% 6.07/6.27         ((v1_funct_1 @ (k2_funct_1 @ X6))
% 6.07/6.27          | ~ (v2_funct_1 @ X6)
% 6.07/6.27          | ~ (v1_funct_1 @ X6)
% 6.07/6.27          | ~ (v1_relat_1 @ X6))),
% 6.07/6.27      inference('cnf', [status(esa)], [fc6_funct_1])).
% 6.07/6.27  thf('136', plain,
% 6.07/6.27      (![X6 : $i]:
% 6.07/6.27         ((v2_funct_1 @ (k2_funct_1 @ X6))
% 6.07/6.27          | ~ (v2_funct_1 @ X6)
% 6.07/6.27          | ~ (v1_funct_1 @ X6)
% 6.07/6.27          | ~ (v1_relat_1 @ X6))),
% 6.07/6.27      inference('cnf', [status(esa)], [fc6_funct_1])).
% 6.07/6.27  thf('137', plain,
% 6.07/6.27      (![X7 : $i]:
% 6.07/6.27         (~ (v2_funct_1 @ X7)
% 6.07/6.27          | ((k1_relat_1 @ X7) = (k2_relat_1 @ (k2_funct_1 @ X7)))
% 6.07/6.27          | ~ (v1_funct_1 @ X7)
% 6.07/6.27          | ~ (v1_relat_1 @ X7))),
% 6.07/6.27      inference('cnf', [status(esa)], [t55_funct_1])).
% 6.07/6.27  thf('138', plain,
% 6.07/6.27      (![X0 : $i]:
% 6.07/6.27         (~ (v1_relat_1 @ X0)
% 6.07/6.27          | ~ (v1_funct_1 @ X0)
% 6.07/6.27          | ~ (v2_funct_1 @ X0)
% 6.07/6.27          | (m1_subset_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ 
% 6.07/6.27             (k1_zfmisc_1 @ (k2_relat_1 @ X0))))),
% 6.07/6.27      inference('simplify', [status(thm)], ['52'])).
% 6.07/6.27  thf('139', plain,
% 6.07/6.27      (![X0 : $i]:
% 6.07/6.27         ((m1_subset_1 @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 6.07/6.27           (k1_zfmisc_1 @ (k1_relat_1 @ X0)))
% 6.07/6.27          | ~ (v1_relat_1 @ X0)
% 6.07/6.27          | ~ (v1_funct_1 @ X0)
% 6.07/6.27          | ~ (v2_funct_1 @ X0)
% 6.07/6.27          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 6.07/6.27          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.07/6.27          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 6.07/6.27      inference('sup+', [status(thm)], ['137', '138'])).
% 6.07/6.27  thf('140', plain,
% 6.07/6.27      (![X0 : $i]:
% 6.07/6.27         (~ (v1_relat_1 @ X0)
% 6.07/6.27          | ~ (v1_funct_1 @ X0)
% 6.07/6.27          | ~ (v2_funct_1 @ X0)
% 6.07/6.27          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 6.07/6.27          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.07/6.27          | ~ (v2_funct_1 @ X0)
% 6.07/6.27          | ~ (v1_funct_1 @ X0)
% 6.07/6.27          | ~ (v1_relat_1 @ X0)
% 6.07/6.27          | (m1_subset_1 @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 6.07/6.27             (k1_zfmisc_1 @ (k1_relat_1 @ X0))))),
% 6.07/6.27      inference('sup-', [status(thm)], ['136', '139'])).
% 6.07/6.27  thf('141', plain,
% 6.07/6.27      (![X0 : $i]:
% 6.07/6.27         ((m1_subset_1 @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 6.07/6.27           (k1_zfmisc_1 @ (k1_relat_1 @ X0)))
% 6.07/6.27          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.07/6.27          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 6.07/6.27          | ~ (v2_funct_1 @ X0)
% 6.07/6.27          | ~ (v1_funct_1 @ X0)
% 6.07/6.27          | ~ (v1_relat_1 @ X0))),
% 6.07/6.27      inference('simplify', [status(thm)], ['140'])).
% 6.07/6.27  thf('142', plain,
% 6.07/6.27      (![X0 : $i]:
% 6.07/6.28         (~ (v1_relat_1 @ X0)
% 6.07/6.28          | ~ (v1_funct_1 @ X0)
% 6.07/6.28          | ~ (v2_funct_1 @ X0)
% 6.07/6.28          | ~ (v1_relat_1 @ X0)
% 6.07/6.28          | ~ (v1_funct_1 @ X0)
% 6.07/6.28          | ~ (v2_funct_1 @ X0)
% 6.07/6.28          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 6.07/6.28          | (m1_subset_1 @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 6.07/6.28             (k1_zfmisc_1 @ (k1_relat_1 @ X0))))),
% 6.07/6.28      inference('sup-', [status(thm)], ['135', '141'])).
% 6.07/6.28  thf('143', plain,
% 6.07/6.28      (![X0 : $i]:
% 6.07/6.28         ((m1_subset_1 @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 6.07/6.28           (k1_zfmisc_1 @ (k1_relat_1 @ X0)))
% 6.07/6.28          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 6.07/6.28          | ~ (v2_funct_1 @ X0)
% 6.07/6.28          | ~ (v1_funct_1 @ X0)
% 6.07/6.28          | ~ (v1_relat_1 @ X0))),
% 6.07/6.28      inference('simplify', [status(thm)], ['142'])).
% 6.07/6.28  thf('144', plain,
% 6.07/6.28      (![X0 : $i]:
% 6.07/6.28         (~ (v1_relat_1 @ X0)
% 6.07/6.28          | ~ (v1_funct_1 @ X0)
% 6.07/6.28          | ~ (v2_funct_1 @ X0)
% 6.07/6.28          | ~ (v1_relat_1 @ X0)
% 6.07/6.28          | ~ (v1_funct_1 @ X0)
% 6.07/6.28          | ~ (v2_funct_1 @ X0)
% 6.07/6.28          | (m1_subset_1 @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 6.07/6.28             (k1_zfmisc_1 @ (k1_relat_1 @ X0))))),
% 6.07/6.28      inference('sup-', [status(thm)], ['134', '143'])).
% 6.07/6.28  thf('145', plain,
% 6.07/6.28      (![X0 : $i]:
% 6.07/6.28         ((m1_subset_1 @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 6.07/6.28           (k1_zfmisc_1 @ (k1_relat_1 @ X0)))
% 6.07/6.28          | ~ (v2_funct_1 @ X0)
% 6.07/6.28          | ~ (v1_funct_1 @ X0)
% 6.07/6.28          | ~ (v1_relat_1 @ X0))),
% 6.07/6.28      inference('simplify', [status(thm)], ['144'])).
% 6.07/6.28  thf('146', plain,
% 6.07/6.28      (![X3 : $i, X4 : $i]:
% 6.07/6.28         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 6.07/6.28      inference('cnf', [status(esa)], [t3_subset])).
% 6.07/6.28  thf('147', plain,
% 6.07/6.28      (![X0 : $i]:
% 6.07/6.28         (~ (v1_relat_1 @ X0)
% 6.07/6.28          | ~ (v1_funct_1 @ X0)
% 6.07/6.28          | ~ (v2_funct_1 @ X0)
% 6.07/6.28          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 6.07/6.28             (k1_relat_1 @ X0)))),
% 6.07/6.28      inference('sup-', [status(thm)], ['145', '146'])).
% 6.07/6.28  thf('148', plain,
% 6.07/6.28      (![X0 : $i, X2 : $i]:
% 6.07/6.28         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 6.07/6.28      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.07/6.28  thf('149', plain,
% 6.07/6.28      (![X0 : $i]:
% 6.07/6.28         (~ (v2_funct_1 @ X0)
% 6.07/6.28          | ~ (v1_funct_1 @ X0)
% 6.07/6.28          | ~ (v1_relat_1 @ X0)
% 6.07/6.28          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ 
% 6.07/6.28               (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 6.07/6.28          | ((k1_relat_1 @ X0)
% 6.07/6.28              = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 6.07/6.28      inference('sup-', [status(thm)], ['147', '148'])).
% 6.07/6.28  thf('150', plain,
% 6.07/6.28      (![X0 : $i]:
% 6.07/6.28         (~ (r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 6.07/6.28          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 6.07/6.28          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.07/6.28          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 6.07/6.28          | ((k1_relat_1 @ X0)
% 6.07/6.28              = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 6.07/6.28          | ~ (v1_relat_1 @ X0)
% 6.07/6.28          | ~ (v1_funct_1 @ X0)
% 6.07/6.28          | ~ (v2_funct_1 @ X0))),
% 6.07/6.28      inference('sup-', [status(thm)], ['133', '149'])).
% 6.07/6.28  thf('151', plain,
% 6.07/6.28      (![X0 : $i]:
% 6.07/6.28         (~ (r1_tarski @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 6.07/6.28          | ~ (v1_relat_1 @ X0)
% 6.07/6.28          | ~ (v1_funct_1 @ X0)
% 6.07/6.28          | ~ (v2_funct_1 @ X0)
% 6.07/6.28          | ~ (v2_funct_1 @ X0)
% 6.07/6.28          | ~ (v1_funct_1 @ X0)
% 6.07/6.28          | ~ (v1_relat_1 @ X0)
% 6.07/6.28          | ((k1_relat_1 @ X0)
% 6.07/6.28              = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 6.07/6.28          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 6.07/6.28          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.07/6.28          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 6.07/6.28      inference('sup-', [status(thm)], ['132', '150'])).
% 6.07/6.28  thf('152', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 6.07/6.28      inference('simplify', [status(thm)], ['65'])).
% 6.07/6.28  thf('153', plain,
% 6.07/6.28      (![X0 : $i]:
% 6.07/6.28         (~ (v1_relat_1 @ X0)
% 6.07/6.28          | ~ (v1_funct_1 @ X0)
% 6.07/6.28          | ~ (v2_funct_1 @ X0)
% 6.07/6.28          | ~ (v2_funct_1 @ X0)
% 6.07/6.28          | ~ (v1_funct_1 @ X0)
% 6.07/6.28          | ~ (v1_relat_1 @ X0)
% 6.07/6.28          | ((k1_relat_1 @ X0)
% 6.07/6.28              = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 6.07/6.28          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 6.07/6.28          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.07/6.28          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 6.07/6.28      inference('demod', [status(thm)], ['151', '152'])).
% 6.07/6.28  thf('154', plain,
% 6.07/6.28      (![X0 : $i]:
% 6.07/6.28         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 6.07/6.28          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.07/6.28          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 6.07/6.28          | ((k1_relat_1 @ X0)
% 6.07/6.28              = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 6.07/6.28          | ~ (v2_funct_1 @ X0)
% 6.07/6.28          | ~ (v1_funct_1 @ X0)
% 6.07/6.28          | ~ (v1_relat_1 @ X0))),
% 6.07/6.28      inference('simplify', [status(thm)], ['153'])).
% 6.07/6.28  thf('155', plain,
% 6.07/6.28      ((~ (v1_relat_1 @ sk_C)
% 6.07/6.28        | ~ (v1_funct_1 @ sk_C)
% 6.07/6.28        | ~ (v2_funct_1 @ sk_C)
% 6.07/6.28        | ((k1_relat_1 @ sk_C)
% 6.07/6.28            = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 6.07/6.28        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 6.07/6.28        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 6.07/6.28      inference('sup-', [status(thm)], ['131', '154'])).
% 6.07/6.28  thf('156', plain, ((v1_relat_1 @ sk_C)),
% 6.07/6.28      inference('sup-', [status(thm)], ['32', '33'])).
% 6.07/6.28  thf('157', plain, ((v1_funct_1 @ sk_C)),
% 6.07/6.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.07/6.28  thf('158', plain, ((v2_funct_1 @ sk_C)),
% 6.07/6.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.07/6.28  thf('159', plain,
% 6.07/6.28      ((((k1_relat_1 @ sk_C)
% 6.07/6.28          = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 6.07/6.28        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 6.07/6.28        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 6.07/6.28      inference('demod', [status(thm)], ['155', '156', '157', '158'])).
% 6.07/6.28  thf('160', plain,
% 6.07/6.28      ((~ (v1_relat_1 @ sk_C)
% 6.07/6.28        | ~ (v1_funct_1 @ sk_C)
% 6.07/6.28        | ~ (v2_funct_1 @ sk_C)
% 6.07/6.28        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 6.07/6.28        | ((k1_relat_1 @ sk_C)
% 6.07/6.28            = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 6.07/6.28      inference('sup-', [status(thm)], ['130', '159'])).
% 6.07/6.28  thf('161', plain, ((v1_relat_1 @ sk_C)),
% 6.07/6.28      inference('sup-', [status(thm)], ['32', '33'])).
% 6.07/6.28  thf('162', plain, ((v1_funct_1 @ sk_C)),
% 6.07/6.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.07/6.28  thf('163', plain, ((v2_funct_1 @ sk_C)),
% 6.07/6.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.07/6.28  thf('164', plain,
% 6.07/6.28      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 6.07/6.28        | ((k1_relat_1 @ sk_C)
% 6.07/6.28            = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 6.07/6.28      inference('demod', [status(thm)], ['160', '161', '162', '163'])).
% 6.07/6.28  thf('165', plain,
% 6.07/6.28      ((~ (v1_relat_1 @ sk_C)
% 6.07/6.28        | ~ (v1_funct_1 @ sk_C)
% 6.07/6.28        | ~ (v2_funct_1 @ sk_C)
% 6.07/6.28        | ((k1_relat_1 @ sk_C)
% 6.07/6.28            = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 6.07/6.28      inference('sup-', [status(thm)], ['129', '164'])).
% 6.07/6.28  thf('166', plain, ((v1_relat_1 @ sk_C)),
% 6.07/6.28      inference('sup-', [status(thm)], ['32', '33'])).
% 6.07/6.28  thf('167', plain, ((v1_funct_1 @ sk_C)),
% 6.07/6.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.07/6.28  thf('168', plain, ((v2_funct_1 @ sk_C)),
% 6.07/6.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.07/6.28  thf('169', plain,
% 6.07/6.28      (((k1_relat_1 @ sk_C) = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 6.07/6.28      inference('demod', [status(thm)], ['165', '166', '167', '168'])).
% 6.07/6.28  thf('170', plain,
% 6.07/6.28      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 6.07/6.28        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 6.07/6.28        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 6.07/6.28        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 6.07/6.28      inference('sup+', [status(thm)], ['128', '169'])).
% 6.07/6.28  thf('171', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 6.07/6.28      inference('sup-', [status(thm)], ['37', '38'])).
% 6.07/6.28  thf('172', plain,
% 6.07/6.28      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 6.07/6.28        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 6.07/6.28        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 6.07/6.28      inference('demod', [status(thm)], ['170', '171'])).
% 6.07/6.28  thf('173', plain,
% 6.07/6.28      ((~ (v1_relat_1 @ sk_C)
% 6.07/6.28        | ~ (v1_funct_1 @ sk_C)
% 6.07/6.28        | ~ (v2_funct_1 @ sk_C)
% 6.07/6.28        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 6.07/6.28        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 6.07/6.28      inference('sup-', [status(thm)], ['127', '172'])).
% 6.07/6.28  thf('174', plain, ((v1_relat_1 @ sk_C)),
% 6.07/6.28      inference('sup-', [status(thm)], ['32', '33'])).
% 6.07/6.28  thf('175', plain, ((v1_funct_1 @ sk_C)),
% 6.07/6.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.07/6.28  thf('176', plain, ((v2_funct_1 @ sk_C)),
% 6.07/6.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.07/6.28  thf('177', plain,
% 6.07/6.28      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 6.07/6.28        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 6.07/6.28      inference('demod', [status(thm)], ['173', '174', '175', '176'])).
% 6.07/6.28  thf('178', plain,
% 6.07/6.28      ((~ (v1_relat_1 @ sk_C)
% 6.07/6.28        | ~ (v1_funct_1 @ sk_C)
% 6.07/6.28        | ~ (v2_funct_1 @ sk_C)
% 6.07/6.28        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 6.07/6.28      inference('sup-', [status(thm)], ['126', '177'])).
% 6.07/6.28  thf('179', plain, ((v1_relat_1 @ sk_C)),
% 6.07/6.28      inference('sup-', [status(thm)], ['32', '33'])).
% 6.07/6.28  thf('180', plain, ((v1_funct_1 @ sk_C)),
% 6.07/6.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.07/6.28  thf('181', plain, ((v2_funct_1 @ sk_C)),
% 6.07/6.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.07/6.28  thf('182', plain,
% 6.07/6.28      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 6.07/6.28      inference('demod', [status(thm)], ['178', '179', '180', '181'])).
% 6.07/6.28  thf('183', plain,
% 6.07/6.28      (![X29 : $i, X30 : $i]:
% 6.07/6.28         (~ (r1_tarski @ (k2_relat_1 @ X29) @ X30)
% 6.07/6.28          | (v1_funct_2 @ X29 @ (k1_relat_1 @ X29) @ X30)
% 6.07/6.28          | ~ (v1_funct_1 @ X29)
% 6.07/6.28          | ~ (v1_relat_1 @ X29))),
% 6.07/6.28      inference('cnf', [status(esa)], [t4_funct_2])).
% 6.07/6.28  thf('184', plain,
% 6.07/6.28      (![X0 : $i]:
% 6.07/6.28         (~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0)
% 6.07/6.28          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 6.07/6.28          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 6.07/6.28          | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 6.07/6.28             (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0))),
% 6.07/6.28      inference('sup-', [status(thm)], ['182', '183'])).
% 6.07/6.28  thf('185', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 6.07/6.28      inference('sup-', [status(thm)], ['37', '38'])).
% 6.07/6.28  thf('186', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 6.07/6.28      inference('demod', [status(thm)], ['63', '64', '66', '67', '68', '69'])).
% 6.07/6.28  thf('187', plain,
% 6.07/6.28      (![X0 : $i]:
% 6.07/6.28         (~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0)
% 6.07/6.28          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 6.07/6.28          | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ X0))),
% 6.07/6.28      inference('demod', [status(thm)], ['184', '185', '186'])).
% 6.07/6.28  thf('188', plain,
% 6.07/6.28      (![X0 : $i]:
% 6.07/6.28         (~ (v1_relat_1 @ sk_C)
% 6.07/6.28          | ~ (v1_funct_1 @ sk_C)
% 6.07/6.28          | ~ (v2_funct_1 @ sk_C)
% 6.07/6.28          | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ X0)
% 6.07/6.28          | ~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0))),
% 6.07/6.28      inference('sup-', [status(thm)], ['125', '187'])).
% 6.07/6.28  thf('189', plain, ((v1_relat_1 @ sk_C)),
% 6.07/6.28      inference('sup-', [status(thm)], ['32', '33'])).
% 6.07/6.28  thf('190', plain, ((v1_funct_1 @ sk_C)),
% 6.07/6.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.07/6.28  thf('191', plain, ((v2_funct_1 @ sk_C)),
% 6.07/6.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.07/6.28  thf('192', plain,
% 6.07/6.28      (![X0 : $i]:
% 6.07/6.28         ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ X0)
% 6.07/6.28          | ~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0))),
% 6.07/6.28      inference('demod', [status(thm)], ['188', '189', '190', '191'])).
% 6.07/6.28  thf('193', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)),
% 6.07/6.28      inference('sup-', [status(thm)], ['124', '192'])).
% 6.07/6.28  thf('194', plain,
% 6.07/6.28      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ k1_xboole_0 @ sk_A))
% 6.07/6.28         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 6.07/6.28      inference('sup+', [status(thm)], ['123', '193'])).
% 6.07/6.28  thf('195', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 6.07/6.28      inference('demod', [status(thm)], ['122', '194'])).
% 6.07/6.28  thf('196', plain,
% 6.07/6.28      (~
% 6.07/6.28       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.07/6.28         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 6.07/6.28       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 6.07/6.28       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 6.07/6.28      inference('split', [status(esa)], ['89'])).
% 6.07/6.28  thf('197', plain,
% 6.07/6.28      (~
% 6.07/6.28       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.07/6.28         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 6.07/6.28      inference('sat_resolution*', [status(thm)], ['99', '195', '196'])).
% 6.07/6.28  thf('198', plain, (((sk_B) = (k1_xboole_0))),
% 6.07/6.28      inference('simpl_trail', [status(thm)], ['91', '197'])).
% 6.07/6.28  thf('199', plain, (((k1_xboole_0) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 6.07/6.28      inference('demod', [status(thm)], ['70', '198'])).
% 6.07/6.28  thf('200', plain,
% 6.07/6.28      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.07/6.28         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_A)))
% 6.07/6.28        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 6.07/6.28      inference('demod', [status(thm)], ['43', '199'])).
% 6.07/6.28  thf('201', plain,
% 6.07/6.28      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.07/6.28           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 6.07/6.28         <= (~
% 6.07/6.28             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.07/6.28               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 6.07/6.28      inference('split', [status(esa)], ['89'])).
% 6.07/6.28  thf('202', plain,
% 6.07/6.28      ((((sk_B) = (k1_xboole_0)))
% 6.07/6.28         <= (~
% 6.07/6.28             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.07/6.28               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 6.07/6.28      inference('sup-', [status(thm)], ['88', '90'])).
% 6.07/6.28  thf('203', plain,
% 6.07/6.28      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.07/6.28           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_A))))
% 6.07/6.28         <= (~
% 6.07/6.28             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.07/6.28               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 6.07/6.28      inference('demod', [status(thm)], ['201', '202'])).
% 6.07/6.28  thf('204', plain,
% 6.07/6.28      (~
% 6.07/6.28       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.07/6.28         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 6.07/6.28      inference('sat_resolution*', [status(thm)], ['99', '195', '196'])).
% 6.07/6.28  thf('205', plain,
% 6.07/6.28      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.07/6.28          (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_A)))),
% 6.07/6.28      inference('simpl_trail', [status(thm)], ['203', '204'])).
% 6.07/6.28  thf('206', plain, (~ (v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 6.07/6.28      inference('clc', [status(thm)], ['200', '205'])).
% 6.07/6.28  thf('207', plain,
% 6.07/6.28      ((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C) | ~ (v2_funct_1 @ sk_C))),
% 6.07/6.28      inference('sup-', [status(thm)], ['0', '206'])).
% 6.07/6.28  thf('208', plain, ((v1_relat_1 @ sk_C)),
% 6.07/6.28      inference('sup-', [status(thm)], ['32', '33'])).
% 6.07/6.28  thf('209', plain, ((v1_funct_1 @ sk_C)),
% 6.07/6.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.07/6.28  thf('210', plain, ((v2_funct_1 @ sk_C)),
% 6.07/6.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.07/6.28  thf('211', plain, ($false),
% 6.07/6.28      inference('demod', [status(thm)], ['207', '208', '209', '210'])).
% 6.07/6.28  
% 6.07/6.28  % SZS output end Refutation
% 6.07/6.28  
% 6.07/6.28  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
