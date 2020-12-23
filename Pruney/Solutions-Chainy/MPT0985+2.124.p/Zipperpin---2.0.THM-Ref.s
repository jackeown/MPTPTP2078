%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.omFvaR6u1l

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:44 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 805 expanded)
%              Number of leaves         :   29 ( 251 expanded)
%              Depth                    :   31
%              Number of atoms          : 1195 (11349 expanded)
%              Number of equality atoms :   44 ( 434 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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

thf('0',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('4',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X12: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('7',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,(
    ! [X12: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('15',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_xboole_0 @ X3 @ X4 )
        = X3 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('16',plain,
    ( ( k3_xboole_0 @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    = sk_C ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('18',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('19',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t96_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ A @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf('22',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k7_relat_1 @ X10 @ X11 )
        = ( k3_xboole_0 @ X10 @ ( k2_zfmisc_1 @ X11 @ ( k2_relat_1 @ X10 ) ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t96_relat_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ sk_C @ X0 )
        = ( k3_xboole_0 @ sk_C @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_C @ X0 )
      = ( k3_xboole_0 @ sk_C @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k7_relat_1 @ sk_C @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['16','25'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('27',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X8 @ X9 ) ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('28',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('30',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['28','29'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('31',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k1_relat_1 @ X13 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('32',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X23 ) @ X24 )
      | ( v1_funct_2 @ X23 @ ( k1_relat_1 @ X23 ) @ X24 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_relat_1 @ X13 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('36',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['19','20'])).

thf('37',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('38',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('39',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_relat_1 @ X13 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('40',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k7_relat_1 @ X10 @ X11 )
        = ( k3_xboole_0 @ X10 @ ( k2_zfmisc_1 @ X11 @ ( k2_relat_1 @ X10 ) ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t96_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('42',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['41'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('44',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X20 ) @ X21 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X20 ) @ X22 )
      | ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_xboole_0 @ X3 @ X4 )
        = X3 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X8 @ X9 ) ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('57',plain,(
    ! [X5: $i,X7: $i] :
      ( ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( m1_subset_1 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['37','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['36','63'])).

thf('65',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('68',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['64','65','66','67'])).

thf('69',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('70',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['35','70'])).

thf('72',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['19','20'])).

thf('73',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('74',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('75',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['71','72','73','74','75','76'])).

thf('78',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('79',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['71','72','73','74','75','76'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('81',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('84',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('87',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('91',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['34','77','87','88','89','90'])).

thf('92',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['11','91'])).

thf('93',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('94',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('96',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('97',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('99',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','97','98'])).

thf('100',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','99'])).

thf('101',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['28','29'])).

thf('102',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k1_relat_1 @ X13 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('103',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['19','20'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('105',plain,
    ( ( ( k7_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('107',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( k7_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['105','106','107','108'])).

thf('110',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X8 @ X9 ) ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('111',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X20 ) @ X21 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X20 ) @ X22 )
      | ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 )
      | ( m1_subset_1 @ ( k7_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['109','112'])).

thf('114',plain,
    ( ( k7_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['105','106','107','108'])).

thf('115',plain,
    ( ( k7_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['105','106','107','108'])).

thf('116',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('117',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['113','114','115','116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C )
      | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['102','118'])).

thf('120',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('121',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['119','120','121','122'])).

thf('124',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['101','123'])).

thf('125',plain,(
    $false ),
    inference(demod,[status(thm)],['100','124'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.omFvaR6u1l
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:39:18 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.39/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.62  % Solved by: fo/fo7.sh
% 0.39/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.62  % done 195 iterations in 0.148s
% 0.39/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.62  % SZS output start Refutation
% 0.39/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.62  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.39/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.62  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.39/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.62  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.39/0.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.39/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.39/0.62  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.39/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.62  thf(t31_funct_2, conjecture,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.39/0.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.62       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.39/0.62         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.39/0.62           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.39/0.62           ( m1_subset_1 @
% 0.39/0.62             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.39/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.62    (~( ![A:$i,B:$i,C:$i]:
% 0.39/0.62        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.39/0.62            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.62          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.39/0.62            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.39/0.62              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.39/0.62              ( m1_subset_1 @
% 0.39/0.62                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 0.39/0.62    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 0.39/0.62  thf('0', plain,
% 0.39/0.62      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.62        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.39/0.62        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.39/0.62             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('1', plain,
% 0.39/0.62      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.39/0.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 0.39/0.62         <= (~
% 0.39/0.62             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.39/0.62               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.39/0.62      inference('split', [status(esa)], ['0'])).
% 0.39/0.62  thf('2', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(cc1_relset_1, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.62       ( v1_relat_1 @ C ) ))).
% 0.39/0.62  thf('3', plain,
% 0.39/0.62      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.39/0.62         ((v1_relat_1 @ X14)
% 0.39/0.62          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.39/0.62      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.39/0.62  thf('4', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.62      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.62  thf(dt_k2_funct_1, axiom,
% 0.39/0.62    (![A:$i]:
% 0.39/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.39/0.62       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.39/0.62         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.39/0.62  thf('5', plain,
% 0.39/0.62      (![X12 : $i]:
% 0.39/0.62         ((v1_funct_1 @ (k2_funct_1 @ X12))
% 0.39/0.62          | ~ (v1_funct_1 @ X12)
% 0.39/0.62          | ~ (v1_relat_1 @ X12))),
% 0.39/0.62      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.39/0.62  thf('6', plain,
% 0.39/0.62      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.39/0.62         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.39/0.62      inference('split', [status(esa)], ['0'])).
% 0.39/0.62  thf('7', plain,
% 0.39/0.62      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 0.39/0.62         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.39/0.62      inference('sup-', [status(thm)], ['5', '6'])).
% 0.39/0.62  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('9', plain,
% 0.39/0.62      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.39/0.62      inference('demod', [status(thm)], ['7', '8'])).
% 0.39/0.62  thf('10', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['4', '9'])).
% 0.39/0.62  thf('11', plain,
% 0.39/0.62      (![X12 : $i]:
% 0.39/0.62         ((v1_funct_1 @ (k2_funct_1 @ X12))
% 0.39/0.62          | ~ (v1_funct_1 @ X12)
% 0.39/0.62          | ~ (v1_relat_1 @ X12))),
% 0.39/0.62      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.39/0.62  thf('12', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(t3_subset, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.39/0.62  thf('13', plain,
% 0.39/0.62      (![X5 : $i, X6 : $i]:
% 0.39/0.62         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.62  thf('14', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.39/0.62      inference('sup-', [status(thm)], ['12', '13'])).
% 0.39/0.62  thf(t28_xboole_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.39/0.62  thf('15', plain,
% 0.39/0.62      (![X3 : $i, X4 : $i]:
% 0.39/0.62         (((k3_xboole_0 @ X3 @ X4) = (X3)) | ~ (r1_tarski @ X3 @ X4))),
% 0.39/0.62      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.39/0.62  thf('16', plain,
% 0.39/0.62      (((k3_xboole_0 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B)) = (sk_C))),
% 0.39/0.62      inference('sup-', [status(thm)], ['14', '15'])).
% 0.39/0.62  thf('17', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(redefinition_k2_relset_1, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.62       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.39/0.62  thf('18', plain,
% 0.39/0.62      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.39/0.62         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 0.39/0.62          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.39/0.62      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.39/0.62  thf('19', plain,
% 0.39/0.62      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.39/0.62      inference('sup-', [status(thm)], ['17', '18'])).
% 0.39/0.62  thf('20', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('21', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.39/0.62      inference('sup+', [status(thm)], ['19', '20'])).
% 0.39/0.62  thf(t96_relat_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( v1_relat_1 @ B ) =>
% 0.39/0.62       ( ( k7_relat_1 @ B @ A ) =
% 0.39/0.62         ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ A @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.39/0.62  thf('22', plain,
% 0.39/0.62      (![X10 : $i, X11 : $i]:
% 0.39/0.62         (((k7_relat_1 @ X10 @ X11)
% 0.39/0.62            = (k3_xboole_0 @ X10 @ (k2_zfmisc_1 @ X11 @ (k2_relat_1 @ X10))))
% 0.39/0.62          | ~ (v1_relat_1 @ X10))),
% 0.39/0.62      inference('cnf', [status(esa)], [t96_relat_1])).
% 0.39/0.62  thf('23', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (((k7_relat_1 @ sk_C @ X0)
% 0.39/0.62            = (k3_xboole_0 @ sk_C @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.39/0.62          | ~ (v1_relat_1 @ sk_C))),
% 0.39/0.62      inference('sup+', [status(thm)], ['21', '22'])).
% 0.39/0.62  thf('24', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.62      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.62  thf('25', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         ((k7_relat_1 @ sk_C @ X0)
% 0.39/0.62           = (k3_xboole_0 @ sk_C @ (k2_zfmisc_1 @ X0 @ sk_B)))),
% 0.39/0.62      inference('demod', [status(thm)], ['23', '24'])).
% 0.39/0.62  thf('26', plain, (((k7_relat_1 @ sk_C @ sk_A) = (sk_C))),
% 0.39/0.62      inference('demod', [status(thm)], ['16', '25'])).
% 0.39/0.62  thf(t87_relat_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( v1_relat_1 @ B ) =>
% 0.39/0.62       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.39/0.62  thf('27', plain,
% 0.39/0.62      (![X8 : $i, X9 : $i]:
% 0.39/0.62         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X8 @ X9)) @ X9)
% 0.39/0.62          | ~ (v1_relat_1 @ X8))),
% 0.39/0.62      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.39/0.62  thf('28', plain,
% 0.39/0.62      (((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A) | ~ (v1_relat_1 @ sk_C))),
% 0.39/0.62      inference('sup+', [status(thm)], ['26', '27'])).
% 0.39/0.62  thf('29', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.62      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.62  thf('30', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.39/0.62      inference('demod', [status(thm)], ['28', '29'])).
% 0.39/0.62  thf(t55_funct_1, axiom,
% 0.39/0.62    (![A:$i]:
% 0.39/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.39/0.62       ( ( v2_funct_1 @ A ) =>
% 0.39/0.62         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.39/0.62           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.39/0.62  thf('31', plain,
% 0.39/0.62      (![X13 : $i]:
% 0.39/0.62         (~ (v2_funct_1 @ X13)
% 0.39/0.62          | ((k1_relat_1 @ X13) = (k2_relat_1 @ (k2_funct_1 @ X13)))
% 0.39/0.62          | ~ (v1_funct_1 @ X13)
% 0.39/0.62          | ~ (v1_relat_1 @ X13))),
% 0.39/0.62      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.39/0.62  thf(t4_funct_2, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.39/0.62       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.39/0.62         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.39/0.62           ( m1_subset_1 @
% 0.39/0.62             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.39/0.62  thf('32', plain,
% 0.39/0.62      (![X23 : $i, X24 : $i]:
% 0.39/0.62         (~ (r1_tarski @ (k2_relat_1 @ X23) @ X24)
% 0.39/0.62          | (v1_funct_2 @ X23 @ (k1_relat_1 @ X23) @ X24)
% 0.39/0.62          | ~ (v1_funct_1 @ X23)
% 0.39/0.62          | ~ (v1_relat_1 @ X23))),
% 0.39/0.62      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.39/0.62  thf('33', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.39/0.62          | ~ (v1_relat_1 @ X0)
% 0.39/0.62          | ~ (v1_funct_1 @ X0)
% 0.39/0.62          | ~ (v2_funct_1 @ X0)
% 0.39/0.62          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.39/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.39/0.62          | (v1_funct_2 @ (k2_funct_1 @ X0) @ 
% 0.39/0.62             (k1_relat_1 @ (k2_funct_1 @ X0)) @ X1))),
% 0.39/0.62      inference('sup-', [status(thm)], ['31', '32'])).
% 0.39/0.62  thf('34', plain,
% 0.39/0.62      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 0.39/0.62         (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)
% 0.39/0.62        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.62        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.62        | ~ (v2_funct_1 @ sk_C)
% 0.39/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.39/0.62        | ~ (v1_relat_1 @ sk_C))),
% 0.39/0.62      inference('sup-', [status(thm)], ['30', '33'])).
% 0.39/0.62  thf('35', plain,
% 0.39/0.62      (![X13 : $i]:
% 0.39/0.62         (~ (v2_funct_1 @ X13)
% 0.39/0.62          | ((k2_relat_1 @ X13) = (k1_relat_1 @ (k2_funct_1 @ X13)))
% 0.39/0.62          | ~ (v1_funct_1 @ X13)
% 0.39/0.62          | ~ (v1_relat_1 @ X13))),
% 0.39/0.62      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.39/0.62  thf('36', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.39/0.62      inference('sup+', [status(thm)], ['19', '20'])).
% 0.39/0.62  thf('37', plain,
% 0.39/0.62      (![X12 : $i]:
% 0.39/0.62         ((v1_relat_1 @ (k2_funct_1 @ X12))
% 0.39/0.62          | ~ (v1_funct_1 @ X12)
% 0.39/0.62          | ~ (v1_relat_1 @ X12))),
% 0.39/0.62      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.39/0.62  thf('38', plain,
% 0.39/0.62      (![X12 : $i]:
% 0.39/0.62         ((v1_relat_1 @ (k2_funct_1 @ X12))
% 0.39/0.62          | ~ (v1_funct_1 @ X12)
% 0.39/0.62          | ~ (v1_relat_1 @ X12))),
% 0.39/0.62      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.39/0.62  thf('39', plain,
% 0.39/0.62      (![X13 : $i]:
% 0.39/0.62         (~ (v2_funct_1 @ X13)
% 0.39/0.62          | ((k2_relat_1 @ X13) = (k1_relat_1 @ (k2_funct_1 @ X13)))
% 0.39/0.62          | ~ (v1_funct_1 @ X13)
% 0.39/0.62          | ~ (v1_relat_1 @ X13))),
% 0.39/0.62      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.39/0.62  thf('40', plain,
% 0.39/0.62      (![X10 : $i, X11 : $i]:
% 0.39/0.62         (((k7_relat_1 @ X10 @ X11)
% 0.39/0.62            = (k3_xboole_0 @ X10 @ (k2_zfmisc_1 @ X11 @ (k2_relat_1 @ X10))))
% 0.39/0.62          | ~ (v1_relat_1 @ X10))),
% 0.39/0.62      inference('cnf', [status(esa)], [t96_relat_1])).
% 0.39/0.62  thf(d10_xboole_0, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.39/0.62  thf('41', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.39/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.62  thf('42', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.39/0.62      inference('simplify', [status(thm)], ['41'])).
% 0.39/0.62  thf('43', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.39/0.62      inference('simplify', [status(thm)], ['41'])).
% 0.39/0.62  thf(t11_relset_1, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( v1_relat_1 @ C ) =>
% 0.39/0.62       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.39/0.62           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.39/0.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.39/0.62  thf('44', plain,
% 0.39/0.62      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.39/0.62         (~ (r1_tarski @ (k1_relat_1 @ X20) @ X21)
% 0.39/0.62          | ~ (r1_tarski @ (k2_relat_1 @ X20) @ X22)
% 0.39/0.62          | (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.39/0.62          | ~ (v1_relat_1 @ X20))),
% 0.39/0.62      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.39/0.62  thf('45', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         (~ (v1_relat_1 @ X0)
% 0.39/0.62          | (m1_subset_1 @ X0 @ 
% 0.39/0.62             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.39/0.62          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.39/0.62      inference('sup-', [status(thm)], ['43', '44'])).
% 0.39/0.62  thf('46', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         ((m1_subset_1 @ X0 @ 
% 0.39/0.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.39/0.62          | ~ (v1_relat_1 @ X0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['42', '45'])).
% 0.39/0.62  thf('47', plain,
% 0.39/0.62      (![X5 : $i, X6 : $i]:
% 0.39/0.62         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.62  thf('48', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (v1_relat_1 @ X0)
% 0.39/0.62          | (r1_tarski @ X0 @ 
% 0.39/0.62             (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 0.39/0.62      inference('sup-', [status(thm)], ['46', '47'])).
% 0.39/0.62  thf('49', plain,
% 0.39/0.62      (![X3 : $i, X4 : $i]:
% 0.39/0.62         (((k3_xboole_0 @ X3 @ X4) = (X3)) | ~ (r1_tarski @ X3 @ X4))),
% 0.39/0.62      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.39/0.62  thf('50', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (v1_relat_1 @ X0)
% 0.39/0.62          | ((k3_xboole_0 @ X0 @ 
% 0.39/0.62              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))) = (
% 0.39/0.62              X0)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['48', '49'])).
% 0.39/0.62  thf('51', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0))
% 0.39/0.62          | ~ (v1_relat_1 @ X0)
% 0.39/0.62          | ~ (v1_relat_1 @ X0))),
% 0.39/0.62      inference('sup+', [status(thm)], ['40', '50'])).
% 0.39/0.62  thf('52', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (v1_relat_1 @ X0) | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0)))),
% 0.39/0.62      inference('simplify', [status(thm)], ['51'])).
% 0.39/0.62  thf('53', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (((k7_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.39/0.62            = (k2_funct_1 @ X0))
% 0.39/0.62          | ~ (v1_relat_1 @ X0)
% 0.39/0.62          | ~ (v1_funct_1 @ X0)
% 0.39/0.62          | ~ (v2_funct_1 @ X0)
% 0.39/0.62          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.39/0.62      inference('sup+', [status(thm)], ['39', '52'])).
% 0.39/0.62  thf('54', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (v1_relat_1 @ X0)
% 0.39/0.62          | ~ (v1_funct_1 @ X0)
% 0.39/0.62          | ~ (v2_funct_1 @ X0)
% 0.39/0.62          | ~ (v1_funct_1 @ X0)
% 0.39/0.62          | ~ (v1_relat_1 @ X0)
% 0.39/0.62          | ((k7_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.39/0.62              = (k2_funct_1 @ X0)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['38', '53'])).
% 0.39/0.62  thf('55', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (((k7_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.39/0.62            = (k2_funct_1 @ X0))
% 0.39/0.62          | ~ (v2_funct_1 @ X0)
% 0.39/0.62          | ~ (v1_funct_1 @ X0)
% 0.39/0.62          | ~ (v1_relat_1 @ X0))),
% 0.39/0.62      inference('simplify', [status(thm)], ['54'])).
% 0.39/0.62  thf('56', plain,
% 0.39/0.62      (![X8 : $i, X9 : $i]:
% 0.39/0.62         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X8 @ X9)) @ X9)
% 0.39/0.62          | ~ (v1_relat_1 @ X8))),
% 0.39/0.62      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.39/0.62  thf('57', plain,
% 0.39/0.62      (![X5 : $i, X7 : $i]:
% 0.39/0.62         ((m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X7)) | ~ (r1_tarski @ X5 @ X7))),
% 0.39/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.62  thf('58', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         (~ (v1_relat_1 @ X1)
% 0.39/0.62          | (m1_subset_1 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ 
% 0.39/0.62             (k1_zfmisc_1 @ X0)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['56', '57'])).
% 0.39/0.62  thf('59', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         ((m1_subset_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ 
% 0.39/0.62           (k1_zfmisc_1 @ (k2_relat_1 @ X0)))
% 0.39/0.62          | ~ (v1_relat_1 @ X0)
% 0.39/0.62          | ~ (v1_funct_1 @ X0)
% 0.39/0.62          | ~ (v2_funct_1 @ X0)
% 0.39/0.62          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.39/0.62      inference('sup+', [status(thm)], ['55', '58'])).
% 0.39/0.62  thf('60', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (v1_relat_1 @ X0)
% 0.39/0.62          | ~ (v1_funct_1 @ X0)
% 0.39/0.62          | ~ (v2_funct_1 @ X0)
% 0.39/0.62          | ~ (v1_funct_1 @ X0)
% 0.39/0.62          | ~ (v1_relat_1 @ X0)
% 0.39/0.62          | (m1_subset_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ 
% 0.39/0.62             (k1_zfmisc_1 @ (k2_relat_1 @ X0))))),
% 0.39/0.62      inference('sup-', [status(thm)], ['37', '59'])).
% 0.39/0.62  thf('61', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         ((m1_subset_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ 
% 0.39/0.62           (k1_zfmisc_1 @ (k2_relat_1 @ X0)))
% 0.39/0.62          | ~ (v2_funct_1 @ X0)
% 0.39/0.62          | ~ (v1_funct_1 @ X0)
% 0.39/0.62          | ~ (v1_relat_1 @ X0))),
% 0.39/0.62      inference('simplify', [status(thm)], ['60'])).
% 0.39/0.62  thf('62', plain,
% 0.39/0.62      (![X5 : $i, X6 : $i]:
% 0.39/0.62         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.62  thf('63', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (v1_relat_1 @ X0)
% 0.39/0.62          | ~ (v1_funct_1 @ X0)
% 0.39/0.62          | ~ (v2_funct_1 @ X0)
% 0.39/0.62          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['61', '62'])).
% 0.39/0.62  thf('64', plain,
% 0.39/0.62      (((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B)
% 0.39/0.62        | ~ (v2_funct_1 @ sk_C)
% 0.39/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.39/0.62        | ~ (v1_relat_1 @ sk_C))),
% 0.39/0.62      inference('sup+', [status(thm)], ['36', '63'])).
% 0.39/0.62  thf('65', plain, ((v2_funct_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('66', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('67', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.62      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.62  thf('68', plain, ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B)),
% 0.39/0.62      inference('demod', [status(thm)], ['64', '65', '66', '67'])).
% 0.39/0.62  thf('69', plain,
% 0.39/0.62      (![X0 : $i, X2 : $i]:
% 0.39/0.62         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.39/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.62  thf('70', plain,
% 0.39/0.62      ((~ (r1_tarski @ sk_B @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.39/0.62        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.39/0.62      inference('sup-', [status(thm)], ['68', '69'])).
% 0.39/0.62  thf('71', plain,
% 0.39/0.62      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C))
% 0.39/0.62        | ~ (v1_relat_1 @ sk_C)
% 0.39/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.39/0.62        | ~ (v2_funct_1 @ sk_C)
% 0.39/0.62        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.39/0.62      inference('sup-', [status(thm)], ['35', '70'])).
% 0.39/0.62  thf('72', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.39/0.62      inference('sup+', [status(thm)], ['19', '20'])).
% 0.39/0.62  thf('73', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.39/0.62      inference('simplify', [status(thm)], ['41'])).
% 0.39/0.62  thf('74', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.62      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.62  thf('75', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('76', plain, ((v2_funct_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('77', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.39/0.62      inference('demod', [status(thm)], ['71', '72', '73', '74', '75', '76'])).
% 0.39/0.62  thf('78', plain,
% 0.39/0.62      (![X12 : $i]:
% 0.39/0.62         ((v1_relat_1 @ (k2_funct_1 @ X12))
% 0.39/0.62          | ~ (v1_funct_1 @ X12)
% 0.39/0.62          | ~ (v1_relat_1 @ X12))),
% 0.39/0.62      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.39/0.62  thf('79', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.39/0.62      inference('demod', [status(thm)], ['71', '72', '73', '74', '75', '76'])).
% 0.39/0.62  thf('80', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         ((m1_subset_1 @ X0 @ 
% 0.39/0.62           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.39/0.62          | ~ (v1_relat_1 @ X0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['42', '45'])).
% 0.39/0.62  thf('81', plain,
% 0.39/0.62      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.39/0.62         (k1_zfmisc_1 @ 
% 0.39/0.62          (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))
% 0.39/0.62        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.39/0.62      inference('sup+', [status(thm)], ['79', '80'])).
% 0.39/0.62  thf('82', plain,
% 0.39/0.62      ((~ (v1_relat_1 @ sk_C)
% 0.39/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.39/0.62        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.39/0.62           (k1_zfmisc_1 @ 
% 0.39/0.62            (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))))),
% 0.39/0.62      inference('sup-', [status(thm)], ['78', '81'])).
% 0.39/0.62  thf('83', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.62      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.62  thf('84', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('85', plain,
% 0.39/0.62      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.39/0.62        (k1_zfmisc_1 @ 
% 0.39/0.62         (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 0.39/0.62      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.39/0.62  thf('86', plain,
% 0.39/0.62      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.39/0.62         ((v1_relat_1 @ X14)
% 0.39/0.62          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.39/0.62      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.39/0.62  thf('87', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.39/0.62      inference('sup-', [status(thm)], ['85', '86'])).
% 0.39/0.62  thf('88', plain, ((v2_funct_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('89', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('90', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.62      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.62  thf('91', plain,
% 0.39/0.62      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.39/0.62        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.39/0.62      inference('demod', [status(thm)], ['34', '77', '87', '88', '89', '90'])).
% 0.39/0.62  thf('92', plain,
% 0.39/0.62      ((~ (v1_relat_1 @ sk_C)
% 0.39/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.39/0.62        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 0.39/0.62      inference('sup-', [status(thm)], ['11', '91'])).
% 0.39/0.62  thf('93', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.62      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.62  thf('94', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('95', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)),
% 0.39/0.62      inference('demod', [status(thm)], ['92', '93', '94'])).
% 0.39/0.62  thf('96', plain,
% 0.39/0.62      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 0.39/0.62         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.39/0.62      inference('split', [status(esa)], ['0'])).
% 0.39/0.62  thf('97', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 0.39/0.62      inference('sup-', [status(thm)], ['95', '96'])).
% 0.39/0.62  thf('98', plain,
% 0.39/0.62      (~
% 0.39/0.62       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.39/0.62         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 0.39/0.62       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 0.39/0.62       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.39/0.62      inference('split', [status(esa)], ['0'])).
% 0.39/0.62  thf('99', plain,
% 0.39/0.62      (~
% 0.39/0.62       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.39/0.62         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.39/0.62      inference('sat_resolution*', [status(thm)], ['10', '97', '98'])).
% 0.39/0.62  thf('100', plain,
% 0.39/0.62      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.39/0.62          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.39/0.62      inference('simpl_trail', [status(thm)], ['1', '99'])).
% 0.39/0.62  thf('101', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.39/0.62      inference('demod', [status(thm)], ['28', '29'])).
% 0.39/0.62  thf('102', plain,
% 0.39/0.62      (![X13 : $i]:
% 0.39/0.62         (~ (v2_funct_1 @ X13)
% 0.39/0.62          | ((k1_relat_1 @ X13) = (k2_relat_1 @ (k2_funct_1 @ X13)))
% 0.39/0.62          | ~ (v1_funct_1 @ X13)
% 0.39/0.62          | ~ (v1_relat_1 @ X13))),
% 0.39/0.62      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.39/0.62  thf('103', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.39/0.62      inference('sup+', [status(thm)], ['19', '20'])).
% 0.39/0.62  thf('104', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (((k7_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.39/0.62            = (k2_funct_1 @ X0))
% 0.39/0.62          | ~ (v2_funct_1 @ X0)
% 0.39/0.62          | ~ (v1_funct_1 @ X0)
% 0.39/0.62          | ~ (v1_relat_1 @ X0))),
% 0.39/0.62      inference('simplify', [status(thm)], ['54'])).
% 0.39/0.62  thf('105', plain,
% 0.39/0.62      ((((k7_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B) = (k2_funct_1 @ sk_C))
% 0.39/0.62        | ~ (v1_relat_1 @ sk_C)
% 0.39/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.39/0.62        | ~ (v2_funct_1 @ sk_C))),
% 0.39/0.62      inference('sup+', [status(thm)], ['103', '104'])).
% 0.39/0.62  thf('106', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.62      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.62  thf('107', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('108', plain, ((v2_funct_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('109', plain,
% 0.39/0.62      (((k7_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B) = (k2_funct_1 @ sk_C))),
% 0.39/0.62      inference('demod', [status(thm)], ['105', '106', '107', '108'])).
% 0.39/0.62  thf('110', plain,
% 0.39/0.62      (![X8 : $i, X9 : $i]:
% 0.39/0.62         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X8 @ X9)) @ X9)
% 0.39/0.62          | ~ (v1_relat_1 @ X8))),
% 0.39/0.62      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.39/0.62  thf('111', plain,
% 0.39/0.62      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.39/0.62         (~ (r1_tarski @ (k1_relat_1 @ X20) @ X21)
% 0.39/0.62          | ~ (r1_tarski @ (k2_relat_1 @ X20) @ X22)
% 0.39/0.62          | (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.39/0.62          | ~ (v1_relat_1 @ X20))),
% 0.39/0.62      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.39/0.62  thf('112', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.62         (~ (v1_relat_1 @ X1)
% 0.39/0.62          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.39/0.62          | (m1_subset_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.39/0.62             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))
% 0.39/0.62          | ~ (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X1 @ X0)) @ X2))),
% 0.39/0.62      inference('sup-', [status(thm)], ['110', '111'])).
% 0.39/0.62  thf('113', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)
% 0.39/0.62          | (m1_subset_1 @ (k7_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B) @ 
% 0.39/0.62             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 0.39/0.62          | ~ (v1_relat_1 @ (k7_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B))
% 0.39/0.62          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['109', '112'])).
% 0.39/0.62  thf('114', plain,
% 0.39/0.62      (((k7_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B) = (k2_funct_1 @ sk_C))),
% 0.39/0.62      inference('demod', [status(thm)], ['105', '106', '107', '108'])).
% 0.39/0.62  thf('115', plain,
% 0.39/0.62      (((k7_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B) = (k2_funct_1 @ sk_C))),
% 0.39/0.62      inference('demod', [status(thm)], ['105', '106', '107', '108'])).
% 0.39/0.62  thf('116', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.39/0.62      inference('sup-', [status(thm)], ['85', '86'])).
% 0.39/0.62  thf('117', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.39/0.62      inference('sup-', [status(thm)], ['85', '86'])).
% 0.39/0.62  thf('118', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)
% 0.39/0.62          | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.39/0.62             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0))))),
% 0.39/0.62      inference('demod', [status(thm)], ['113', '114', '115', '116', '117'])).
% 0.39/0.62  thf('119', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0)
% 0.39/0.62          | ~ (v1_relat_1 @ sk_C)
% 0.39/0.62          | ~ (v1_funct_1 @ sk_C)
% 0.39/0.62          | ~ (v2_funct_1 @ sk_C)
% 0.39/0.62          | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.39/0.62             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0))))),
% 0.39/0.62      inference('sup-', [status(thm)], ['102', '118'])).
% 0.39/0.62  thf('120', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.62      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.62  thf('121', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('122', plain, ((v2_funct_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('123', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0)
% 0.39/0.62          | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.39/0.62             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0))))),
% 0.39/0.62      inference('demod', [status(thm)], ['119', '120', '121', '122'])).
% 0.39/0.62  thf('124', plain,
% 0.39/0.62      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.39/0.62        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['101', '123'])).
% 0.39/0.62  thf('125', plain, ($false), inference('demod', [status(thm)], ['100', '124'])).
% 0.39/0.62  
% 0.39/0.62  % SZS output end Refutation
% 0.39/0.62  
% 0.39/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
