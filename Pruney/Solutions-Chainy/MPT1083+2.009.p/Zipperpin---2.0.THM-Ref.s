%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cju1dREWPL

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 185 expanded)
%              Number of leaves         :   34 (  68 expanded)
%              Depth                    :   17
%              Number of atoms          :  715 (2141 expanded)
%              Number of equality atoms :   26 (  75 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(t200_funct_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ( v1_funct_1 @ B )
            & ( v1_funct_2 @ B @ A @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ! [C: $i] :
              ( ( ( v1_relat_1 @ C )
                & ( v5_relat_1 @ C @ A )
                & ( v1_funct_1 @ C ) )
             => ( ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) )
                = ( k1_relat_1 @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ( ( v1_funct_1 @ B )
              & ( v1_funct_2 @ B @ A @ A )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
           => ! [C: $i] :
                ( ( ( v1_relat_1 @ C )
                  & ( v5_relat_1 @ C @ A )
                  & ( v1_funct_1 @ C ) )
               => ( ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) )
                  = ( k1_relat_1 @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t200_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( v1_partfun1 @ X26 @ X27 )
      | ~ ( v1_funct_2 @ X26 @ X27 @ X28 )
      | ~ ( v1_funct_1 @ X26 )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('2',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v1_partfun1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_partfun1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['5','6'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('8',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_partfun1 @ X30 @ X29 )
      | ( ( k1_relat_1 @ X30 )
        = X29 )
      | ~ ( v4_relat_1 @ X30 @ X29 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v4_relat_1 @ sk_B @ sk_A )
    | ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('11',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('13',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('14',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('16',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v4_relat_1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('17',plain,(
    v4_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['9','14','17'])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('19',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) )
        = ( k10_relat_1 @ X12 @ ( k1_relat_1 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('20',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X16 @ X15 ) ) @ ( k1_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ sk_A ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['18','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['12','13'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ sk_A ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('27',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v5_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('28',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['28','29'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('32',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['31'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('34',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X23 ) @ X24 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X23 ) @ X25 )
      | ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v4_relat_1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('39',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X13
        = ( k7_relat_1 @ X13 @ X14 ) )
      | ~ ( v4_relat_1 @ X13 @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('42',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) )
        = ( k9_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['31'])).

thf(t163_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('46',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X17 @ ( k1_relat_1 @ X18 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X18 @ X17 ) @ X19 )
      | ( r1_tarski @ X17 @ ( k10_relat_1 @ X18 @ X19 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t163_funct_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k10_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['30','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k10_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('55',plain,
    ( ~ ( r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k10_relat_1 @ sk_C @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) )
        = ( k10_relat_1 @ X12 @ ( k1_relat_1 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('57',plain,(
    ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_B ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['12','13'])).

thf('61',plain,(
    ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_B ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['9','14','17'])).

thf('63',plain,(
    ( k10_relat_1 @ sk_C @ sk_A )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ~ ( r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['55','63'])).

thf('65',plain,(
    ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['25','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    $false ),
    inference(demod,[status(thm)],['65','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cju1dREWPL
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:09:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 120 iterations in 0.067s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.53  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.21/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.53  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.53  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.53  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.53  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.53  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.53  thf(t200_funct_2, conjecture,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.21/0.53             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.53           ( ![C:$i]:
% 0.21/0.53             ( ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ A ) & 
% 0.21/0.53                 ( v1_funct_1 @ C ) ) =>
% 0.21/0.53               ( ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) = ( k1_relat_1 @ C ) ) ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i]:
% 0.21/0.53        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.53          ( ![B:$i]:
% 0.21/0.53            ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.21/0.53                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.53              ( ![C:$i]:
% 0.21/0.53                ( ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ A ) & 
% 0.21/0.53                    ( v1_funct_1 @ C ) ) =>
% 0.21/0.53                  ( ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) =
% 0.21/0.53                    ( k1_relat_1 @ C ) ) ) ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t200_funct_2])).
% 0.21/0.53  thf('0', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(cc5_funct_2, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.53       ( ![C:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.53           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.21/0.53             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.21/0.53          | (v1_partfun1 @ X26 @ X27)
% 0.21/0.53          | ~ (v1_funct_2 @ X26 @ X27 @ X28)
% 0.21/0.53          | ~ (v1_funct_1 @ X26)
% 0.21/0.53          | (v1_xboole_0 @ X28))),
% 0.21/0.53      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      (((v1_xboole_0 @ sk_A)
% 0.21/0.53        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.53        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.21/0.53        | (v1_partfun1 @ sk_B @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.53  thf('3', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('4', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('5', plain, (((v1_xboole_0 @ sk_A) | (v1_partfun1 @ sk_B @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.21/0.53  thf('6', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('7', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.21/0.53      inference('clc', [status(thm)], ['5', '6'])).
% 0.21/0.53  thf(d4_partfun1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.21/0.53       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      (![X29 : $i, X30 : $i]:
% 0.21/0.53         (~ (v1_partfun1 @ X30 @ X29)
% 0.21/0.53          | ((k1_relat_1 @ X30) = (X29))
% 0.21/0.53          | ~ (v4_relat_1 @ X30 @ X29)
% 0.21/0.53          | ~ (v1_relat_1 @ X30))),
% 0.21/0.53      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.53        | ~ (v4_relat_1 @ sk_B @ sk_A)
% 0.21/0.53        | ((k1_relat_1 @ sk_B) = (sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.53  thf('10', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(cc2_relat_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ A ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      (![X3 : $i, X4 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.21/0.53          | (v1_relat_1 @ X3)
% 0.21/0.53          | ~ (v1_relat_1 @ X4))),
% 0.21/0.53      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.53  thf(fc6_relat_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.21/0.53      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.53  thf('14', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.53      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(cc2_relset_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.53       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.53         ((v4_relat_1 @ X20 @ X21)
% 0.21/0.53          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.21/0.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.53  thf('17', plain, ((v4_relat_1 @ sk_B @ sk_A)),
% 0.21/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.53  thf('18', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['9', '14', '17'])).
% 0.21/0.53  thf(t182_relat_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ A ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( v1_relat_1 @ B ) =>
% 0.21/0.53           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.21/0.53             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      (![X11 : $i, X12 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X11)
% 0.21/0.53          | ((k1_relat_1 @ (k5_relat_1 @ X12 @ X11))
% 0.21/0.53              = (k10_relat_1 @ X12 @ (k1_relat_1 @ X11)))
% 0.21/0.53          | ~ (v1_relat_1 @ X12))),
% 0.21/0.53      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.21/0.53  thf(t44_relat_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ A ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( v1_relat_1 @ B ) =>
% 0.21/0.53           ( r1_tarski @
% 0.21/0.53             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      (![X15 : $i, X16 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X15)
% 0.21/0.53          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X16 @ X15)) @ 
% 0.21/0.53             (k1_relat_1 @ X16))
% 0.21/0.53          | ~ (v1_relat_1 @ X16))),
% 0.21/0.53      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.21/0.53  thf('21', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((r1_tarski @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)) @ 
% 0.21/0.53           (k1_relat_1 @ X1))
% 0.21/0.53          | ~ (v1_relat_1 @ X1)
% 0.21/0.53          | ~ (v1_relat_1 @ X0)
% 0.21/0.53          | ~ (v1_relat_1 @ X1)
% 0.21/0.53          | ~ (v1_relat_1 @ X0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['19', '20'])).
% 0.21/0.53  thf('22', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X0)
% 0.21/0.53          | ~ (v1_relat_1 @ X1)
% 0.21/0.53          | (r1_tarski @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)) @ 
% 0.21/0.53             (k1_relat_1 @ X1)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['21'])).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r1_tarski @ (k10_relat_1 @ X0 @ sk_A) @ (k1_relat_1 @ X0))
% 0.21/0.53          | ~ (v1_relat_1 @ X0)
% 0.21/0.53          | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.53      inference('sup+', [status(thm)], ['18', '22'])).
% 0.21/0.53  thf('24', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.53      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.53  thf('25', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r1_tarski @ (k10_relat_1 @ X0 @ sk_A) @ (k1_relat_1 @ X0))
% 0.21/0.53          | ~ (v1_relat_1 @ X0))),
% 0.21/0.53      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.53  thf('26', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(d19_relat_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ B ) =>
% 0.21/0.53       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.53  thf('27', plain,
% 0.21/0.53      (![X5 : $i, X6 : $i]:
% 0.21/0.53         (~ (v5_relat_1 @ X5 @ X6)
% 0.21/0.53          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 0.21/0.53          | ~ (v1_relat_1 @ X5))),
% 0.21/0.53      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.21/0.53  thf('28', plain,
% 0.21/0.53      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.53  thf('29', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('30', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A)),
% 0.21/0.53      inference('demod', [status(thm)], ['28', '29'])).
% 0.21/0.53  thf(d10_xboole_0, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.53  thf('31', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.53  thf('32', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.53      inference('simplify', [status(thm)], ['31'])).
% 0.21/0.53  thf('33', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.53      inference('simplify', [status(thm)], ['31'])).
% 0.21/0.53  thf(t11_relset_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ C ) =>
% 0.21/0.53       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.21/0.53           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.21/0.53         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.21/0.53  thf('34', plain,
% 0.21/0.53      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.53         (~ (r1_tarski @ (k1_relat_1 @ X23) @ X24)
% 0.21/0.53          | ~ (r1_tarski @ (k2_relat_1 @ X23) @ X25)
% 0.21/0.53          | (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.21/0.53          | ~ (v1_relat_1 @ X23))),
% 0.21/0.53      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.21/0.53  thf('35', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X0)
% 0.21/0.53          | (m1_subset_1 @ X0 @ 
% 0.21/0.53             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.21/0.53          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.53  thf('36', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((m1_subset_1 @ X0 @ 
% 0.21/0.53           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.21/0.53          | ~ (v1_relat_1 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['32', '35'])).
% 0.21/0.53  thf('37', plain,
% 0.21/0.53      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.53         ((v4_relat_1 @ X20 @ X21)
% 0.21/0.53          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.21/0.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.53  thf('38', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.53  thf(t209_relat_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.21/0.53       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.21/0.53  thf('39', plain,
% 0.21/0.53      (![X13 : $i, X14 : $i]:
% 0.21/0.53         (((X13) = (k7_relat_1 @ X13 @ X14))
% 0.21/0.53          | ~ (v4_relat_1 @ X13 @ X14)
% 0.21/0.53          | ~ (v1_relat_1 @ X13))),
% 0.21/0.53      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.21/0.53  thf('40', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X0)
% 0.21/0.53          | ~ (v1_relat_1 @ X0)
% 0.21/0.53          | ((X0) = (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.53  thf('41', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((X0) = (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))) | ~ (v1_relat_1 @ X0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['40'])).
% 0.21/0.53  thf(t148_relat_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ B ) =>
% 0.21/0.53       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.21/0.53  thf('42', plain,
% 0.21/0.53      (![X9 : $i, X10 : $i]:
% 0.21/0.53         (((k2_relat_1 @ (k7_relat_1 @ X9 @ X10)) = (k9_relat_1 @ X9 @ X10))
% 0.21/0.53          | ~ (v1_relat_1 @ X9))),
% 0.21/0.53      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.53  thf('43', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.21/0.53          | ~ (v1_relat_1 @ X0)
% 0.21/0.53          | ~ (v1_relat_1 @ X0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['41', '42'])).
% 0.21/0.53  thf('44', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X0)
% 0.21/0.53          | ((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 0.21/0.53      inference('simplify', [status(thm)], ['43'])).
% 0.21/0.53  thf('45', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.53      inference('simplify', [status(thm)], ['31'])).
% 0.21/0.53  thf(t163_funct_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.53       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & 
% 0.21/0.53           ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ B ) ) =>
% 0.21/0.53         ( r1_tarski @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.21/0.53  thf('46', plain,
% 0.21/0.53      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.53         (~ (r1_tarski @ X17 @ (k1_relat_1 @ X18))
% 0.21/0.53          | ~ (r1_tarski @ (k9_relat_1 @ X18 @ X17) @ X19)
% 0.21/0.53          | (r1_tarski @ X17 @ (k10_relat_1 @ X18 @ X19))
% 0.21/0.53          | ~ (v1_funct_1 @ X18)
% 0.21/0.53          | ~ (v1_relat_1 @ X18))),
% 0.21/0.53      inference('cnf', [status(esa)], [t163_funct_1])).
% 0.21/0.53  thf('47', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X0)
% 0.21/0.53          | ~ (v1_funct_1 @ X0)
% 0.21/0.53          | (r1_tarski @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 0.21/0.53          | ~ (r1_tarski @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) @ X1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.53  thf('48', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 0.21/0.53          | ~ (v1_relat_1 @ X0)
% 0.21/0.53          | (r1_tarski @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 0.21/0.53          | ~ (v1_funct_1 @ X0)
% 0.21/0.53          | ~ (v1_relat_1 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['44', '47'])).
% 0.21/0.53  thf('49', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (v1_funct_1 @ X0)
% 0.21/0.53          | (r1_tarski @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 0.21/0.53          | ~ (v1_relat_1 @ X0)
% 0.21/0.53          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.21/0.53      inference('simplify', [status(thm)], ['48'])).
% 0.21/0.53  thf('50', plain,
% 0.21/0.53      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.53        | (r1_tarski @ (k1_relat_1 @ sk_C) @ (k10_relat_1 @ sk_C @ sk_A))
% 0.21/0.53        | ~ (v1_funct_1 @ sk_C))),
% 0.21/0.53      inference('sup-', [status(thm)], ['30', '49'])).
% 0.21/0.53  thf('51', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('52', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('53', plain,
% 0.21/0.53      ((r1_tarski @ (k1_relat_1 @ sk_C) @ (k10_relat_1 @ sk_C @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.21/0.53  thf('54', plain,
% 0.21/0.53      (![X0 : $i, X2 : $i]:
% 0.21/0.53         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.53  thf('55', plain,
% 0.21/0.53      ((~ (r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ (k1_relat_1 @ sk_C))
% 0.21/0.53        | ((k10_relat_1 @ sk_C @ sk_A) = (k1_relat_1 @ sk_C)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.53  thf('56', plain,
% 0.21/0.53      (![X11 : $i, X12 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X11)
% 0.21/0.53          | ((k1_relat_1 @ (k5_relat_1 @ X12 @ X11))
% 0.21/0.53              = (k10_relat_1 @ X12 @ (k1_relat_1 @ X11)))
% 0.21/0.53          | ~ (v1_relat_1 @ X12))),
% 0.21/0.53      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.21/0.53  thf('57', plain,
% 0.21/0.53      (((k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)) != (k1_relat_1 @ sk_C))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('58', plain,
% 0.21/0.53      ((((k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_B)) != (k1_relat_1 @ sk_C))
% 0.21/0.53        | ~ (v1_relat_1 @ sk_C)
% 0.21/0.53        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['56', '57'])).
% 0.21/0.53  thf('59', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('60', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.53      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.53  thf('61', plain,
% 0.21/0.53      (((k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_B)) != (k1_relat_1 @ sk_C))),
% 0.21/0.53      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.21/0.53  thf('62', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['9', '14', '17'])).
% 0.21/0.53  thf('63', plain, (((k10_relat_1 @ sk_C @ sk_A) != (k1_relat_1 @ sk_C))),
% 0.21/0.53      inference('demod', [status(thm)], ['61', '62'])).
% 0.21/0.53  thf('64', plain,
% 0.21/0.53      (~ (r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ (k1_relat_1 @ sk_C))),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['55', '63'])).
% 0.21/0.53  thf('65', plain, (~ (v1_relat_1 @ sk_C)),
% 0.21/0.53      inference('sup-', [status(thm)], ['25', '64'])).
% 0.21/0.53  thf('66', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('67', plain, ($false), inference('demod', [status(thm)], ['65', '66'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
