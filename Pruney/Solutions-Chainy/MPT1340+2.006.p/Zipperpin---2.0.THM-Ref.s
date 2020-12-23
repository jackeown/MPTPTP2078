%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NahhkGPXjE

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:06 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  251 (1363 expanded)
%              Number of leaves         :   43 ( 417 expanded)
%              Depth                    :   28
%              Number of atoms          : 2363 (29888 expanded)
%              Number of equality atoms :  110 ( 812 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('0',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X7 ) )
        = X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('3',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t64_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_struct_0 @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ B ) )
                  & ( v2_funct_1 @ C ) )
               => ( r2_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( k2_tops_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_struct_0 @ A )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( l1_struct_0 @ B ) )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                      = ( k2_struct_0 @ B ) )
                    & ( v2_funct_1 @ C ) )
                 => ( r2_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( k2_tops_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_tops_2])).

thf('4',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('12',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( v1_partfun1 @ X17 @ X18 )
      | ~ ( v1_funct_2 @ X17 @ X18 @ X19 )
      | ~ ( v1_funct_1 @ X17 )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('13',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('17',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_partfun1 @ X21 @ X20 )
      | ( ( k1_relat_1 @ X21 )
        = X20 )
      | ~ ( v4_relat_1 @ X21 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('18',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('20',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('21',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('23',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v4_relat_1 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('24',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','21','24'])).

thf('26',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( v1_partfun1 @ X17 @ X18 )
      | ~ ( v1_funct_2 @ X17 @ X18 @ X19 )
      | ~ ( v1_funct_1 @ X17 )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('32',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('35',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33','38'])).

thf('40',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_partfun1 @ X21 @ X20 )
      | ( ( k1_relat_1 @ X21 )
        = X20 )
      | ~ ( v4_relat_1 @ X21 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('41',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['19','20'])).

thf('43',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('44',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v4_relat_1 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('45',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42','45'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('47',plain,(
    ! [X30: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('48',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','52'])).

thf('54',plain,(
    ! [X30: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('55',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('61',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['10','59','60'])).

thf('62',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('64',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf(d4_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( ( k2_relset_1 @ A @ B @ C )
            = B )
          & ( v2_funct_1 @ C ) )
       => ( ( k2_tops_2 @ A @ B @ C )
          = ( k2_funct_1 @ C ) ) ) ) )).

thf('67',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k2_relset_1 @ X32 @ X31 @ X33 )
       != X31 )
      | ~ ( v2_funct_1 @ X33 )
      | ( ( k2_tops_2 @ X32 @ X31 @ X33 )
        = ( k2_funct_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X32 @ X31 )
      | ~ ( v1_funct_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('68',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('71',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('72',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('77',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('78',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['76','81'])).

thf('83',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['68','69','74','75','84'])).

thf('86',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['61','86'])).

thf('88',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','87'])).

thf('89',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['88','89'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('91',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('92',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

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

thf('93',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k2_relset_1 @ X28 @ X27 @ X26 )
       != X27 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X28 @ X27 )
      | ~ ( v1_funct_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('94',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('97',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('98',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['94','95','96','97','98'])).

thf('100',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k2_relset_1 @ X32 @ X31 @ X33 )
       != X31 )
      | ~ ( v2_funct_1 @ X33 )
      | ( ( k2_tops_2 @ X32 @ X31 @ X33 )
        = ( k2_funct_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X32 @ X31 )
      | ~ ( v1_funct_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('102',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('104',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k2_relset_1 @ X28 @ X27 @ X26 )
       != X27 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X28 @ X27 )
      | ~ ( v1_funct_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('105',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('108',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('109',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['105','106','107','108','109'])).

thf('111',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('113',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k2_relset_1 @ X28 @ X27 @ X26 )
       != X27 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X26 ) @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X28 @ X27 )
      | ~ ( v1_funct_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('114',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('117',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('118',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['114','115','116','117','118'])).

thf('120',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('122',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('123',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
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

thf('126',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X6 ) @ X6 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

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

thf('127',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ( v2_funct_1 @ X3 )
      | ( ( k2_relat_1 @ X3 )
       != ( k1_relat_1 @ X4 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X3 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('128',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('129',plain,(
    ! [X2: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('130',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['125','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['124','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['123','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['110'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('140',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X7 ) )
        = X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('141',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k5_relat_1 @ X6 @ ( k2_funct_1 @ X6 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['139','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['138','144'])).

thf('146',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['19','20'])).

thf('147',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['145','146','147','148'])).

thf('150',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['137','149'])).

thf('151',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['19','20'])).

thf('152',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['150','151','152','153'])).

thf('155',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ( v2_funct_1 @ X3 )
      | ( ( k2_relat_1 @ X3 )
       != ( k1_relat_1 @ X4 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X3 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('156',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X2: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('158',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['19','20'])).

thf('159',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('161',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['110'])).

thf('162',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['156','157','158','159','160','161'])).

thf('163',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['122','162'])).

thf('164',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['19','20'])).

thf('165',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['163','164','165'])).

thf('167',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['121','166'])).

thf('168',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('169',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['19','20'])).

thf('170',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['167','168','169','170','171'])).

thf('173',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['172'])).

thf('174',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('175',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('176',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['102','111','120','173','176'])).

thf('178',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['91','177'])).

thf('179',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('180',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['19','20'])).

thf('181',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['178','179','180','181','182'])).

thf('184',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['183'])).

thf('185',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['90','184'])).

thf('186',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','185'])).

thf('187',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['19','20'])).

thf('188',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['186','187','188','189'])).

thf('191',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('192',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(reflexivity_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_funct_2 @ A @ B @ C @ C ) ) )).

thf('193',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( r2_funct_2 @ X22 @ X23 @ X24 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_2 @ X25 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_funct_2])).

thf('194',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['194','195','196'])).

thf('198',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('199',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('200',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('201',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['197','198','199','200'])).

thf('202',plain,
    ( ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['191','201'])).

thf('203',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('205',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['202','203','204'])).

thf('206',plain,(
    $false ),
    inference(demod,[status(thm)],['190','205'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NahhkGPXjE
% 0.13/0.37  % Computer   : n007.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 12:55:51 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.47/0.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.68  % Solved by: fo/fo7.sh
% 0.47/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.68  % done 458 iterations in 0.195s
% 0.47/0.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.68  % SZS output start Refutation
% 0.47/0.68  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.47/0.68  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.47/0.68  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.47/0.68  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.47/0.68  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.47/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.68  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.47/0.68  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.68  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.47/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.68  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.68  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.68  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.47/0.68  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.47/0.68  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.47/0.68  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.68  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.47/0.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.68  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.47/0.68  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.47/0.68  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.47/0.68  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.47/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.68  thf(sk_C_type, type, sk_C: $i).
% 0.47/0.68  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.47/0.68  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.47/0.68  thf(t65_funct_1, axiom,
% 0.47/0.68    (![A:$i]:
% 0.47/0.68     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.47/0.68       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.47/0.68  thf('0', plain,
% 0.47/0.68      (![X7 : $i]:
% 0.47/0.68         (~ (v2_funct_1 @ X7)
% 0.47/0.68          | ((k2_funct_1 @ (k2_funct_1 @ X7)) = (X7))
% 0.47/0.68          | ~ (v1_funct_1 @ X7)
% 0.47/0.68          | ~ (v1_relat_1 @ X7))),
% 0.47/0.68      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.47/0.68  thf(d3_struct_0, axiom,
% 0.47/0.68    (![A:$i]:
% 0.47/0.68     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.47/0.68  thf('1', plain,
% 0.47/0.68      (![X29 : $i]:
% 0.47/0.68         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.47/0.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.68  thf('2', plain,
% 0.47/0.68      (![X29 : $i]:
% 0.47/0.68         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.47/0.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.68  thf('3', plain,
% 0.47/0.68      (![X29 : $i]:
% 0.47/0.68         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.47/0.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.68  thf(t64_tops_2, conjecture,
% 0.47/0.68    (![A:$i]:
% 0.47/0.68     ( ( l1_struct_0 @ A ) =>
% 0.47/0.68       ( ![B:$i]:
% 0.47/0.68         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.47/0.68           ( ![C:$i]:
% 0.47/0.68             ( ( ( v1_funct_1 @ C ) & 
% 0.47/0.68                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.47/0.68                 ( m1_subset_1 @
% 0.47/0.68                   C @ 
% 0.47/0.68                   ( k1_zfmisc_1 @
% 0.47/0.68                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.47/0.68               ( ( ( ( k2_relset_1 @
% 0.47/0.68                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.47/0.68                     ( k2_struct_0 @ B ) ) & 
% 0.47/0.68                   ( v2_funct_1 @ C ) ) =>
% 0.47/0.68                 ( r2_funct_2 @
% 0.47/0.68                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.47/0.68                   ( k2_tops_2 @
% 0.47/0.68                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.47/0.68                     ( k2_tops_2 @
% 0.47/0.68                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.47/0.68                   C ) ) ) ) ) ) ))).
% 0.47/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.68    (~( ![A:$i]:
% 0.47/0.68        ( ( l1_struct_0 @ A ) =>
% 0.47/0.68          ( ![B:$i]:
% 0.47/0.68            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.47/0.68              ( ![C:$i]:
% 0.47/0.68                ( ( ( v1_funct_1 @ C ) & 
% 0.47/0.68                    ( v1_funct_2 @
% 0.47/0.68                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.47/0.68                    ( m1_subset_1 @
% 0.47/0.68                      C @ 
% 0.47/0.68                      ( k1_zfmisc_1 @
% 0.47/0.68                        ( k2_zfmisc_1 @
% 0.47/0.68                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.47/0.68                  ( ( ( ( k2_relset_1 @
% 0.47/0.68                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.47/0.68                        ( k2_struct_0 @ B ) ) & 
% 0.47/0.68                      ( v2_funct_1 @ C ) ) =>
% 0.47/0.68                    ( r2_funct_2 @
% 0.47/0.68                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.47/0.68                      ( k2_tops_2 @
% 0.47/0.68                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.47/0.68                        ( k2_tops_2 @
% 0.47/0.68                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.47/0.68                      C ) ) ) ) ) ) ) )),
% 0.47/0.68    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.47/0.68  thf('4', plain,
% 0.47/0.68      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.47/0.68          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.68           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.47/0.68          sk_C)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('5', plain,
% 0.47/0.68      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.47/0.68           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.68            (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.47/0.68           sk_C)
% 0.47/0.68        | ~ (l1_struct_0 @ sk_A))),
% 0.47/0.68      inference('sup-', [status(thm)], ['3', '4'])).
% 0.47/0.68  thf('6', plain, ((l1_struct_0 @ sk_A)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('7', plain,
% 0.47/0.68      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.47/0.68          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.68           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.47/0.68          sk_C)),
% 0.47/0.68      inference('demod', [status(thm)], ['5', '6'])).
% 0.47/0.68  thf('8', plain,
% 0.47/0.68      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.47/0.68           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.68            (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.47/0.68           sk_C)
% 0.47/0.68        | ~ (l1_struct_0 @ sk_B))),
% 0.47/0.68      inference('sup-', [status(thm)], ['2', '7'])).
% 0.47/0.68  thf('9', plain, ((l1_struct_0 @ sk_B)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('10', plain,
% 0.47/0.68      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.47/0.68          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.68           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.47/0.68          sk_C)),
% 0.47/0.68      inference('demod', [status(thm)], ['8', '9'])).
% 0.47/0.68  thf('11', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_C @ 
% 0.47/0.68        (k1_zfmisc_1 @ 
% 0.47/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf(cc5_funct_2, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.47/0.68       ( ![C:$i]:
% 0.47/0.68         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.68           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.47/0.68             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.47/0.68  thf('12', plain,
% 0.47/0.68      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.47/0.68         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.47/0.68          | (v1_partfun1 @ X17 @ X18)
% 0.47/0.68          | ~ (v1_funct_2 @ X17 @ X18 @ X19)
% 0.47/0.68          | ~ (v1_funct_1 @ X17)
% 0.47/0.68          | (v1_xboole_0 @ X19))),
% 0.47/0.68      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.47/0.68  thf('13', plain,
% 0.47/0.68      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.47/0.68        | ~ (v1_funct_1 @ sk_C)
% 0.47/0.68        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.47/0.68        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['11', '12'])).
% 0.47/0.68  thf('14', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('15', plain,
% 0.47/0.68      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('16', plain,
% 0.47/0.68      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.47/0.68        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.47/0.68      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.47/0.68  thf(d4_partfun1, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.47/0.68       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.47/0.68  thf('17', plain,
% 0.47/0.68      (![X20 : $i, X21 : $i]:
% 0.47/0.68         (~ (v1_partfun1 @ X21 @ X20)
% 0.47/0.68          | ((k1_relat_1 @ X21) = (X20))
% 0.47/0.68          | ~ (v4_relat_1 @ X21 @ X20)
% 0.47/0.68          | ~ (v1_relat_1 @ X21))),
% 0.47/0.68      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.47/0.68  thf('18', plain,
% 0.47/0.68      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.47/0.68        | ~ (v1_relat_1 @ sk_C)
% 0.47/0.68        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.47/0.68        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['16', '17'])).
% 0.47/0.68  thf('19', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_C @ 
% 0.47/0.68        (k1_zfmisc_1 @ 
% 0.47/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf(cc1_relset_1, axiom,
% 0.47/0.68    (![A:$i,B:$i,C:$i]:
% 0.47/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.68       ( v1_relat_1 @ C ) ))).
% 0.47/0.68  thf('20', plain,
% 0.47/0.68      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.47/0.68         ((v1_relat_1 @ X8)
% 0.47/0.68          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.47/0.68      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.47/0.68  thf('21', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.68      inference('sup-', [status(thm)], ['19', '20'])).
% 0.47/0.68  thf('22', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_C @ 
% 0.47/0.68        (k1_zfmisc_1 @ 
% 0.47/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf(cc2_relset_1, axiom,
% 0.47/0.68    (![A:$i,B:$i,C:$i]:
% 0.47/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.68       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.47/0.68  thf('23', plain,
% 0.47/0.68      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.47/0.68         ((v4_relat_1 @ X11 @ X12)
% 0.47/0.68          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.47/0.68      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.47/0.68  thf('24', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.47/0.68      inference('sup-', [status(thm)], ['22', '23'])).
% 0.47/0.68  thf('25', plain,
% 0.47/0.68      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.47/0.68        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.47/0.68      inference('demod', [status(thm)], ['18', '21', '24'])).
% 0.47/0.68  thf('26', plain,
% 0.47/0.68      (![X29 : $i]:
% 0.47/0.68         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.47/0.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.68  thf('27', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_C @ 
% 0.47/0.68        (k1_zfmisc_1 @ 
% 0.47/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('28', plain,
% 0.47/0.68      (((m1_subset_1 @ sk_C @ 
% 0.47/0.68         (k1_zfmisc_1 @ 
% 0.47/0.68          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.47/0.68        | ~ (l1_struct_0 @ sk_A))),
% 0.47/0.68      inference('sup+', [status(thm)], ['26', '27'])).
% 0.47/0.68  thf('29', plain, ((l1_struct_0 @ sk_A)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('30', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_C @ 
% 0.47/0.68        (k1_zfmisc_1 @ 
% 0.47/0.68         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.68      inference('demod', [status(thm)], ['28', '29'])).
% 0.47/0.68  thf('31', plain,
% 0.47/0.68      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.47/0.68         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.47/0.68          | (v1_partfun1 @ X17 @ X18)
% 0.47/0.68          | ~ (v1_funct_2 @ X17 @ X18 @ X19)
% 0.47/0.68          | ~ (v1_funct_1 @ X17)
% 0.47/0.68          | (v1_xboole_0 @ X19))),
% 0.47/0.68      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.47/0.68  thf('32', plain,
% 0.47/0.68      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.47/0.68        | ~ (v1_funct_1 @ sk_C)
% 0.47/0.68        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.47/0.68        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['30', '31'])).
% 0.47/0.68  thf('33', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('34', plain,
% 0.47/0.68      (![X29 : $i]:
% 0.47/0.68         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.47/0.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.68  thf('35', plain,
% 0.47/0.68      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('36', plain,
% 0.47/0.68      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.47/0.68        | ~ (l1_struct_0 @ sk_A))),
% 0.47/0.68      inference('sup+', [status(thm)], ['34', '35'])).
% 0.47/0.68  thf('37', plain, ((l1_struct_0 @ sk_A)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('38', plain,
% 0.47/0.68      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.47/0.68      inference('demod', [status(thm)], ['36', '37'])).
% 0.47/0.68  thf('39', plain,
% 0.47/0.68      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.47/0.68        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.47/0.68      inference('demod', [status(thm)], ['32', '33', '38'])).
% 0.47/0.68  thf('40', plain,
% 0.47/0.68      (![X20 : $i, X21 : $i]:
% 0.47/0.68         (~ (v1_partfun1 @ X21 @ X20)
% 0.47/0.68          | ((k1_relat_1 @ X21) = (X20))
% 0.47/0.68          | ~ (v4_relat_1 @ X21 @ X20)
% 0.47/0.68          | ~ (v1_relat_1 @ X21))),
% 0.47/0.68      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.47/0.68  thf('41', plain,
% 0.47/0.68      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.47/0.68        | ~ (v1_relat_1 @ sk_C)
% 0.47/0.68        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.47/0.68        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['39', '40'])).
% 0.47/0.68  thf('42', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.68      inference('sup-', [status(thm)], ['19', '20'])).
% 0.47/0.68  thf('43', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_C @ 
% 0.47/0.68        (k1_zfmisc_1 @ 
% 0.47/0.68         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.68      inference('demod', [status(thm)], ['28', '29'])).
% 0.47/0.68  thf('44', plain,
% 0.47/0.68      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.47/0.68         ((v4_relat_1 @ X11 @ X12)
% 0.47/0.68          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.47/0.68      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.47/0.68  thf('45', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.47/0.68      inference('sup-', [status(thm)], ['43', '44'])).
% 0.47/0.68  thf('46', plain,
% 0.47/0.68      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.47/0.68        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.47/0.68      inference('demod', [status(thm)], ['41', '42', '45'])).
% 0.47/0.68  thf(fc2_struct_0, axiom,
% 0.47/0.68    (![A:$i]:
% 0.47/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.47/0.68       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.47/0.68  thf('47', plain,
% 0.47/0.68      (![X30 : $i]:
% 0.47/0.68         (~ (v1_xboole_0 @ (u1_struct_0 @ X30))
% 0.47/0.68          | ~ (l1_struct_0 @ X30)
% 0.47/0.68          | (v2_struct_0 @ X30))),
% 0.47/0.68      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.47/0.68  thf('48', plain,
% 0.47/0.68      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))
% 0.47/0.68        | (v2_struct_0 @ sk_B)
% 0.47/0.68        | ~ (l1_struct_0 @ sk_B))),
% 0.47/0.68      inference('sup-', [status(thm)], ['46', '47'])).
% 0.47/0.68  thf('49', plain, ((l1_struct_0 @ sk_B)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('50', plain,
% 0.47/0.68      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 0.47/0.68      inference('demod', [status(thm)], ['48', '49'])).
% 0.47/0.68  thf('51', plain, (~ (v2_struct_0 @ sk_B)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('52', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.47/0.68      inference('clc', [status(thm)], ['50', '51'])).
% 0.47/0.68  thf('53', plain,
% 0.47/0.68      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.47/0.68        | ((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)))),
% 0.47/0.68      inference('demod', [status(thm)], ['25', '52'])).
% 0.47/0.68  thf('54', plain,
% 0.47/0.68      (![X30 : $i]:
% 0.47/0.68         (~ (v1_xboole_0 @ (u1_struct_0 @ X30))
% 0.47/0.68          | ~ (l1_struct_0 @ X30)
% 0.47/0.68          | (v2_struct_0 @ X30))),
% 0.47/0.68      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.47/0.68  thf('55', plain,
% 0.47/0.68      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))
% 0.47/0.68        | (v2_struct_0 @ sk_B)
% 0.47/0.68        | ~ (l1_struct_0 @ sk_B))),
% 0.47/0.68      inference('sup-', [status(thm)], ['53', '54'])).
% 0.47/0.68  thf('56', plain, ((l1_struct_0 @ sk_B)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('57', plain,
% 0.47/0.68      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 0.47/0.68      inference('demod', [status(thm)], ['55', '56'])).
% 0.47/0.68  thf('58', plain, (~ (v2_struct_0 @ sk_B)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('59', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.47/0.68      inference('clc', [status(thm)], ['57', '58'])).
% 0.47/0.68  thf('60', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.47/0.68      inference('clc', [status(thm)], ['57', '58'])).
% 0.47/0.68  thf('61', plain,
% 0.47/0.68      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.47/0.68          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.68           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.47/0.68          sk_C)),
% 0.47/0.68      inference('demod', [status(thm)], ['10', '59', '60'])).
% 0.47/0.68  thf('62', plain,
% 0.47/0.68      (![X29 : $i]:
% 0.47/0.68         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.47/0.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.68  thf('63', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_C @ 
% 0.47/0.68        (k1_zfmisc_1 @ 
% 0.47/0.68         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.68      inference('demod', [status(thm)], ['28', '29'])).
% 0.47/0.68  thf('64', plain,
% 0.47/0.68      (((m1_subset_1 @ sk_C @ 
% 0.47/0.68         (k1_zfmisc_1 @ 
% 0.47/0.68          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.47/0.68        | ~ (l1_struct_0 @ sk_B))),
% 0.47/0.68      inference('sup+', [status(thm)], ['62', '63'])).
% 0.47/0.68  thf('65', plain, ((l1_struct_0 @ sk_B)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('66', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_C @ 
% 0.47/0.68        (k1_zfmisc_1 @ 
% 0.47/0.68         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.47/0.68      inference('demod', [status(thm)], ['64', '65'])).
% 0.47/0.68  thf(d4_tops_2, axiom,
% 0.47/0.68    (![A:$i,B:$i,C:$i]:
% 0.47/0.68     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.47/0.68         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.68       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.47/0.68         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.47/0.68  thf('67', plain,
% 0.47/0.68      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.47/0.68         (((k2_relset_1 @ X32 @ X31 @ X33) != (X31))
% 0.47/0.68          | ~ (v2_funct_1 @ X33)
% 0.47/0.68          | ((k2_tops_2 @ X32 @ X31 @ X33) = (k2_funct_1 @ X33))
% 0.47/0.68          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 0.47/0.68          | ~ (v1_funct_2 @ X33 @ X32 @ X31)
% 0.47/0.68          | ~ (v1_funct_1 @ X33))),
% 0.47/0.68      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.47/0.68  thf('68', plain,
% 0.47/0.68      ((~ (v1_funct_1 @ sk_C)
% 0.47/0.68        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.47/0.68        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.47/0.68            = (k2_funct_1 @ sk_C))
% 0.47/0.68        | ~ (v2_funct_1 @ sk_C)
% 0.47/0.68        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.47/0.68            != (k2_struct_0 @ sk_B)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['66', '67'])).
% 0.47/0.68  thf('69', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('70', plain,
% 0.47/0.68      (![X29 : $i]:
% 0.47/0.68         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.47/0.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.68  thf('71', plain,
% 0.47/0.68      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.47/0.68      inference('demod', [status(thm)], ['36', '37'])).
% 0.47/0.68  thf('72', plain,
% 0.47/0.68      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.47/0.68        | ~ (l1_struct_0 @ sk_B))),
% 0.47/0.68      inference('sup+', [status(thm)], ['70', '71'])).
% 0.47/0.68  thf('73', plain, ((l1_struct_0 @ sk_B)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('74', plain,
% 0.47/0.68      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.47/0.68      inference('demod', [status(thm)], ['72', '73'])).
% 0.47/0.68  thf('75', plain, ((v2_funct_1 @ sk_C)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('76', plain,
% 0.47/0.68      (![X29 : $i]:
% 0.47/0.68         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.47/0.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.68  thf('77', plain,
% 0.47/0.68      (![X29 : $i]:
% 0.47/0.68         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.47/0.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.68  thf('78', plain,
% 0.47/0.68      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.47/0.68         = (k2_struct_0 @ sk_B))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('79', plain,
% 0.47/0.68      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.47/0.68          = (k2_struct_0 @ sk_B))
% 0.47/0.68        | ~ (l1_struct_0 @ sk_A))),
% 0.47/0.68      inference('sup+', [status(thm)], ['77', '78'])).
% 0.47/0.68  thf('80', plain, ((l1_struct_0 @ sk_A)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('81', plain,
% 0.47/0.68      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.47/0.68         = (k2_struct_0 @ sk_B))),
% 0.47/0.68      inference('demod', [status(thm)], ['79', '80'])).
% 0.47/0.68  thf('82', plain,
% 0.47/0.68      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.47/0.68          = (k2_struct_0 @ sk_B))
% 0.47/0.68        | ~ (l1_struct_0 @ sk_B))),
% 0.47/0.68      inference('sup+', [status(thm)], ['76', '81'])).
% 0.47/0.68  thf('83', plain, ((l1_struct_0 @ sk_B)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('84', plain,
% 0.47/0.68      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.47/0.68         = (k2_struct_0 @ sk_B))),
% 0.47/0.68      inference('demod', [status(thm)], ['82', '83'])).
% 0.47/0.68  thf('85', plain,
% 0.47/0.68      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.47/0.68          = (k2_funct_1 @ sk_C))
% 0.47/0.68        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.47/0.68      inference('demod', [status(thm)], ['68', '69', '74', '75', '84'])).
% 0.47/0.68  thf('86', plain,
% 0.47/0.68      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.47/0.68         = (k2_funct_1 @ sk_C))),
% 0.47/0.68      inference('simplify', [status(thm)], ['85'])).
% 0.47/0.68  thf('87', plain,
% 0.47/0.68      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.47/0.68          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.68           (k2_funct_1 @ sk_C)) @ 
% 0.47/0.68          sk_C)),
% 0.47/0.68      inference('demod', [status(thm)], ['61', '86'])).
% 0.47/0.68  thf('88', plain,
% 0.47/0.68      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.47/0.68           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.68            (k2_funct_1 @ sk_C)) @ 
% 0.47/0.68           sk_C)
% 0.47/0.68        | ~ (l1_struct_0 @ sk_B))),
% 0.47/0.68      inference('sup-', [status(thm)], ['1', '87'])).
% 0.47/0.68  thf('89', plain, ((l1_struct_0 @ sk_B)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('90', plain,
% 0.47/0.68      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.47/0.68          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.68           (k2_funct_1 @ sk_C)) @ 
% 0.47/0.68          sk_C)),
% 0.47/0.68      inference('demod', [status(thm)], ['88', '89'])).
% 0.47/0.68  thf(t55_funct_1, axiom,
% 0.47/0.68    (![A:$i]:
% 0.47/0.68     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.47/0.68       ( ( v2_funct_1 @ A ) =>
% 0.47/0.68         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.47/0.68           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.47/0.68  thf('91', plain,
% 0.47/0.68      (![X5 : $i]:
% 0.47/0.68         (~ (v2_funct_1 @ X5)
% 0.47/0.68          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 0.47/0.68          | ~ (v1_funct_1 @ X5)
% 0.47/0.68          | ~ (v1_relat_1 @ X5))),
% 0.47/0.68      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.47/0.68  thf('92', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_C @ 
% 0.47/0.68        (k1_zfmisc_1 @ 
% 0.47/0.68         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.47/0.68      inference('demod', [status(thm)], ['64', '65'])).
% 0.47/0.68  thf(t31_funct_2, axiom,
% 0.47/0.68    (![A:$i,B:$i,C:$i]:
% 0.47/0.68     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.47/0.68         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.68       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.47/0.68         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.47/0.68           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.47/0.68           ( m1_subset_1 @
% 0.47/0.68             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.47/0.68  thf('93', plain,
% 0.47/0.68      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.47/0.68         (~ (v2_funct_1 @ X26)
% 0.47/0.68          | ((k2_relset_1 @ X28 @ X27 @ X26) != (X27))
% 0.47/0.68          | (m1_subset_1 @ (k2_funct_1 @ X26) @ 
% 0.47/0.68             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.47/0.68          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27)))
% 0.47/0.68          | ~ (v1_funct_2 @ X26 @ X28 @ X27)
% 0.47/0.68          | ~ (v1_funct_1 @ X26))),
% 0.47/0.68      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.47/0.68  thf('94', plain,
% 0.47/0.68      ((~ (v1_funct_1 @ sk_C)
% 0.47/0.68        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.47/0.68        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.47/0.68           (k1_zfmisc_1 @ 
% 0.47/0.68            (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.47/0.68        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.47/0.68            != (k2_struct_0 @ sk_B))
% 0.47/0.68        | ~ (v2_funct_1 @ sk_C))),
% 0.47/0.68      inference('sup-', [status(thm)], ['92', '93'])).
% 0.47/0.68  thf('95', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('96', plain,
% 0.47/0.68      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.47/0.68      inference('demod', [status(thm)], ['72', '73'])).
% 0.47/0.68  thf('97', plain,
% 0.47/0.68      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.47/0.68         = (k2_struct_0 @ sk_B))),
% 0.47/0.68      inference('demod', [status(thm)], ['82', '83'])).
% 0.47/0.68  thf('98', plain, ((v2_funct_1 @ sk_C)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('99', plain,
% 0.47/0.68      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.47/0.68         (k1_zfmisc_1 @ 
% 0.47/0.68          (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.47/0.68        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.47/0.68      inference('demod', [status(thm)], ['94', '95', '96', '97', '98'])).
% 0.47/0.68  thf('100', plain,
% 0.47/0.68      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.47/0.68        (k1_zfmisc_1 @ 
% 0.47/0.68         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.47/0.68      inference('simplify', [status(thm)], ['99'])).
% 0.47/0.68  thf('101', plain,
% 0.47/0.68      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.47/0.68         (((k2_relset_1 @ X32 @ X31 @ X33) != (X31))
% 0.47/0.68          | ~ (v2_funct_1 @ X33)
% 0.47/0.68          | ((k2_tops_2 @ X32 @ X31 @ X33) = (k2_funct_1 @ X33))
% 0.47/0.68          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 0.47/0.68          | ~ (v1_funct_2 @ X33 @ X32 @ X31)
% 0.47/0.68          | ~ (v1_funct_1 @ X33))),
% 0.47/0.68      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.47/0.68  thf('102', plain,
% 0.47/0.68      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.47/0.68        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.47/0.68             (k2_struct_0 @ sk_A))
% 0.47/0.68        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.68            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.47/0.68        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.47/0.68        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.68            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['100', '101'])).
% 0.47/0.68  thf('103', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_C @ 
% 0.47/0.68        (k1_zfmisc_1 @ 
% 0.47/0.68         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.47/0.68      inference('demod', [status(thm)], ['64', '65'])).
% 0.47/0.68  thf('104', plain,
% 0.47/0.68      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.47/0.68         (~ (v2_funct_1 @ X26)
% 0.47/0.68          | ((k2_relset_1 @ X28 @ X27 @ X26) != (X27))
% 0.47/0.68          | (v1_funct_1 @ (k2_funct_1 @ X26))
% 0.47/0.68          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27)))
% 0.47/0.68          | ~ (v1_funct_2 @ X26 @ X28 @ X27)
% 0.47/0.68          | ~ (v1_funct_1 @ X26))),
% 0.47/0.68      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.47/0.68  thf('105', plain,
% 0.47/0.68      ((~ (v1_funct_1 @ sk_C)
% 0.47/0.68        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.47/0.68        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.47/0.68        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.47/0.68            != (k2_struct_0 @ sk_B))
% 0.47/0.68        | ~ (v2_funct_1 @ sk_C))),
% 0.47/0.68      inference('sup-', [status(thm)], ['103', '104'])).
% 0.47/0.68  thf('106', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('107', plain,
% 0.47/0.68      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.47/0.68      inference('demod', [status(thm)], ['72', '73'])).
% 0.47/0.68  thf('108', plain,
% 0.47/0.68      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.47/0.68         = (k2_struct_0 @ sk_B))),
% 0.47/0.68      inference('demod', [status(thm)], ['82', '83'])).
% 0.47/0.68  thf('109', plain, ((v2_funct_1 @ sk_C)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('110', plain,
% 0.47/0.68      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.47/0.68        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.47/0.68      inference('demod', [status(thm)], ['105', '106', '107', '108', '109'])).
% 0.47/0.68  thf('111', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.47/0.68      inference('simplify', [status(thm)], ['110'])).
% 0.47/0.68  thf('112', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_C @ 
% 0.47/0.68        (k1_zfmisc_1 @ 
% 0.47/0.68         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.47/0.68      inference('demod', [status(thm)], ['64', '65'])).
% 0.47/0.68  thf('113', plain,
% 0.47/0.68      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.47/0.68         (~ (v2_funct_1 @ X26)
% 0.47/0.68          | ((k2_relset_1 @ X28 @ X27 @ X26) != (X27))
% 0.47/0.68          | (v1_funct_2 @ (k2_funct_1 @ X26) @ X27 @ X28)
% 0.47/0.68          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27)))
% 0.47/0.68          | ~ (v1_funct_2 @ X26 @ X28 @ X27)
% 0.47/0.68          | ~ (v1_funct_1 @ X26))),
% 0.47/0.68      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.47/0.68  thf('114', plain,
% 0.47/0.68      ((~ (v1_funct_1 @ sk_C)
% 0.47/0.68        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.47/0.68        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.47/0.68           (k2_struct_0 @ sk_A))
% 0.47/0.68        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.47/0.68            != (k2_struct_0 @ sk_B))
% 0.47/0.68        | ~ (v2_funct_1 @ sk_C))),
% 0.47/0.68      inference('sup-', [status(thm)], ['112', '113'])).
% 0.47/0.68  thf('115', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('116', plain,
% 0.47/0.68      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.47/0.68      inference('demod', [status(thm)], ['72', '73'])).
% 0.47/0.68  thf('117', plain,
% 0.47/0.68      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.47/0.68         = (k2_struct_0 @ sk_B))),
% 0.47/0.68      inference('demod', [status(thm)], ['82', '83'])).
% 0.47/0.68  thf('118', plain, ((v2_funct_1 @ sk_C)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('119', plain,
% 0.47/0.68      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.47/0.68         (k2_struct_0 @ sk_A))
% 0.47/0.68        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.47/0.68      inference('demod', [status(thm)], ['114', '115', '116', '117', '118'])).
% 0.47/0.68  thf('120', plain,
% 0.47/0.68      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.47/0.68        (k2_struct_0 @ sk_A))),
% 0.47/0.68      inference('simplify', [status(thm)], ['119'])).
% 0.47/0.68  thf('121', plain,
% 0.47/0.68      (![X5 : $i]:
% 0.47/0.68         (~ (v2_funct_1 @ X5)
% 0.47/0.68          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 0.47/0.68          | ~ (v1_funct_1 @ X5)
% 0.47/0.68          | ~ (v1_relat_1 @ X5))),
% 0.47/0.68      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.47/0.68  thf(dt_k2_funct_1, axiom,
% 0.47/0.68    (![A:$i]:
% 0.47/0.68     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.47/0.68       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.47/0.68         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.47/0.68  thf('122', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.47/0.68          | ~ (v1_funct_1 @ X0)
% 0.47/0.68          | ~ (v1_relat_1 @ X0))),
% 0.47/0.68      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.47/0.68  thf('123', plain,
% 0.47/0.68      (![X5 : $i]:
% 0.47/0.68         (~ (v2_funct_1 @ X5)
% 0.47/0.68          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 0.47/0.68          | ~ (v1_funct_1 @ X5)
% 0.47/0.68          | ~ (v1_relat_1 @ X5))),
% 0.47/0.68      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.47/0.68  thf('124', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.47/0.68          | ~ (v1_funct_1 @ X0)
% 0.47/0.68          | ~ (v1_relat_1 @ X0))),
% 0.47/0.68      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.47/0.68  thf('125', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.47/0.68          | ~ (v1_funct_1 @ X0)
% 0.47/0.68          | ~ (v1_relat_1 @ X0))),
% 0.47/0.68      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.47/0.68  thf(t61_funct_1, axiom,
% 0.47/0.68    (![A:$i]:
% 0.47/0.68     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.47/0.68       ( ( v2_funct_1 @ A ) =>
% 0.47/0.68         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.47/0.68             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.47/0.68           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.47/0.68             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.47/0.68  thf('126', plain,
% 0.47/0.68      (![X6 : $i]:
% 0.47/0.68         (~ (v2_funct_1 @ X6)
% 0.47/0.68          | ((k5_relat_1 @ (k2_funct_1 @ X6) @ X6)
% 0.47/0.68              = (k6_relat_1 @ (k2_relat_1 @ X6)))
% 0.47/0.68          | ~ (v1_funct_1 @ X6)
% 0.47/0.68          | ~ (v1_relat_1 @ X6))),
% 0.47/0.68      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.47/0.68  thf(t48_funct_1, axiom,
% 0.47/0.68    (![A:$i]:
% 0.47/0.68     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.47/0.68       ( ![B:$i]:
% 0.47/0.68         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.47/0.68           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.47/0.68               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.47/0.68             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 0.47/0.68  thf('127', plain,
% 0.47/0.68      (![X3 : $i, X4 : $i]:
% 0.47/0.68         (~ (v1_relat_1 @ X3)
% 0.47/0.68          | ~ (v1_funct_1 @ X3)
% 0.47/0.68          | (v2_funct_1 @ X3)
% 0.47/0.68          | ((k2_relat_1 @ X3) != (k1_relat_1 @ X4))
% 0.47/0.68          | ~ (v2_funct_1 @ (k5_relat_1 @ X3 @ X4))
% 0.47/0.68          | ~ (v1_funct_1 @ X4)
% 0.47/0.68          | ~ (v1_relat_1 @ X4))),
% 0.47/0.68      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.47/0.68  thf('128', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         (~ (v2_funct_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.47/0.68          | ~ (v1_relat_1 @ X0)
% 0.47/0.68          | ~ (v1_funct_1 @ X0)
% 0.47/0.68          | ~ (v2_funct_1 @ X0)
% 0.47/0.68          | ~ (v1_relat_1 @ X0)
% 0.47/0.68          | ~ (v1_funct_1 @ X0)
% 0.47/0.68          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.47/0.68          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.47/0.68          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.47/0.68          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['126', '127'])).
% 0.47/0.68  thf(fc4_funct_1, axiom,
% 0.47/0.68    (![A:$i]:
% 0.47/0.68     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.47/0.68       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.47/0.68  thf('129', plain, (![X2 : $i]: (v2_funct_1 @ (k6_relat_1 @ X2))),
% 0.47/0.68      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.47/0.68  thf('130', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         (~ (v1_relat_1 @ X0)
% 0.47/0.68          | ~ (v1_funct_1 @ X0)
% 0.47/0.68          | ~ (v2_funct_1 @ X0)
% 0.47/0.68          | ~ (v1_relat_1 @ X0)
% 0.47/0.68          | ~ (v1_funct_1 @ X0)
% 0.47/0.68          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.47/0.68          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.47/0.68          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.47/0.68          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.47/0.68      inference('demod', [status(thm)], ['128', '129'])).
% 0.47/0.68  thf('131', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.47/0.68          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.47/0.68          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.47/0.68          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.47/0.68          | ~ (v2_funct_1 @ X0)
% 0.47/0.68          | ~ (v1_funct_1 @ X0)
% 0.47/0.68          | ~ (v1_relat_1 @ X0))),
% 0.47/0.68      inference('simplify', [status(thm)], ['130'])).
% 0.47/0.68  thf('132', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         (~ (v1_relat_1 @ X0)
% 0.47/0.68          | ~ (v1_funct_1 @ X0)
% 0.47/0.68          | ~ (v1_relat_1 @ X0)
% 0.47/0.68          | ~ (v1_funct_1 @ X0)
% 0.47/0.68          | ~ (v2_funct_1 @ X0)
% 0.47/0.68          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.47/0.68          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.47/0.68          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['125', '131'])).
% 0.47/0.68  thf('133', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         (~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.47/0.68          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.47/0.68          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.47/0.68          | ~ (v2_funct_1 @ X0)
% 0.47/0.68          | ~ (v1_funct_1 @ X0)
% 0.47/0.68          | ~ (v1_relat_1 @ X0))),
% 0.47/0.68      inference('simplify', [status(thm)], ['132'])).
% 0.47/0.68  thf('134', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         (~ (v1_relat_1 @ X0)
% 0.47/0.68          | ~ (v1_funct_1 @ X0)
% 0.47/0.68          | ~ (v1_relat_1 @ X0)
% 0.47/0.68          | ~ (v1_funct_1 @ X0)
% 0.47/0.68          | ~ (v2_funct_1 @ X0)
% 0.47/0.68          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.47/0.68          | (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['124', '133'])).
% 0.47/0.68  thf('135', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.47/0.68          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.47/0.68          | ~ (v2_funct_1 @ X0)
% 0.47/0.68          | ~ (v1_funct_1 @ X0)
% 0.47/0.68          | ~ (v1_relat_1 @ X0))),
% 0.47/0.68      inference('simplify', [status(thm)], ['134'])).
% 0.47/0.68  thf('136', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 0.47/0.68          | ~ (v1_relat_1 @ X0)
% 0.47/0.68          | ~ (v1_funct_1 @ X0)
% 0.47/0.68          | ~ (v2_funct_1 @ X0)
% 0.47/0.68          | ~ (v1_relat_1 @ X0)
% 0.47/0.68          | ~ (v1_funct_1 @ X0)
% 0.47/0.68          | ~ (v2_funct_1 @ X0)
% 0.47/0.68          | (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['123', '135'])).
% 0.47/0.68  thf('137', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.47/0.68          | ~ (v2_funct_1 @ X0)
% 0.47/0.68          | ~ (v1_funct_1 @ X0)
% 0.47/0.68          | ~ (v1_relat_1 @ X0))),
% 0.47/0.68      inference('simplify', [status(thm)], ['136'])).
% 0.47/0.68  thf('138', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.47/0.68      inference('simplify', [status(thm)], ['110'])).
% 0.47/0.68  thf('139', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.47/0.68          | ~ (v1_funct_1 @ X0)
% 0.47/0.68          | ~ (v1_relat_1 @ X0))),
% 0.47/0.68      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.47/0.68  thf('140', plain,
% 0.47/0.68      (![X7 : $i]:
% 0.47/0.68         (~ (v2_funct_1 @ X7)
% 0.47/0.68          | ((k2_funct_1 @ (k2_funct_1 @ X7)) = (X7))
% 0.47/0.68          | ~ (v1_funct_1 @ X7)
% 0.47/0.68          | ~ (v1_relat_1 @ X7))),
% 0.47/0.68      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.47/0.68  thf('141', plain,
% 0.47/0.68      (![X6 : $i]:
% 0.47/0.68         (~ (v2_funct_1 @ X6)
% 0.47/0.68          | ((k5_relat_1 @ X6 @ (k2_funct_1 @ X6))
% 0.47/0.68              = (k6_relat_1 @ (k1_relat_1 @ X6)))
% 0.47/0.68          | ~ (v1_funct_1 @ X6)
% 0.47/0.68          | ~ (v1_relat_1 @ X6))),
% 0.47/0.68      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.47/0.68  thf('142', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.47/0.68            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.47/0.68          | ~ (v1_relat_1 @ X0)
% 0.47/0.68          | ~ (v1_funct_1 @ X0)
% 0.47/0.68          | ~ (v2_funct_1 @ X0)
% 0.47/0.68          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.47/0.68          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.47/0.68          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.47/0.68      inference('sup+', [status(thm)], ['140', '141'])).
% 0.47/0.68  thf('143', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         (~ (v1_relat_1 @ X0)
% 0.47/0.68          | ~ (v1_funct_1 @ X0)
% 0.47/0.68          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.47/0.68          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.47/0.68          | ~ (v2_funct_1 @ X0)
% 0.47/0.68          | ~ (v1_funct_1 @ X0)
% 0.47/0.68          | ~ (v1_relat_1 @ X0)
% 0.47/0.68          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.47/0.68              = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.47/0.68      inference('sup-', [status(thm)], ['139', '142'])).
% 0.47/0.68  thf('144', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.47/0.68            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.47/0.68          | ~ (v2_funct_1 @ X0)
% 0.47/0.68          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.47/0.68          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.47/0.68          | ~ (v1_funct_1 @ X0)
% 0.47/0.68          | ~ (v1_relat_1 @ X0))),
% 0.47/0.68      inference('simplify', [status(thm)], ['143'])).
% 0.47/0.68  thf('145', plain,
% 0.47/0.68      ((~ (v1_relat_1 @ sk_C)
% 0.47/0.68        | ~ (v1_funct_1 @ sk_C)
% 0.47/0.68        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.47/0.68        | ~ (v2_funct_1 @ sk_C)
% 0.47/0.68        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.47/0.68            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 0.47/0.68      inference('sup-', [status(thm)], ['138', '144'])).
% 0.47/0.68  thf('146', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.68      inference('sup-', [status(thm)], ['19', '20'])).
% 0.47/0.68  thf('147', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('148', plain, ((v2_funct_1 @ sk_C)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('149', plain,
% 0.47/0.68      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.47/0.68        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.47/0.68            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 0.47/0.68      inference('demod', [status(thm)], ['145', '146', '147', '148'])).
% 0.47/0.68  thf('150', plain,
% 0.47/0.68      ((~ (v1_relat_1 @ sk_C)
% 0.47/0.68        | ~ (v1_funct_1 @ sk_C)
% 0.47/0.68        | ~ (v2_funct_1 @ sk_C)
% 0.47/0.68        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.47/0.68            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 0.47/0.68      inference('sup-', [status(thm)], ['137', '149'])).
% 0.47/0.68  thf('151', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.68      inference('sup-', [status(thm)], ['19', '20'])).
% 0.47/0.68  thf('152', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('153', plain, ((v2_funct_1 @ sk_C)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('154', plain,
% 0.47/0.68      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.47/0.68         = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.47/0.68      inference('demod', [status(thm)], ['150', '151', '152', '153'])).
% 0.47/0.68  thf('155', plain,
% 0.47/0.68      (![X3 : $i, X4 : $i]:
% 0.47/0.68         (~ (v1_relat_1 @ X3)
% 0.47/0.68          | ~ (v1_funct_1 @ X3)
% 0.47/0.68          | (v2_funct_1 @ X3)
% 0.47/0.68          | ((k2_relat_1 @ X3) != (k1_relat_1 @ X4))
% 0.47/0.68          | ~ (v2_funct_1 @ (k5_relat_1 @ X3 @ X4))
% 0.47/0.68          | ~ (v1_funct_1 @ X4)
% 0.47/0.68          | ~ (v1_relat_1 @ X4))),
% 0.47/0.68      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.47/0.68  thf('156', plain,
% 0.47/0.68      ((~ (v2_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))
% 0.47/0.68        | ~ (v1_relat_1 @ sk_C)
% 0.47/0.68        | ~ (v1_funct_1 @ sk_C)
% 0.47/0.68        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 0.47/0.68        | (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.47/0.68        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.47/0.68        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['154', '155'])).
% 0.47/0.68  thf('157', plain, (![X2 : $i]: (v2_funct_1 @ (k6_relat_1 @ X2))),
% 0.47/0.68      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.47/0.68  thf('158', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.68      inference('sup-', [status(thm)], ['19', '20'])).
% 0.47/0.68  thf('159', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('160', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.47/0.68      inference('clc', [status(thm)], ['50', '51'])).
% 0.47/0.68  thf('161', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.47/0.68      inference('simplify', [status(thm)], ['110'])).
% 0.47/0.68  thf('162', plain,
% 0.47/0.68      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 0.47/0.68        | (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.47/0.68        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.47/0.68      inference('demod', [status(thm)],
% 0.47/0.68                ['156', '157', '158', '159', '160', '161'])).
% 0.47/0.68  thf('163', plain,
% 0.47/0.68      ((~ (v1_relat_1 @ sk_C)
% 0.47/0.68        | ~ (v1_funct_1 @ sk_C)
% 0.47/0.68        | (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.47/0.68        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['122', '162'])).
% 0.47/0.68  thf('164', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.68      inference('sup-', [status(thm)], ['19', '20'])).
% 0.47/0.68  thf('165', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('166', plain,
% 0.47/0.68      (((v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.47/0.68        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.47/0.68      inference('demod', [status(thm)], ['163', '164', '165'])).
% 0.47/0.68  thf('167', plain,
% 0.47/0.68      ((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))
% 0.47/0.68        | ~ (v1_relat_1 @ sk_C)
% 0.47/0.68        | ~ (v1_funct_1 @ sk_C)
% 0.47/0.68        | ~ (v2_funct_1 @ sk_C)
% 0.47/0.68        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['121', '166'])).
% 0.47/0.68  thf('168', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.47/0.68      inference('clc', [status(thm)], ['50', '51'])).
% 0.47/0.68  thf('169', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.68      inference('sup-', [status(thm)], ['19', '20'])).
% 0.47/0.68  thf('170', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('171', plain, ((v2_funct_1 @ sk_C)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('172', plain,
% 0.47/0.68      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.47/0.68        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.47/0.68      inference('demod', [status(thm)], ['167', '168', '169', '170', '171'])).
% 0.47/0.68  thf('173', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.47/0.68      inference('simplify', [status(thm)], ['172'])).
% 0.47/0.68  thf('174', plain,
% 0.47/0.68      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.47/0.68        (k1_zfmisc_1 @ 
% 0.47/0.68         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.47/0.68      inference('simplify', [status(thm)], ['99'])).
% 0.47/0.68  thf(redefinition_k2_relset_1, axiom,
% 0.47/0.68    (![A:$i,B:$i,C:$i]:
% 0.47/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.68       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.47/0.68  thf('175', plain,
% 0.47/0.68      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.47/0.68         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 0.47/0.68          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.47/0.68      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.47/0.68  thf('176', plain,
% 0.47/0.68      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.68         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['174', '175'])).
% 0.47/0.68  thf('177', plain,
% 0.47/0.68      ((((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.68          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.47/0.68        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.47/0.68      inference('demod', [status(thm)], ['102', '111', '120', '173', '176'])).
% 0.47/0.68  thf('178', plain,
% 0.47/0.68      ((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))
% 0.47/0.68        | ~ (v1_relat_1 @ sk_C)
% 0.47/0.68        | ~ (v1_funct_1 @ sk_C)
% 0.47/0.68        | ~ (v2_funct_1 @ sk_C)
% 0.47/0.68        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.68            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.47/0.68      inference('sup-', [status(thm)], ['91', '177'])).
% 0.47/0.68  thf('179', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.47/0.68      inference('clc', [status(thm)], ['50', '51'])).
% 0.47/0.68  thf('180', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.68      inference('sup-', [status(thm)], ['19', '20'])).
% 0.47/0.68  thf('181', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('182', plain, ((v2_funct_1 @ sk_C)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('183', plain,
% 0.47/0.68      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.47/0.68        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.68            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.47/0.68      inference('demod', [status(thm)], ['178', '179', '180', '181', '182'])).
% 0.47/0.68  thf('184', plain,
% 0.47/0.68      (((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.47/0.68         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.47/0.68      inference('simplify', [status(thm)], ['183'])).
% 0.47/0.68  thf('185', plain,
% 0.47/0.68      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.47/0.68          (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)),
% 0.47/0.68      inference('demod', [status(thm)], ['90', '184'])).
% 0.47/0.68  thf('186', plain,
% 0.47/0.68      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.47/0.68           sk_C)
% 0.47/0.68        | ~ (v1_relat_1 @ sk_C)
% 0.47/0.68        | ~ (v1_funct_1 @ sk_C)
% 0.47/0.68        | ~ (v2_funct_1 @ sk_C))),
% 0.47/0.68      inference('sup-', [status(thm)], ['0', '185'])).
% 0.47/0.68  thf('187', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.68      inference('sup-', [status(thm)], ['19', '20'])).
% 0.47/0.68  thf('188', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('189', plain, ((v2_funct_1 @ sk_C)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('190', plain,
% 0.47/0.68      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.47/0.68          sk_C)),
% 0.47/0.68      inference('demod', [status(thm)], ['186', '187', '188', '189'])).
% 0.47/0.68  thf('191', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_C @ 
% 0.47/0.68        (k1_zfmisc_1 @ 
% 0.47/0.68         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.68      inference('demod', [status(thm)], ['28', '29'])).
% 0.47/0.68  thf('192', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_C @ 
% 0.47/0.68        (k1_zfmisc_1 @ 
% 0.47/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf(reflexivity_r2_funct_2, axiom,
% 0.47/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.68     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.47/0.68         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.47/0.68         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.47/0.68         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.68       ( r2_funct_2 @ A @ B @ C @ C ) ))).
% 0.47/0.68  thf('193', plain,
% 0.47/0.68      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.47/0.68         ((r2_funct_2 @ X22 @ X23 @ X24 @ X24)
% 0.47/0.68          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.47/0.68          | ~ (v1_funct_2 @ X24 @ X22 @ X23)
% 0.47/0.68          | ~ (v1_funct_1 @ X24)
% 0.47/0.68          | ~ (v1_funct_1 @ X25)
% 0.47/0.68          | ~ (v1_funct_2 @ X25 @ X22 @ X23)
% 0.47/0.68          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.47/0.68      inference('cnf', [status(esa)], [reflexivity_r2_funct_2])).
% 0.47/0.68  thf('194', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         (~ (m1_subset_1 @ X0 @ 
% 0.47/0.68             (k1_zfmisc_1 @ 
% 0.47/0.68              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.47/0.68          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.47/0.68          | ~ (v1_funct_1 @ X0)
% 0.47/0.68          | ~ (v1_funct_1 @ sk_C)
% 0.47/0.68          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.47/0.68          | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.47/0.68             sk_C))),
% 0.47/0.68      inference('sup-', [status(thm)], ['192', '193'])).
% 0.47/0.68  thf('195', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('196', plain,
% 0.47/0.68      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('197', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         (~ (m1_subset_1 @ X0 @ 
% 0.47/0.68             (k1_zfmisc_1 @ 
% 0.47/0.68              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.47/0.68          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.47/0.68          | ~ (v1_funct_1 @ X0)
% 0.47/0.68          | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.47/0.68             sk_C))),
% 0.47/0.68      inference('demod', [status(thm)], ['194', '195', '196'])).
% 0.47/0.68  thf('198', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.47/0.68      inference('clc', [status(thm)], ['57', '58'])).
% 0.47/0.68  thf('199', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.47/0.68      inference('clc', [status(thm)], ['57', '58'])).
% 0.47/0.68  thf('200', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.47/0.68      inference('clc', [status(thm)], ['57', '58'])).
% 0.47/0.68  thf('201', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         (~ (m1_subset_1 @ X0 @ 
% 0.47/0.68             (k1_zfmisc_1 @ 
% 0.47/0.68              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.47/0.68          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.47/0.68          | ~ (v1_funct_1 @ X0)
% 0.47/0.68          | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.47/0.68             sk_C))),
% 0.47/0.68      inference('demod', [status(thm)], ['197', '198', '199', '200'])).
% 0.47/0.68  thf('202', plain,
% 0.47/0.68      (((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)
% 0.47/0.68        | ~ (v1_funct_1 @ sk_C)
% 0.47/0.68        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['191', '201'])).
% 0.47/0.68  thf('203', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('204', plain,
% 0.47/0.68      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.47/0.68      inference('demod', [status(thm)], ['36', '37'])).
% 0.47/0.68  thf('205', plain,
% 0.47/0.68      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.47/0.68      inference('demod', [status(thm)], ['202', '203', '204'])).
% 0.47/0.68  thf('206', plain, ($false), inference('demod', [status(thm)], ['190', '205'])).
% 0.47/0.68  
% 0.47/0.68  % SZS output end Refutation
% 0.47/0.68  
% 0.47/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
