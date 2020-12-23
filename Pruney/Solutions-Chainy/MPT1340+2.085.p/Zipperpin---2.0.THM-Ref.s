%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DwG9xvBTsB

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:22 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  263 (1464 expanded)
%              Number of leaves         :   46 ( 452 expanded)
%              Depth                    :   36
%              Number of atoms          : 2553 (30930 expanded)
%              Number of equality atoms :  133 ( 949 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('0',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X10 ) )
        = X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
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

thf('3',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t132_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( v1_partfun1 @ C @ A ) ) ) ) )).

thf('11',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( X23 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X23 ) ) )
      | ( v1_partfun1 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X25 @ X23 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('12',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_2 @ X24 @ X25 @ X23 )
      | ( v1_partfun1 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
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
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_partfun1 @ X18 @ X17 )
      | ( ( k1_relat_1 @ X18 )
        = X17 )
      | ~ ( v4_relat_1 @ X18 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('18',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('22',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('23',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('25',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v4_relat_1 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('26',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','23','26'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('28',plain,(
    ! [X30: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('29',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('30',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('31',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('36',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('37',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','39'])).

thf('41',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','39'])).

thf('42',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','39'])).

thf('43',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['9','40','41','42'])).

thf('44',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('45',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['44','49'])).

thf('51',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

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

thf('53',plain,(
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

thf('54',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('57',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('58',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['56','61'])).

thf('63',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('67',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('68',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['66','71'])).

thf('73',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['54','55','64','65','74'])).

thf('76',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['43','76'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('78',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k1_relat_1 @ X8 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('79',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

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

thf('80',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k2_relset_1 @ X28 @ X27 @ X26 )
       != X27 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X28 @ X27 )
      | ~ ( v1_funct_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('81',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('84',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('85',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['81','82','83','84','85'])).

thf('87',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
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

thf('89',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('91',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k2_relset_1 @ X28 @ X27 @ X26 )
       != X27 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X28 @ X27 )
      | ~ ( v1_funct_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('92',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('95',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('96',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['92','93','94','95','96'])).

thf('98',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('100',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k2_relset_1 @ X28 @ X27 @ X26 )
       != X27 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X26 ) @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X28 @ X27 )
      | ~ ( v1_funct_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('101',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('104',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('105',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['101','102','103','104','105'])).

thf('107',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k2_relat_1 @ X8 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('109',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('110',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X10 ) )
        = X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('111',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k1_relat_1 @ X8 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('112',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('113',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
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

thf('114',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X9 ) @ X9 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
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

thf('115',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ X5 )
       != ( k1_relat_1 @ X6 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X5 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('116',plain,(
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
    inference('sup-',[status(thm)],['114','115'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('117',plain,(
    ! [X7: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('118',plain,(
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
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
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
    inference('sup-',[status(thm)],['113','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['112','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
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
    inference('sup-',[status(thm)],['111','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['97'])).

thf('127',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('128',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X10 ) )
        = X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('130',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('131',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('132',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X10 ) )
        = X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('133',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k5_relat_1 @ X9 @ ( k2_funct_1 @ X9 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('135',plain,(
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
    inference('sup-',[status(thm)],['131','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['130','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['129','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['128','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['127','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['142'])).

thf('144',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ),
    inference('sup-',[status(thm)],['126','143'])).

thf('145',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('146',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ),
    inference(demod,[status(thm)],['144','145','146','147'])).

thf('149',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ),
    inference('sup-',[status(thm)],['125','148'])).

thf('150',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('151',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['149','150','151','152'])).

thf('154',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['110','153'])).

thf('155',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('156',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('157',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_relat_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['154','155','156','157','158'])).

thf('160',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ( v2_funct_1 @ X6 )
      | ( ( k2_relat_1 @ X5 )
       != ( k1_relat_1 @ X6 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X5 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('161',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X7: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('163',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['97'])).

thf('164',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('165',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('166',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['166','167'])).

thf('169',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('171',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['161','162','163','168','169','170'])).

thf('172',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['109','171'])).

thf('173',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('174',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['172','173','174'])).

thf('176',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['108','175'])).

thf('177',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['166','167'])).

thf('178',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('179',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['176','177','178','179','180'])).

thf('182',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['181'])).

thf('183',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['89','98','107','182'])).

thf('184',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('185',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('186',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['183','186'])).

thf('188',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['78','187'])).

thf('189',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('190',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('191',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['188','189','190','191','192'])).

thf('194',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['193'])).

thf('195',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['77','194'])).

thf('196',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','195'])).

thf('197',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('198',plain,(
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

thf('199',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( r2_funct_2 @ X19 @ X20 @ X21 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_2 @ X22 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_funct_2])).

thf('200',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf('201',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['200','201','202'])).

thf('204',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','39'])).

thf('205',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','39'])).

thf('206',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','39'])).

thf('207',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['203','204','205','206'])).

thf('208',plain,
    ( ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['197','207'])).

thf('209',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('211',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['208','209','210'])).

thf('212',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('213',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,(
    $false ),
    inference(demod,[status(thm)],['196','211','212','213','214'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DwG9xvBTsB
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:12:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.46/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.65  % Solved by: fo/fo7.sh
% 0.46/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.65  % done 468 iterations in 0.195s
% 0.46/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.65  % SZS output start Refutation
% 0.46/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.65  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.65  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.46/0.65  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.46/0.65  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.46/0.65  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.65  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.46/0.65  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.65  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.65  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.46/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.65  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.65  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.65  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.65  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.46/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.65  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.46/0.65  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.46/0.65  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.65  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.65  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.46/0.65  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.46/0.65  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.46/0.65  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.46/0.65  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.46/0.65  thf(t65_funct_1, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.65       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.46/0.65  thf('0', plain,
% 0.46/0.65      (![X10 : $i]:
% 0.46/0.65         (~ (v2_funct_1 @ X10)
% 0.46/0.65          | ((k2_funct_1 @ (k2_funct_1 @ X10)) = (X10))
% 0.46/0.65          | ~ (v1_funct_1 @ X10)
% 0.46/0.65          | ~ (v1_relat_1 @ X10))),
% 0.46/0.65      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.46/0.65  thf(d3_struct_0, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.46/0.65  thf('1', plain,
% 0.46/0.65      (![X29 : $i]:
% 0.46/0.65         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.46/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.65  thf('2', plain,
% 0.46/0.65      (![X29 : $i]:
% 0.46/0.65         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.46/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.65  thf(t64_tops_2, conjecture,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( l1_struct_0 @ A ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.46/0.65           ( ![C:$i]:
% 0.46/0.65             ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.65                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.46/0.65                 ( m1_subset_1 @
% 0.46/0.65                   C @ 
% 0.46/0.65                   ( k1_zfmisc_1 @
% 0.46/0.65                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.46/0.65               ( ( ( ( k2_relset_1 @
% 0.46/0.65                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.46/0.65                     ( k2_struct_0 @ B ) ) & 
% 0.46/0.65                   ( v2_funct_1 @ C ) ) =>
% 0.46/0.65                 ( r2_funct_2 @
% 0.46/0.65                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.46/0.65                   ( k2_tops_2 @
% 0.46/0.65                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.46/0.65                     ( k2_tops_2 @
% 0.46/0.65                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.46/0.65                   C ) ) ) ) ) ) ))).
% 0.46/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.65    (~( ![A:$i]:
% 0.46/0.65        ( ( l1_struct_0 @ A ) =>
% 0.46/0.65          ( ![B:$i]:
% 0.46/0.65            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.46/0.65              ( ![C:$i]:
% 0.46/0.65                ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.65                    ( v1_funct_2 @
% 0.46/0.65                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.46/0.65                    ( m1_subset_1 @
% 0.46/0.65                      C @ 
% 0.46/0.65                      ( k1_zfmisc_1 @
% 0.46/0.65                        ( k2_zfmisc_1 @
% 0.46/0.65                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.46/0.65                  ( ( ( ( k2_relset_1 @
% 0.46/0.65                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.46/0.65                        ( k2_struct_0 @ B ) ) & 
% 0.46/0.65                      ( v2_funct_1 @ C ) ) =>
% 0.46/0.65                    ( r2_funct_2 @
% 0.46/0.65                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.46/0.65                      ( k2_tops_2 @
% 0.46/0.65                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.46/0.65                        ( k2_tops_2 @
% 0.46/0.65                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.46/0.65                      C ) ) ) ) ) ) ) )),
% 0.46/0.65    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.46/0.65  thf('3', plain,
% 0.46/0.65      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.65          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.65           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.65          sk_C)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('4', plain,
% 0.46/0.65      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.65           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.65            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.65           sk_C)
% 0.46/0.65        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.65      inference('sup-', [status(thm)], ['2', '3'])).
% 0.46/0.65  thf('5', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('6', plain,
% 0.46/0.65      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.65          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.65           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.65          sk_C)),
% 0.46/0.65      inference('demod', [status(thm)], ['4', '5'])).
% 0.46/0.65  thf('7', plain,
% 0.46/0.65      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.65           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.65            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.65           sk_C)
% 0.46/0.65        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.65      inference('sup-', [status(thm)], ['1', '6'])).
% 0.46/0.65  thf('8', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('9', plain,
% 0.46/0.65      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.65          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.65           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.65          sk_C)),
% 0.46/0.65      inference('demod', [status(thm)], ['7', '8'])).
% 0.46/0.65  thf('10', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_C @ 
% 0.46/0.65        (k1_zfmisc_1 @ 
% 0.46/0.65         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(t132_funct_2, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.65         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.65       ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.65           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.65         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.46/0.65           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.46/0.65  thf('11', plain,
% 0.46/0.65      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.46/0.65         (((X23) = (k1_xboole_0))
% 0.46/0.65          | ~ (v1_funct_1 @ X24)
% 0.46/0.65          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X23)))
% 0.46/0.65          | (v1_partfun1 @ X24 @ X25)
% 0.46/0.65          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X23)))
% 0.46/0.65          | ~ (v1_funct_2 @ X24 @ X25 @ X23)
% 0.46/0.65          | ~ (v1_funct_1 @ X24))),
% 0.46/0.65      inference('cnf', [status(esa)], [t132_funct_2])).
% 0.46/0.65  thf('12', plain,
% 0.46/0.65      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.46/0.65         (~ (v1_funct_2 @ X24 @ X25 @ X23)
% 0.46/0.65          | (v1_partfun1 @ X24 @ X25)
% 0.46/0.65          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X23)))
% 0.46/0.65          | ~ (v1_funct_1 @ X24)
% 0.46/0.65          | ((X23) = (k1_xboole_0)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['11'])).
% 0.46/0.65  thf('13', plain,
% 0.46/0.65      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.46/0.65        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.65        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['10', '12'])).
% 0.46/0.65  thf('14', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('15', plain,
% 0.46/0.65      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('16', plain,
% 0.46/0.65      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.46/0.65        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.46/0.65  thf(d4_partfun1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.46/0.65       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.46/0.65  thf('17', plain,
% 0.46/0.65      (![X17 : $i, X18 : $i]:
% 0.46/0.65         (~ (v1_partfun1 @ X18 @ X17)
% 0.46/0.65          | ((k1_relat_1 @ X18) = (X17))
% 0.46/0.65          | ~ (v4_relat_1 @ X18 @ X17)
% 0.46/0.65          | ~ (v1_relat_1 @ X18))),
% 0.46/0.65      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.46/0.65  thf('18', plain,
% 0.46/0.65      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.46/0.65        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.65        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.46/0.65        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['16', '17'])).
% 0.46/0.65  thf('19', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_C @ 
% 0.46/0.65        (k1_zfmisc_1 @ 
% 0.46/0.65         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(cc2_relat_1, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( v1_relat_1 @ A ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.46/0.65  thf('20', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.46/0.65          | (v1_relat_1 @ X0)
% 0.46/0.65          | ~ (v1_relat_1 @ X1))),
% 0.46/0.65      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.46/0.65  thf('21', plain,
% 0.46/0.65      ((~ (v1_relat_1 @ 
% 0.46/0.65           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.46/0.65        | (v1_relat_1 @ sk_C))),
% 0.46/0.65      inference('sup-', [status(thm)], ['19', '20'])).
% 0.46/0.65  thf(fc6_relat_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.46/0.65  thf('22', plain,
% 0.46/0.65      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.46/0.65      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.46/0.65  thf('23', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.65      inference('demod', [status(thm)], ['21', '22'])).
% 0.46/0.65  thf('24', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_C @ 
% 0.46/0.65        (k1_zfmisc_1 @ 
% 0.46/0.65         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(cc2_relset_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.65       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.46/0.65  thf('25', plain,
% 0.46/0.65      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.46/0.65         ((v4_relat_1 @ X11 @ X12)
% 0.46/0.65          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.46/0.65      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.65  thf('26', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['24', '25'])).
% 0.46/0.65  thf('27', plain,
% 0.46/0.65      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.46/0.65        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.46/0.65      inference('demod', [status(thm)], ['18', '23', '26'])).
% 0.46/0.65  thf(fc2_struct_0, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.46/0.65       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.46/0.65  thf('28', plain,
% 0.46/0.65      (![X30 : $i]:
% 0.46/0.65         (~ (v1_xboole_0 @ (u1_struct_0 @ X30))
% 0.46/0.65          | ~ (l1_struct_0 @ X30)
% 0.46/0.65          | (v2_struct_0 @ X30))),
% 0.46/0.65      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.46/0.65  thf('29', plain,
% 0.46/0.65      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.46/0.65        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))
% 0.46/0.65        | (v2_struct_0 @ sk_B)
% 0.46/0.65        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.65      inference('sup-', [status(thm)], ['27', '28'])).
% 0.46/0.65  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.46/0.65  thf('30', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.65      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.65  thf('31', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('32', plain,
% 0.46/0.65      ((((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 0.46/0.65      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.46/0.65  thf('33', plain, (~ (v2_struct_0 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('34', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.46/0.65      inference('clc', [status(thm)], ['32', '33'])).
% 0.46/0.65  thf('35', plain,
% 0.46/0.65      (![X29 : $i]:
% 0.46/0.65         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.46/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.65  thf('36', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.46/0.65      inference('clc', [status(thm)], ['32', '33'])).
% 0.46/0.65  thf('37', plain,
% 0.46/0.65      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.65      inference('sup+', [status(thm)], ['35', '36'])).
% 0.46/0.65  thf('38', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('39', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['37', '38'])).
% 0.46/0.65  thf('40', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['34', '39'])).
% 0.46/0.65  thf('41', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['34', '39'])).
% 0.46/0.65  thf('42', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['34', '39'])).
% 0.46/0.65  thf('43', plain,
% 0.46/0.65      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.65          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.65           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.65          sk_C)),
% 0.46/0.65      inference('demod', [status(thm)], ['9', '40', '41', '42'])).
% 0.46/0.65  thf('44', plain,
% 0.46/0.65      (![X29 : $i]:
% 0.46/0.65         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.46/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.65  thf('45', plain,
% 0.46/0.65      (![X29 : $i]:
% 0.46/0.65         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.46/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.65  thf('46', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_C @ 
% 0.46/0.65        (k1_zfmisc_1 @ 
% 0.46/0.65         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('47', plain,
% 0.46/0.65      (((m1_subset_1 @ sk_C @ 
% 0.46/0.65         (k1_zfmisc_1 @ 
% 0.46/0.65          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.46/0.65        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.65      inference('sup+', [status(thm)], ['45', '46'])).
% 0.46/0.65  thf('48', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('49', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_C @ 
% 0.46/0.65        (k1_zfmisc_1 @ 
% 0.46/0.65         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.65      inference('demod', [status(thm)], ['47', '48'])).
% 0.46/0.65  thf('50', plain,
% 0.46/0.65      (((m1_subset_1 @ sk_C @ 
% 0.46/0.65         (k1_zfmisc_1 @ 
% 0.46/0.65          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.46/0.65        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.65      inference('sup+', [status(thm)], ['44', '49'])).
% 0.46/0.65  thf('51', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('52', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_C @ 
% 0.46/0.65        (k1_zfmisc_1 @ 
% 0.46/0.65         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.46/0.65      inference('demod', [status(thm)], ['50', '51'])).
% 0.46/0.65  thf(d4_tops_2, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.65         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.65       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.46/0.65         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.46/0.65  thf('53', plain,
% 0.46/0.65      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.46/0.65         (((k2_relset_1 @ X32 @ X31 @ X33) != (X31))
% 0.46/0.65          | ~ (v2_funct_1 @ X33)
% 0.46/0.65          | ((k2_tops_2 @ X32 @ X31 @ X33) = (k2_funct_1 @ X33))
% 0.46/0.65          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 0.46/0.65          | ~ (v1_funct_2 @ X33 @ X32 @ X31)
% 0.46/0.65          | ~ (v1_funct_1 @ X33))),
% 0.46/0.65      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.46/0.65  thf('54', plain,
% 0.46/0.65      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.65        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.46/0.65        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.65            = (k2_funct_1 @ sk_C))
% 0.46/0.65        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.65        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.65            != (k2_struct_0 @ sk_B)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['52', '53'])).
% 0.46/0.65  thf('55', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('56', plain,
% 0.46/0.65      (![X29 : $i]:
% 0.46/0.65         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.46/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.65  thf('57', plain,
% 0.46/0.65      (![X29 : $i]:
% 0.46/0.65         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.46/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.65  thf('58', plain,
% 0.46/0.65      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('59', plain,
% 0.46/0.65      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.65        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.65      inference('sup+', [status(thm)], ['57', '58'])).
% 0.46/0.65  thf('60', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('61', plain,
% 0.46/0.65      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.65      inference('demod', [status(thm)], ['59', '60'])).
% 0.46/0.65  thf('62', plain,
% 0.46/0.65      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.46/0.65        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.65      inference('sup+', [status(thm)], ['56', '61'])).
% 0.46/0.65  thf('63', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('64', plain,
% 0.46/0.65      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.46/0.65      inference('demod', [status(thm)], ['62', '63'])).
% 0.46/0.65  thf('65', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('66', plain,
% 0.46/0.65      (![X29 : $i]:
% 0.46/0.65         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.46/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.65  thf('67', plain,
% 0.46/0.65      (![X29 : $i]:
% 0.46/0.65         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.46/0.65      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.65  thf('68', plain,
% 0.46/0.65      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.65         = (k2_struct_0 @ sk_B))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('69', plain,
% 0.46/0.65      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.65          = (k2_struct_0 @ sk_B))
% 0.46/0.65        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.65      inference('sup+', [status(thm)], ['67', '68'])).
% 0.46/0.65  thf('70', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('71', plain,
% 0.46/0.65      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.65         = (k2_struct_0 @ sk_B))),
% 0.46/0.65      inference('demod', [status(thm)], ['69', '70'])).
% 0.46/0.65  thf('72', plain,
% 0.46/0.65      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.65          = (k2_struct_0 @ sk_B))
% 0.46/0.65        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.65      inference('sup+', [status(thm)], ['66', '71'])).
% 0.46/0.65  thf('73', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('74', plain,
% 0.46/0.65      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.65         = (k2_struct_0 @ sk_B))),
% 0.46/0.65      inference('demod', [status(thm)], ['72', '73'])).
% 0.46/0.65  thf('75', plain,
% 0.46/0.65      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.65          = (k2_funct_1 @ sk_C))
% 0.46/0.65        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.46/0.65      inference('demod', [status(thm)], ['54', '55', '64', '65', '74'])).
% 0.46/0.65  thf('76', plain,
% 0.46/0.65      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.65         = (k2_funct_1 @ sk_C))),
% 0.46/0.65      inference('simplify', [status(thm)], ['75'])).
% 0.46/0.65  thf('77', plain,
% 0.46/0.65      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.65          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.65           (k2_funct_1 @ sk_C)) @ 
% 0.46/0.65          sk_C)),
% 0.46/0.65      inference('demod', [status(thm)], ['43', '76'])).
% 0.46/0.65  thf(t55_funct_1, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.65       ( ( v2_funct_1 @ A ) =>
% 0.46/0.65         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.46/0.65           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.46/0.65  thf('78', plain,
% 0.46/0.65      (![X8 : $i]:
% 0.46/0.65         (~ (v2_funct_1 @ X8)
% 0.46/0.65          | ((k1_relat_1 @ X8) = (k2_relat_1 @ (k2_funct_1 @ X8)))
% 0.46/0.65          | ~ (v1_funct_1 @ X8)
% 0.46/0.65          | ~ (v1_relat_1 @ X8))),
% 0.46/0.65      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.46/0.65  thf('79', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_C @ 
% 0.46/0.65        (k1_zfmisc_1 @ 
% 0.46/0.65         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.46/0.65      inference('demod', [status(thm)], ['50', '51'])).
% 0.46/0.65  thf(t31_funct_2, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.65         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.65       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.46/0.65         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.46/0.65           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.46/0.65           ( m1_subset_1 @
% 0.46/0.65             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.46/0.65  thf('80', plain,
% 0.46/0.65      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.46/0.65         (~ (v2_funct_1 @ X26)
% 0.46/0.65          | ((k2_relset_1 @ X28 @ X27 @ X26) != (X27))
% 0.46/0.65          | (m1_subset_1 @ (k2_funct_1 @ X26) @ 
% 0.46/0.65             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.46/0.65          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27)))
% 0.46/0.65          | ~ (v1_funct_2 @ X26 @ X28 @ X27)
% 0.46/0.65          | ~ (v1_funct_1 @ X26))),
% 0.46/0.65      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.46/0.65  thf('81', plain,
% 0.46/0.65      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.65        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.46/0.65        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.65           (k1_zfmisc_1 @ 
% 0.46/0.65            (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.46/0.65        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.65            != (k2_struct_0 @ sk_B))
% 0.46/0.65        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.65      inference('sup-', [status(thm)], ['79', '80'])).
% 0.46/0.65  thf('82', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('83', plain,
% 0.46/0.65      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.46/0.65      inference('demod', [status(thm)], ['62', '63'])).
% 0.46/0.65  thf('84', plain,
% 0.46/0.65      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.65         = (k2_struct_0 @ sk_B))),
% 0.46/0.65      inference('demod', [status(thm)], ['72', '73'])).
% 0.46/0.65  thf('85', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('86', plain,
% 0.46/0.65      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.65         (k1_zfmisc_1 @ 
% 0.46/0.65          (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.46/0.65        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.46/0.65      inference('demod', [status(thm)], ['81', '82', '83', '84', '85'])).
% 0.46/0.65  thf('87', plain,
% 0.46/0.65      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.65        (k1_zfmisc_1 @ 
% 0.46/0.65         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.46/0.65      inference('simplify', [status(thm)], ['86'])).
% 0.46/0.65  thf('88', plain,
% 0.46/0.65      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.46/0.65         (((k2_relset_1 @ X32 @ X31 @ X33) != (X31))
% 0.46/0.65          | ~ (v2_funct_1 @ X33)
% 0.46/0.65          | ((k2_tops_2 @ X32 @ X31 @ X33) = (k2_funct_1 @ X33))
% 0.46/0.65          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 0.46/0.65          | ~ (v1_funct_2 @ X33 @ X32 @ X31)
% 0.46/0.65          | ~ (v1_funct_1 @ X33))),
% 0.46/0.65      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.46/0.65  thf('89', plain,
% 0.46/0.65      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.65        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.46/0.65             (k2_struct_0 @ sk_A))
% 0.46/0.65        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.65            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.65        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.65        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.65            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['87', '88'])).
% 0.46/0.65  thf('90', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_C @ 
% 0.46/0.65        (k1_zfmisc_1 @ 
% 0.46/0.65         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.46/0.65      inference('demod', [status(thm)], ['50', '51'])).
% 0.46/0.65  thf('91', plain,
% 0.46/0.65      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.46/0.65         (~ (v2_funct_1 @ X26)
% 0.46/0.65          | ((k2_relset_1 @ X28 @ X27 @ X26) != (X27))
% 0.46/0.65          | (v1_funct_1 @ (k2_funct_1 @ X26))
% 0.46/0.65          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27)))
% 0.46/0.65          | ~ (v1_funct_2 @ X26 @ X28 @ X27)
% 0.46/0.65          | ~ (v1_funct_1 @ X26))),
% 0.46/0.65      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.46/0.65  thf('92', plain,
% 0.46/0.65      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.65        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.46/0.65        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.65        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.65            != (k2_struct_0 @ sk_B))
% 0.46/0.65        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.65      inference('sup-', [status(thm)], ['90', '91'])).
% 0.46/0.65  thf('93', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('94', plain,
% 0.46/0.65      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.46/0.65      inference('demod', [status(thm)], ['62', '63'])).
% 0.46/0.65  thf('95', plain,
% 0.46/0.65      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.65         = (k2_struct_0 @ sk_B))),
% 0.46/0.65      inference('demod', [status(thm)], ['72', '73'])).
% 0.46/0.65  thf('96', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('97', plain,
% 0.46/0.65      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.65        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.46/0.65      inference('demod', [status(thm)], ['92', '93', '94', '95', '96'])).
% 0.46/0.65  thf('98', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.65      inference('simplify', [status(thm)], ['97'])).
% 0.46/0.65  thf('99', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_C @ 
% 0.46/0.65        (k1_zfmisc_1 @ 
% 0.46/0.65         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.46/0.65      inference('demod', [status(thm)], ['50', '51'])).
% 0.46/0.65  thf('100', plain,
% 0.46/0.65      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.46/0.65         (~ (v2_funct_1 @ X26)
% 0.46/0.65          | ((k2_relset_1 @ X28 @ X27 @ X26) != (X27))
% 0.46/0.65          | (v1_funct_2 @ (k2_funct_1 @ X26) @ X27 @ X28)
% 0.46/0.65          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27)))
% 0.46/0.65          | ~ (v1_funct_2 @ X26 @ X28 @ X27)
% 0.46/0.65          | ~ (v1_funct_1 @ X26))),
% 0.46/0.65      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.46/0.65  thf('101', plain,
% 0.46/0.65      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.65        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.46/0.65        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.46/0.65           (k2_struct_0 @ sk_A))
% 0.46/0.65        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.65            != (k2_struct_0 @ sk_B))
% 0.46/0.65        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.65      inference('sup-', [status(thm)], ['99', '100'])).
% 0.46/0.65  thf('102', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('103', plain,
% 0.46/0.65      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.46/0.65      inference('demod', [status(thm)], ['62', '63'])).
% 0.46/0.65  thf('104', plain,
% 0.46/0.65      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.65         = (k2_struct_0 @ sk_B))),
% 0.46/0.65      inference('demod', [status(thm)], ['72', '73'])).
% 0.46/0.65  thf('105', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('106', plain,
% 0.46/0.65      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.46/0.65         (k2_struct_0 @ sk_A))
% 0.46/0.65        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.46/0.65      inference('demod', [status(thm)], ['101', '102', '103', '104', '105'])).
% 0.46/0.65  thf('107', plain,
% 0.46/0.65      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.46/0.65        (k2_struct_0 @ sk_A))),
% 0.46/0.65      inference('simplify', [status(thm)], ['106'])).
% 0.46/0.65  thf('108', plain,
% 0.46/0.65      (![X8 : $i]:
% 0.46/0.65         (~ (v2_funct_1 @ X8)
% 0.46/0.65          | ((k2_relat_1 @ X8) = (k1_relat_1 @ (k2_funct_1 @ X8)))
% 0.46/0.65          | ~ (v1_funct_1 @ X8)
% 0.46/0.65          | ~ (v1_relat_1 @ X8))),
% 0.46/0.65      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.46/0.65  thf(dt_k2_funct_1, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.65       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.46/0.65         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.46/0.65  thf('109', plain,
% 0.46/0.65      (![X4 : $i]:
% 0.46/0.65         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.46/0.65          | ~ (v1_funct_1 @ X4)
% 0.46/0.65          | ~ (v1_relat_1 @ X4))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.65  thf('110', plain,
% 0.46/0.65      (![X10 : $i]:
% 0.46/0.65         (~ (v2_funct_1 @ X10)
% 0.46/0.65          | ((k2_funct_1 @ (k2_funct_1 @ X10)) = (X10))
% 0.46/0.65          | ~ (v1_funct_1 @ X10)
% 0.46/0.65          | ~ (v1_relat_1 @ X10))),
% 0.46/0.65      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.46/0.65  thf('111', plain,
% 0.46/0.65      (![X8 : $i]:
% 0.46/0.65         (~ (v2_funct_1 @ X8)
% 0.46/0.65          | ((k1_relat_1 @ X8) = (k2_relat_1 @ (k2_funct_1 @ X8)))
% 0.46/0.65          | ~ (v1_funct_1 @ X8)
% 0.46/0.65          | ~ (v1_relat_1 @ X8))),
% 0.46/0.65      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.46/0.65  thf('112', plain,
% 0.46/0.65      (![X4 : $i]:
% 0.46/0.65         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 0.46/0.65          | ~ (v1_funct_1 @ X4)
% 0.46/0.65          | ~ (v1_relat_1 @ X4))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.65  thf('113', plain,
% 0.46/0.65      (![X4 : $i]:
% 0.46/0.65         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.46/0.65          | ~ (v1_funct_1 @ X4)
% 0.46/0.65          | ~ (v1_relat_1 @ X4))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.65  thf(t61_funct_1, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.65       ( ( v2_funct_1 @ A ) =>
% 0.46/0.65         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.46/0.65             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.46/0.65           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.46/0.65             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.46/0.65  thf('114', plain,
% 0.46/0.65      (![X9 : $i]:
% 0.46/0.65         (~ (v2_funct_1 @ X9)
% 0.46/0.65          | ((k5_relat_1 @ (k2_funct_1 @ X9) @ X9)
% 0.46/0.65              = (k6_relat_1 @ (k2_relat_1 @ X9)))
% 0.46/0.65          | ~ (v1_funct_1 @ X9)
% 0.46/0.65          | ~ (v1_relat_1 @ X9))),
% 0.46/0.65      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.46/0.65  thf(t48_funct_1, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.46/0.65           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.46/0.65               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.46/0.65             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 0.46/0.65  thf('115', plain,
% 0.46/0.65      (![X5 : $i, X6 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ X5)
% 0.46/0.65          | ~ (v1_funct_1 @ X5)
% 0.46/0.65          | (v2_funct_1 @ X5)
% 0.46/0.65          | ((k2_relat_1 @ X5) != (k1_relat_1 @ X6))
% 0.46/0.65          | ~ (v2_funct_1 @ (k5_relat_1 @ X5 @ X6))
% 0.46/0.65          | ~ (v1_funct_1 @ X6)
% 0.46/0.65          | ~ (v1_relat_1 @ X6))),
% 0.46/0.65      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.46/0.65  thf('116', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (v2_funct_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.46/0.65          | ~ (v1_relat_1 @ X0)
% 0.46/0.65          | ~ (v1_funct_1 @ X0)
% 0.46/0.65          | ~ (v2_funct_1 @ X0)
% 0.46/0.65          | ~ (v1_relat_1 @ X0)
% 0.46/0.65          | ~ (v1_funct_1 @ X0)
% 0.46/0.65          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.46/0.65          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.65          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.65          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['114', '115'])).
% 0.46/0.65  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 0.46/0.65  thf('117', plain, (![X7 : $i]: (v2_funct_1 @ (k6_relat_1 @ X7))),
% 0.46/0.65      inference('cnf', [status(esa)], [t52_funct_1])).
% 0.46/0.65  thf('118', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ X0)
% 0.46/0.65          | ~ (v1_funct_1 @ X0)
% 0.46/0.65          | ~ (v2_funct_1 @ X0)
% 0.46/0.65          | ~ (v1_relat_1 @ X0)
% 0.46/0.65          | ~ (v1_funct_1 @ X0)
% 0.46/0.65          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.46/0.65          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.65          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.65          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.46/0.65      inference('demod', [status(thm)], ['116', '117'])).
% 0.46/0.65  thf('119', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.65          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.65          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.65          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.46/0.65          | ~ (v2_funct_1 @ X0)
% 0.46/0.65          | ~ (v1_funct_1 @ X0)
% 0.46/0.65          | ~ (v1_relat_1 @ X0))),
% 0.46/0.65      inference('simplify', [status(thm)], ['118'])).
% 0.46/0.65  thf('120', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ X0)
% 0.46/0.65          | ~ (v1_funct_1 @ X0)
% 0.46/0.65          | ~ (v1_relat_1 @ X0)
% 0.46/0.65          | ~ (v1_funct_1 @ X0)
% 0.46/0.65          | ~ (v2_funct_1 @ X0)
% 0.46/0.65          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.46/0.65          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.65          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['113', '119'])).
% 0.46/0.65  thf('121', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.65          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.65          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.46/0.65          | ~ (v2_funct_1 @ X0)
% 0.46/0.65          | ~ (v1_funct_1 @ X0)
% 0.46/0.65          | ~ (v1_relat_1 @ X0))),
% 0.46/0.65      inference('simplify', [status(thm)], ['120'])).
% 0.46/0.65  thf('122', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ X0)
% 0.46/0.65          | ~ (v1_funct_1 @ X0)
% 0.46/0.65          | ~ (v1_relat_1 @ X0)
% 0.46/0.65          | ~ (v1_funct_1 @ X0)
% 0.46/0.65          | ~ (v2_funct_1 @ X0)
% 0.46/0.65          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.46/0.65          | (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['112', '121'])).
% 0.46/0.65  thf('123', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.65          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.46/0.65          | ~ (v2_funct_1 @ X0)
% 0.46/0.65          | ~ (v1_funct_1 @ X0)
% 0.46/0.65          | ~ (v1_relat_1 @ X0))),
% 0.46/0.65      inference('simplify', [status(thm)], ['122'])).
% 0.46/0.65  thf('124', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 0.46/0.65          | ~ (v1_relat_1 @ X0)
% 0.46/0.65          | ~ (v1_funct_1 @ X0)
% 0.46/0.65          | ~ (v2_funct_1 @ X0)
% 0.46/0.65          | ~ (v1_relat_1 @ X0)
% 0.46/0.65          | ~ (v1_funct_1 @ X0)
% 0.46/0.65          | ~ (v2_funct_1 @ X0)
% 0.46/0.65          | (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['111', '123'])).
% 0.46/0.65  thf('125', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.65          | ~ (v2_funct_1 @ X0)
% 0.46/0.65          | ~ (v1_funct_1 @ X0)
% 0.46/0.65          | ~ (v1_relat_1 @ X0))),
% 0.46/0.65      inference('simplify', [status(thm)], ['124'])).
% 0.46/0.65  thf('126', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.65      inference('simplify', [status(thm)], ['97'])).
% 0.46/0.65  thf('127', plain,
% 0.46/0.65      (![X4 : $i]:
% 0.46/0.65         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.46/0.65          | ~ (v1_funct_1 @ X4)
% 0.46/0.65          | ~ (v1_relat_1 @ X4))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.65  thf('128', plain,
% 0.46/0.65      (![X10 : $i]:
% 0.46/0.65         (~ (v2_funct_1 @ X10)
% 0.46/0.65          | ((k2_funct_1 @ (k2_funct_1 @ X10)) = (X10))
% 0.46/0.65          | ~ (v1_funct_1 @ X10)
% 0.46/0.65          | ~ (v1_relat_1 @ X10))),
% 0.46/0.65      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.46/0.65  thf('129', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.65          | ~ (v2_funct_1 @ X0)
% 0.46/0.65          | ~ (v1_funct_1 @ X0)
% 0.46/0.65          | ~ (v1_relat_1 @ X0))),
% 0.46/0.65      inference('simplify', [status(thm)], ['124'])).
% 0.46/0.65  thf('130', plain,
% 0.46/0.65      (![X4 : $i]:
% 0.46/0.65         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 0.46/0.65          | ~ (v1_funct_1 @ X4)
% 0.46/0.65          | ~ (v1_relat_1 @ X4))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.65  thf('131', plain,
% 0.46/0.65      (![X4 : $i]:
% 0.46/0.65         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.46/0.65          | ~ (v1_funct_1 @ X4)
% 0.46/0.65          | ~ (v1_relat_1 @ X4))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.65  thf('132', plain,
% 0.46/0.65      (![X10 : $i]:
% 0.46/0.65         (~ (v2_funct_1 @ X10)
% 0.46/0.65          | ((k2_funct_1 @ (k2_funct_1 @ X10)) = (X10))
% 0.46/0.65          | ~ (v1_funct_1 @ X10)
% 0.46/0.65          | ~ (v1_relat_1 @ X10))),
% 0.46/0.65      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.46/0.65  thf('133', plain,
% 0.46/0.65      (![X9 : $i]:
% 0.46/0.65         (~ (v2_funct_1 @ X9)
% 0.46/0.65          | ((k5_relat_1 @ X9 @ (k2_funct_1 @ X9))
% 0.46/0.65              = (k6_relat_1 @ (k1_relat_1 @ X9)))
% 0.46/0.65          | ~ (v1_funct_1 @ X9)
% 0.46/0.65          | ~ (v1_relat_1 @ X9))),
% 0.46/0.65      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.46/0.65  thf('134', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.46/0.65            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.46/0.65          | ~ (v1_relat_1 @ X0)
% 0.46/0.65          | ~ (v1_funct_1 @ X0)
% 0.46/0.65          | ~ (v2_funct_1 @ X0)
% 0.46/0.65          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.65          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.65          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['132', '133'])).
% 0.46/0.65  thf('135', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ X0)
% 0.46/0.65          | ~ (v1_funct_1 @ X0)
% 0.46/0.65          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.65          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.65          | ~ (v2_funct_1 @ X0)
% 0.46/0.65          | ~ (v1_funct_1 @ X0)
% 0.46/0.65          | ~ (v1_relat_1 @ X0)
% 0.46/0.65          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.46/0.65              = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['131', '134'])).
% 0.46/0.65  thf('136', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.46/0.65            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.46/0.65          | ~ (v2_funct_1 @ X0)
% 0.46/0.65          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.65          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.65          | ~ (v1_funct_1 @ X0)
% 0.46/0.65          | ~ (v1_relat_1 @ X0))),
% 0.46/0.65      inference('simplify', [status(thm)], ['135'])).
% 0.46/0.65  thf('137', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ X0)
% 0.46/0.65          | ~ (v1_funct_1 @ X0)
% 0.46/0.65          | ~ (v1_relat_1 @ X0)
% 0.46/0.65          | ~ (v1_funct_1 @ X0)
% 0.46/0.65          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.65          | ~ (v2_funct_1 @ X0)
% 0.46/0.65          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.46/0.65              = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['130', '136'])).
% 0.46/0.65  thf('138', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.46/0.65            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.46/0.65          | ~ (v2_funct_1 @ X0)
% 0.46/0.65          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.65          | ~ (v1_funct_1 @ X0)
% 0.46/0.65          | ~ (v1_relat_1 @ X0))),
% 0.46/0.65      inference('simplify', [status(thm)], ['137'])).
% 0.46/0.65  thf('139', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (v1_relat_1 @ X0)
% 0.46/0.65          | ~ (v1_funct_1 @ X0)
% 0.46/0.65          | ~ (v2_funct_1 @ X0)
% 0.46/0.65          | ~ (v1_relat_1 @ X0)
% 0.46/0.65          | ~ (v1_funct_1 @ X0)
% 0.46/0.65          | ~ (v2_funct_1 @ X0)
% 0.46/0.65          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.46/0.65              = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['129', '138'])).
% 0.46/0.65  thf('140', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.46/0.66            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['139'])).
% 0.46/0.66  thf('141', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.46/0.66            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['128', '140'])).
% 0.46/0.66  thf('142', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.46/0.66              = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['127', '141'])).
% 0.46/0.66  thf('143', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.46/0.66            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['142'])).
% 0.46/0.66  thf('144', plain,
% 0.46/0.66      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.66        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.66        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.66        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.46/0.66            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['126', '143'])).
% 0.46/0.66  thf('145', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['21', '22'])).
% 0.46/0.66  thf('146', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('147', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('148', plain,
% 0.46/0.66      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.66        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.46/0.66            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))))),
% 0.46/0.66      inference('demod', [status(thm)], ['144', '145', '146', '147'])).
% 0.46/0.66  thf('149', plain,
% 0.46/0.66      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.66        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.66        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.46/0.66            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['125', '148'])).
% 0.46/0.66  thf('150', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['21', '22'])).
% 0.46/0.66  thf('151', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('152', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('153', plain,
% 0.46/0.66      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.46/0.66         = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.46/0.66      inference('demod', [status(thm)], ['149', '150', '151', '152'])).
% 0.46/0.66  thf('154', plain,
% 0.46/0.66      ((((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.46/0.66          = (k6_relat_1 @ (k1_relat_1 @ sk_C)))
% 0.46/0.66        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.66        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.66      inference('sup+', [status(thm)], ['110', '153'])).
% 0.46/0.66  thf('155', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['37', '38'])).
% 0.46/0.66  thf('156', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['21', '22'])).
% 0.46/0.66  thf('157', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('158', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('159', plain,
% 0.46/0.66      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.46/0.66         = (k6_relat_1 @ (k2_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['154', '155', '156', '157', '158'])).
% 0.46/0.66  thf('160', plain,
% 0.46/0.66      (![X5 : $i, X6 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X5)
% 0.46/0.66          | ~ (v1_funct_1 @ X5)
% 0.46/0.66          | (v2_funct_1 @ X6)
% 0.46/0.66          | ((k2_relat_1 @ X5) != (k1_relat_1 @ X6))
% 0.46/0.66          | ~ (v2_funct_1 @ (k5_relat_1 @ X5 @ X6))
% 0.46/0.66          | ~ (v1_funct_1 @ X6)
% 0.46/0.66          | ~ (v1_relat_1 @ X6))),
% 0.46/0.66      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.46/0.66  thf('161', plain,
% 0.46/0.66      ((~ (v2_funct_1 @ (k6_relat_1 @ (k2_struct_0 @ sk_A)))
% 0.46/0.66        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.66        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.66        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.66        | (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.66        | ~ (v1_relat_1 @ sk_C))),
% 0.46/0.66      inference('sup-', [status(thm)], ['159', '160'])).
% 0.46/0.66  thf('162', plain, (![X7 : $i]: (v2_funct_1 @ (k6_relat_1 @ X7))),
% 0.46/0.66      inference('cnf', [status(esa)], [t52_funct_1])).
% 0.46/0.66  thf('163', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.66      inference('simplify', [status(thm)], ['97'])).
% 0.46/0.66  thf('164', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_C @ 
% 0.46/0.66        (k1_zfmisc_1 @ 
% 0.46/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(redefinition_k2_relset_1, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i]:
% 0.46/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.66       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.46/0.66  thf('165', plain,
% 0.46/0.66      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.46/0.66         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 0.46/0.66          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.46/0.66      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.46/0.66  thf('166', plain,
% 0.46/0.66      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66         = (k2_relat_1 @ sk_C))),
% 0.46/0.66      inference('sup-', [status(thm)], ['164', '165'])).
% 0.46/0.66  thf('167', plain,
% 0.46/0.66      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66         = (k2_struct_0 @ sk_B))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('168', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.66      inference('sup+', [status(thm)], ['166', '167'])).
% 0.46/0.66  thf('169', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('170', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['21', '22'])).
% 0.46/0.66  thf('171', plain,
% 0.46/0.66      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.66        | ((k2_struct_0 @ sk_B) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.66        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.66      inference('demod', [status(thm)],
% 0.46/0.66                ['161', '162', '163', '168', '169', '170'])).
% 0.46/0.66  thf('172', plain,
% 0.46/0.66      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.66        | (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.66        | ((k2_struct_0 @ sk_B) != (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['109', '171'])).
% 0.46/0.66  thf('173', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['21', '22'])).
% 0.46/0.66  thf('174', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('175', plain,
% 0.46/0.66      (((v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.66        | ((k2_struct_0 @ sk_B) != (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.46/0.66      inference('demod', [status(thm)], ['172', '173', '174'])).
% 0.46/0.66  thf('176', plain,
% 0.46/0.66      ((((k2_struct_0 @ sk_B) != (k2_relat_1 @ sk_C))
% 0.46/0.66        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.66        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.66        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['108', '175'])).
% 0.46/0.66  thf('177', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.66      inference('sup+', [status(thm)], ['166', '167'])).
% 0.46/0.66  thf('178', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['21', '22'])).
% 0.46/0.66  thf('179', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('180', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('181', plain,
% 0.46/0.66      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.46/0.66        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.66      inference('demod', [status(thm)], ['176', '177', '178', '179', '180'])).
% 0.46/0.66  thf('182', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.66      inference('simplify', [status(thm)], ['181'])).
% 0.46/0.66  thf('183', plain,
% 0.46/0.66      ((((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.66          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.66        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.66            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['89', '98', '107', '182'])).
% 0.46/0.66  thf('184', plain,
% 0.46/0.66      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.66        (k1_zfmisc_1 @ 
% 0.46/0.66         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.46/0.66      inference('simplify', [status(thm)], ['86'])).
% 0.46/0.66  thf('185', plain,
% 0.46/0.66      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.46/0.66         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 0.46/0.66          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.46/0.66      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.46/0.66  thf('186', plain,
% 0.46/0.66      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.66         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['184', '185'])).
% 0.46/0.66  thf('187', plain,
% 0.46/0.66      ((((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.66          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.66        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['183', '186'])).
% 0.46/0.66  thf('188', plain,
% 0.46/0.66      ((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))
% 0.46/0.66        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.66        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.66        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.66            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['78', '187'])).
% 0.46/0.66  thf('189', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['37', '38'])).
% 0.46/0.66  thf('190', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['21', '22'])).
% 0.46/0.66  thf('191', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('192', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('193', plain,
% 0.46/0.66      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.46/0.66        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.66            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.46/0.66      inference('demod', [status(thm)], ['188', '189', '190', '191', '192'])).
% 0.46/0.66  thf('194', plain,
% 0.46/0.66      (((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.66         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['193'])).
% 0.46/0.66  thf('195', plain,
% 0.46/0.66      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.66          (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['77', '194'])).
% 0.46/0.66  thf('196', plain,
% 0.46/0.66      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.66           sk_C)
% 0.46/0.66        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.66        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.66      inference('sup-', [status(thm)], ['0', '195'])).
% 0.46/0.66  thf('197', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_C @ 
% 0.46/0.66        (k1_zfmisc_1 @ 
% 0.46/0.66         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.66      inference('demod', [status(thm)], ['47', '48'])).
% 0.46/0.66  thf('198', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_C @ 
% 0.46/0.66        (k1_zfmisc_1 @ 
% 0.46/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(reflexivity_r2_funct_2, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.66     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.66         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.46/0.66         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.46/0.66         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.66       ( r2_funct_2 @ A @ B @ C @ C ) ))).
% 0.46/0.66  thf('199', plain,
% 0.46/0.66      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.46/0.66         ((r2_funct_2 @ X19 @ X20 @ X21 @ X21)
% 0.46/0.66          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.46/0.66          | ~ (v1_funct_2 @ X21 @ X19 @ X20)
% 0.46/0.66          | ~ (v1_funct_1 @ X21)
% 0.46/0.66          | ~ (v1_funct_1 @ X22)
% 0.46/0.66          | ~ (v1_funct_2 @ X22 @ X19 @ X20)
% 0.46/0.66          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.46/0.66      inference('cnf', [status(esa)], [reflexivity_r2_funct_2])).
% 0.46/0.66  thf('200', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X0 @ 
% 0.46/0.66             (k1_zfmisc_1 @ 
% 0.46/0.66              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.46/0.66          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ sk_C)
% 0.46/0.66          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.66          | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.66             sk_C))),
% 0.46/0.66      inference('sup-', [status(thm)], ['198', '199'])).
% 0.46/0.66  thf('201', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('202', plain,
% 0.46/0.66      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('203', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X0 @ 
% 0.46/0.66             (k1_zfmisc_1 @ 
% 0.46/0.66              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.46/0.66          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.66             sk_C))),
% 0.46/0.66      inference('demod', [status(thm)], ['200', '201', '202'])).
% 0.46/0.66  thf('204', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['34', '39'])).
% 0.46/0.66  thf('205', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['34', '39'])).
% 0.46/0.66  thf('206', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['34', '39'])).
% 0.46/0.66  thf('207', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X0 @ 
% 0.46/0.66             (k1_zfmisc_1 @ 
% 0.46/0.66              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.46/0.66          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.66             sk_C))),
% 0.46/0.66      inference('demod', [status(thm)], ['203', '204', '205', '206'])).
% 0.46/0.66  thf('208', plain,
% 0.46/0.66      (((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)
% 0.46/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.66        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['197', '207'])).
% 0.46/0.66  thf('209', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('210', plain,
% 0.46/0.66      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.66      inference('demod', [status(thm)], ['59', '60'])).
% 0.46/0.66  thf('211', plain,
% 0.46/0.66      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['208', '209', '210'])).
% 0.46/0.66  thf('212', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['21', '22'])).
% 0.46/0.66  thf('213', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('214', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('215', plain, ($false),
% 0.46/0.66      inference('demod', [status(thm)], ['196', '211', '212', '213', '214'])).
% 0.46/0.66  
% 0.46/0.66  % SZS output end Refutation
% 0.46/0.66  
% 0.46/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
