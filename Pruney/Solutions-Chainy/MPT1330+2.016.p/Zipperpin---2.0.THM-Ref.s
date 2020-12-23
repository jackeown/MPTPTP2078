%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4IFSSGHwbE

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:43 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 433 expanded)
%              Number of leaves         :   36 ( 135 expanded)
%              Depth                    :   22
%              Number of atoms          : 1231 (7341 expanded)
%              Number of equality atoms :  114 ( 612 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t52_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( ( ( k2_struct_0 @ B )
                    = k1_xboole_0 )
                 => ( ( k2_struct_0 @ A )
                    = k1_xboole_0 ) )
               => ( ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( k2_struct_0 @ B ) )
                  = ( k2_struct_0 @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_struct_0 @ A )
       => ! [B: $i] :
            ( ( l1_struct_0 @ B )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ( ( ( ( k2_struct_0 @ B )
                      = k1_xboole_0 )
                   => ( ( k2_struct_0 @ A )
                      = k1_xboole_0 ) )
                 => ( ( k8_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( k2_struct_0 @ B ) )
                    = ( k2_struct_0 @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t52_tops_2])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( v1_partfun1 @ X21 @ X22 )
      | ~ ( v1_funct_2 @ X21 @ X22 @ X23 )
      | ~ ( v1_funct_1 @ X21 )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('8',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_partfun1 @ X25 @ X24 )
      | ( ( k1_relat_1 @ X25 )
        = X24 )
      | ~ ( v4_relat_1 @ X25 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('9',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('14',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('16',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v4_relat_1 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('17',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','14','17'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('19',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('20',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['1','20'])).

thf('22',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('27',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','31'])).

thf('33',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v4_relat_1 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('34',plain,
    ( ( v4_relat_1 @ sk_C @ k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('35',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v4_relat_1 @ X8 @ X9 )
      | ( r1_tarski @ ( k1_relat_1 @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('36',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['12','13'])).

thf('38',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('39',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('40',plain,
    ( ( m1_subset_1 @ ( k1_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('41',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('42',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','31'])).

thf('44',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( v1_partfun1 @ X21 @ X22 )
      | ~ ( v1_funct_2 @ X21 @ X22 @ X23 )
      | ~ ( v1_funct_1 @ X21 )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('45',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_partfun1 @ sk_C @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('48',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('49',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( v1_funct_2 @ sk_C @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['47','52'])).

thf('54',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_partfun1 @ sk_C @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','46','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('56',plain,
    ( ( ( v1_partfun1 @ sk_C @ k1_xboole_0 )
      | ( ( u1_struct_0 @ sk_B )
        = k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_partfun1 @ sk_C @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','46','53'])).

thf('58',plain,
    ( ( ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_partfun1 @ sk_C @ k1_xboole_0 )
      | ( v1_partfun1 @ sk_C @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ( v1_partfun1 @ sk_C @ k1_xboole_0 )
      | ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_partfun1 @ X25 @ X24 )
      | ( ( k1_relat_1 @ X25 )
        = X24 )
      | ~ ( v4_relat_1 @ X25 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('61',plain,
    ( ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v4_relat_1 @ sk_C @ k1_xboole_0 )
      | ( ( k1_relat_1 @ sk_C )
        = k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['12','13'])).

thf('63',plain,
    ( ( v4_relat_1 @ sk_C @ k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('64',plain,
    ( ( ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ sk_C )
        = k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('66',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('67',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('68',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','71'])).

thf('73',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('74',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ( ( k8_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
       != k1_xboole_0 )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','74'])).

thf('76',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('79',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','31'])).

thf('80',plain,
    ( ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('83',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k8_relset_1 @ X18 @ X19 @ X20 @ X19 )
        = ( k1_relset_1 @ X18 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('84',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
      = ( k1_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('86',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('87',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
      = ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['84','87'])).

thf('89',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','88'])).

thf('90',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['64','89'])).

thf('91',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('93',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','88'])).

thf('95',plain,(
    ( k2_struct_0 @ sk_A )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('97',plain,(
    ( k2_struct_0 @ sk_B )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['95','96'])).

thf('98',plain,(
    ( k2_struct_0 @ sk_B )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['25','97'])).

thf('99',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['23','98'])).

thf('100',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['0','99'])).

thf('101',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('104',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X26: $i] :
      ( ( ( k2_struct_0 @ X26 )
        = ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('109',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('111',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k8_relset_1 @ X18 @ X19 @ X20 @ X19 )
        = ( k1_relset_1 @ X18 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('114',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('116',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('117',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['114','117'])).

thf('119',plain,(
    ( k1_relat_1 @ sk_C )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['107','118'])).

thf('120',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['102','119'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4IFSSGHwbE
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:20:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.57  % Solved by: fo/fo7.sh
% 0.22/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.57  % done 184 iterations in 0.078s
% 0.22/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.57  % SZS output start Refutation
% 0.22/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.57  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.22/0.57  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.57  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.22/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.57  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.22/0.57  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.22/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.57  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.22/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.57  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.22/0.57  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.22/0.57  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.22/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.57  thf(d3_struct_0, axiom,
% 0.22/0.57    (![A:$i]:
% 0.22/0.57     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.22/0.57  thf('0', plain,
% 0.22/0.57      (![X26 : $i]:
% 0.22/0.57         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.22/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.57  thf('1', plain,
% 0.22/0.57      (![X26 : $i]:
% 0.22/0.57         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.22/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.57  thf(t52_tops_2, conjecture,
% 0.22/0.57    (![A:$i]:
% 0.22/0.57     ( ( l1_struct_0 @ A ) =>
% 0.22/0.57       ( ![B:$i]:
% 0.22/0.57         ( ( l1_struct_0 @ B ) =>
% 0.22/0.57           ( ![C:$i]:
% 0.22/0.57             ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.57                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.57                 ( m1_subset_1 @
% 0.22/0.57                   C @ 
% 0.22/0.57                   ( k1_zfmisc_1 @
% 0.22/0.57                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.57               ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.22/0.57                   ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.22/0.57                 ( ( k8_relset_1 @
% 0.22/0.57                     ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.22/0.57                     ( k2_struct_0 @ B ) ) =
% 0.22/0.57                   ( k2_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.22/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.57    (~( ![A:$i]:
% 0.22/0.57        ( ( l1_struct_0 @ A ) =>
% 0.22/0.57          ( ![B:$i]:
% 0.22/0.57            ( ( l1_struct_0 @ B ) =>
% 0.22/0.57              ( ![C:$i]:
% 0.22/0.57                ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.57                    ( v1_funct_2 @
% 0.22/0.57                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.57                    ( m1_subset_1 @
% 0.22/0.57                      C @ 
% 0.22/0.57                      ( k1_zfmisc_1 @
% 0.22/0.57                        ( k2_zfmisc_1 @
% 0.22/0.57                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.57                  ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.22/0.57                      ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.22/0.57                    ( ( k8_relset_1 @
% 0.22/0.57                        ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.22/0.57                        ( k2_struct_0 @ B ) ) =
% 0.22/0.57                      ( k2_struct_0 @ A ) ) ) ) ) ) ) ) )),
% 0.22/0.57    inference('cnf.neg', [status(esa)], [t52_tops_2])).
% 0.22/0.57  thf('2', plain,
% 0.22/0.57      ((m1_subset_1 @ sk_C @ 
% 0.22/0.57        (k1_zfmisc_1 @ 
% 0.22/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(cc5_funct_2, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.22/0.57       ( ![C:$i]:
% 0.22/0.57         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.57           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.22/0.57             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.22/0.57  thf('3', plain,
% 0.22/0.57      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.22/0.57         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.22/0.57          | (v1_partfun1 @ X21 @ X22)
% 0.22/0.57          | ~ (v1_funct_2 @ X21 @ X22 @ X23)
% 0.22/0.57          | ~ (v1_funct_1 @ X21)
% 0.22/0.57          | (v1_xboole_0 @ X23))),
% 0.22/0.57      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.22/0.57  thf('4', plain,
% 0.22/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.22/0.57        | ~ (v1_funct_1 @ sk_C)
% 0.22/0.57        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.22/0.57        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.57  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('6', plain,
% 0.22/0.57      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('7', plain,
% 0.22/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.22/0.57        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.22/0.57      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.22/0.57  thf(d4_partfun1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.22/0.57       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.22/0.57  thf('8', plain,
% 0.22/0.57      (![X24 : $i, X25 : $i]:
% 0.22/0.57         (~ (v1_partfun1 @ X25 @ X24)
% 0.22/0.57          | ((k1_relat_1 @ X25) = (X24))
% 0.22/0.57          | ~ (v4_relat_1 @ X25 @ X24)
% 0.22/0.57          | ~ (v1_relat_1 @ X25))),
% 0.22/0.57      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.22/0.57  thf('9', plain,
% 0.22/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.22/0.57        | ~ (v1_relat_1 @ sk_C)
% 0.22/0.57        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.22/0.57        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.57  thf('10', plain,
% 0.22/0.57      ((m1_subset_1 @ sk_C @ 
% 0.22/0.57        (k1_zfmisc_1 @ 
% 0.22/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(cc2_relat_1, axiom,
% 0.22/0.57    (![A:$i]:
% 0.22/0.57     ( ( v1_relat_1 @ A ) =>
% 0.22/0.57       ( ![B:$i]:
% 0.22/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.22/0.57  thf('11', plain,
% 0.22/0.57      (![X6 : $i, X7 : $i]:
% 0.22/0.57         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.22/0.57          | (v1_relat_1 @ X6)
% 0.22/0.57          | ~ (v1_relat_1 @ X7))),
% 0.22/0.57      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.22/0.57  thf('12', plain,
% 0.22/0.57      ((~ (v1_relat_1 @ 
% 0.22/0.57           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.22/0.57        | (v1_relat_1 @ sk_C))),
% 0.22/0.57      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.57  thf(fc6_relat_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.22/0.57  thf('13', plain,
% 0.22/0.57      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 0.22/0.57      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.22/0.57  thf('14', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.57      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.57  thf('15', plain,
% 0.22/0.57      ((m1_subset_1 @ sk_C @ 
% 0.22/0.57        (k1_zfmisc_1 @ 
% 0.22/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(cc2_relset_1, axiom,
% 0.22/0.57    (![A:$i,B:$i,C:$i]:
% 0.22/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.57       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.22/0.57  thf('16', plain,
% 0.22/0.57      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.57         ((v4_relat_1 @ X12 @ X13)
% 0.22/0.57          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.22/0.57      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.57  thf('17', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.22/0.57      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.57  thf('18', plain,
% 0.22/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.22/0.57        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.22/0.57      inference('demod', [status(thm)], ['9', '14', '17'])).
% 0.22/0.57  thf(l13_xboole_0, axiom,
% 0.22/0.57    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.57  thf('19', plain,
% 0.22/0.57      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.57      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.22/0.57  thf('20', plain,
% 0.22/0.57      ((((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))
% 0.22/0.57        | ((u1_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.57  thf('21', plain,
% 0.22/0.57      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.22/0.57        | ~ (l1_struct_0 @ sk_B)
% 0.22/0.57        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.22/0.57      inference('sup+', [status(thm)], ['1', '20'])).
% 0.22/0.57  thf('22', plain, ((l1_struct_0 @ sk_B)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('23', plain,
% 0.22/0.57      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.22/0.57        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.22/0.57      inference('demod', [status(thm)], ['21', '22'])).
% 0.22/0.57  thf('24', plain,
% 0.22/0.57      ((((k2_struct_0 @ sk_A) = (k1_xboole_0))
% 0.22/0.57        | ((k2_struct_0 @ sk_B) != (k1_xboole_0)))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('25', plain,
% 0.22/0.57      ((((k2_struct_0 @ sk_B) != (k1_xboole_0)))
% 0.22/0.57         <= (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0))))),
% 0.22/0.57      inference('split', [status(esa)], ['24'])).
% 0.22/0.57  thf('26', plain,
% 0.22/0.57      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.22/0.57         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('split', [status(esa)], ['24'])).
% 0.22/0.57  thf('27', plain,
% 0.22/0.57      (![X26 : $i]:
% 0.22/0.57         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.22/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.57  thf('28', plain,
% 0.22/0.57      ((m1_subset_1 @ sk_C @ 
% 0.22/0.57        (k1_zfmisc_1 @ 
% 0.22/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('29', plain,
% 0.22/0.57      (((m1_subset_1 @ sk_C @ 
% 0.22/0.57         (k1_zfmisc_1 @ 
% 0.22/0.57          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.22/0.57        | ~ (l1_struct_0 @ sk_A))),
% 0.22/0.57      inference('sup+', [status(thm)], ['27', '28'])).
% 0.22/0.57  thf('30', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('31', plain,
% 0.22/0.57      ((m1_subset_1 @ sk_C @ 
% 0.22/0.57        (k1_zfmisc_1 @ 
% 0.22/0.57         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.57      inference('demod', [status(thm)], ['29', '30'])).
% 0.22/0.57  thf('32', plain,
% 0.22/0.57      (((m1_subset_1 @ sk_C @ 
% 0.22/0.57         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))))
% 0.22/0.57         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('sup+', [status(thm)], ['26', '31'])).
% 0.22/0.57  thf('33', plain,
% 0.22/0.57      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.57         ((v4_relat_1 @ X12 @ X13)
% 0.22/0.57          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.22/0.57      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.57  thf('34', plain,
% 0.22/0.57      (((v4_relat_1 @ sk_C @ k1_xboole_0))
% 0.22/0.57         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.57  thf(d18_relat_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( v1_relat_1 @ B ) =>
% 0.22/0.57       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.57  thf('35', plain,
% 0.22/0.57      (![X8 : $i, X9 : $i]:
% 0.22/0.57         (~ (v4_relat_1 @ X8 @ X9)
% 0.22/0.57          | (r1_tarski @ (k1_relat_1 @ X8) @ X9)
% 0.22/0.57          | ~ (v1_relat_1 @ X8))),
% 0.22/0.57      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.22/0.57  thf('36', plain,
% 0.22/0.57      (((~ (v1_relat_1 @ sk_C)
% 0.22/0.57         | (r1_tarski @ (k1_relat_1 @ sk_C) @ k1_xboole_0)))
% 0.22/0.57         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('sup-', [status(thm)], ['34', '35'])).
% 0.22/0.57  thf('37', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.57      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.57  thf('38', plain,
% 0.22/0.57      (((r1_tarski @ (k1_relat_1 @ sk_C) @ k1_xboole_0))
% 0.22/0.57         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('demod', [status(thm)], ['36', '37'])).
% 0.22/0.57  thf(t3_subset, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.57  thf('39', plain,
% 0.22/0.57      (![X3 : $i, X5 : $i]:
% 0.22/0.57         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.22/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.57  thf('40', plain,
% 0.22/0.57      (((m1_subset_1 @ (k1_relat_1 @ sk_C) @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.22/0.57         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('sup-', [status(thm)], ['38', '39'])).
% 0.22/0.57  thf(cc1_subset_1, axiom,
% 0.22/0.57    (![A:$i]:
% 0.22/0.57     ( ( v1_xboole_0 @ A ) =>
% 0.22/0.57       ( ![B:$i]:
% 0.22/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.22/0.57  thf('41', plain,
% 0.22/0.57      (![X1 : $i, X2 : $i]:
% 0.22/0.57         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.22/0.57          | (v1_xboole_0 @ X1)
% 0.22/0.57          | ~ (v1_xboole_0 @ X2))),
% 0.22/0.57      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.22/0.57  thf('42', plain,
% 0.22/0.57      (((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ (k1_relat_1 @ sk_C))))
% 0.22/0.57         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('sup-', [status(thm)], ['40', '41'])).
% 0.22/0.57  thf('43', plain,
% 0.22/0.57      (((m1_subset_1 @ sk_C @ 
% 0.22/0.57         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))))
% 0.22/0.57         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('sup+', [status(thm)], ['26', '31'])).
% 0.22/0.57  thf('44', plain,
% 0.22/0.57      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.22/0.57         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.22/0.57          | (v1_partfun1 @ X21 @ X22)
% 0.22/0.57          | ~ (v1_funct_2 @ X21 @ X22 @ X23)
% 0.22/0.57          | ~ (v1_funct_1 @ X21)
% 0.22/0.57          | (v1_xboole_0 @ X23))),
% 0.22/0.57      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.22/0.57  thf('45', plain,
% 0.22/0.57      ((((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.22/0.57         | ~ (v1_funct_1 @ sk_C)
% 0.22/0.57         | ~ (v1_funct_2 @ sk_C @ k1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.22/0.57         | (v1_partfun1 @ sk_C @ k1_xboole_0)))
% 0.22/0.57         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('sup-', [status(thm)], ['43', '44'])).
% 0.22/0.57  thf('46', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('47', plain,
% 0.22/0.57      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.22/0.57         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('split', [status(esa)], ['24'])).
% 0.22/0.57  thf('48', plain,
% 0.22/0.57      (![X26 : $i]:
% 0.22/0.57         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.22/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.57  thf('49', plain,
% 0.22/0.57      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('50', plain,
% 0.22/0.57      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.22/0.57        | ~ (l1_struct_0 @ sk_A))),
% 0.22/0.57      inference('sup+', [status(thm)], ['48', '49'])).
% 0.22/0.57  thf('51', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('52', plain,
% 0.22/0.57      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.22/0.57      inference('demod', [status(thm)], ['50', '51'])).
% 0.22/0.57  thf('53', plain,
% 0.22/0.57      (((v1_funct_2 @ sk_C @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))
% 0.22/0.57         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('sup+', [status(thm)], ['47', '52'])).
% 0.22/0.57  thf('54', plain,
% 0.22/0.57      ((((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.22/0.57         | (v1_partfun1 @ sk_C @ k1_xboole_0)))
% 0.22/0.57         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('demod', [status(thm)], ['45', '46', '53'])).
% 0.22/0.57  thf('55', plain,
% 0.22/0.57      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.57      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.22/0.57  thf('56', plain,
% 0.22/0.57      ((((v1_partfun1 @ sk_C @ k1_xboole_0)
% 0.22/0.57         | ((u1_struct_0 @ sk_B) = (k1_xboole_0))))
% 0.22/0.57         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('sup-', [status(thm)], ['54', '55'])).
% 0.22/0.57  thf('57', plain,
% 0.22/0.57      ((((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.22/0.57         | (v1_partfun1 @ sk_C @ k1_xboole_0)))
% 0.22/0.57         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('demod', [status(thm)], ['45', '46', '53'])).
% 0.22/0.57  thf('58', plain,
% 0.22/0.57      ((((v1_xboole_0 @ k1_xboole_0)
% 0.22/0.57         | (v1_partfun1 @ sk_C @ k1_xboole_0)
% 0.22/0.57         | (v1_partfun1 @ sk_C @ k1_xboole_0)))
% 0.22/0.57         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('sup+', [status(thm)], ['56', '57'])).
% 0.22/0.57  thf('59', plain,
% 0.22/0.57      ((((v1_partfun1 @ sk_C @ k1_xboole_0) | (v1_xboole_0 @ k1_xboole_0)))
% 0.22/0.57         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('simplify', [status(thm)], ['58'])).
% 0.22/0.57  thf('60', plain,
% 0.22/0.57      (![X24 : $i, X25 : $i]:
% 0.22/0.57         (~ (v1_partfun1 @ X25 @ X24)
% 0.22/0.57          | ((k1_relat_1 @ X25) = (X24))
% 0.22/0.57          | ~ (v4_relat_1 @ X25 @ X24)
% 0.22/0.57          | ~ (v1_relat_1 @ X25))),
% 0.22/0.57      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.22/0.57  thf('61', plain,
% 0.22/0.57      ((((v1_xboole_0 @ k1_xboole_0)
% 0.22/0.57         | ~ (v1_relat_1 @ sk_C)
% 0.22/0.57         | ~ (v4_relat_1 @ sk_C @ k1_xboole_0)
% 0.22/0.57         | ((k1_relat_1 @ sk_C) = (k1_xboole_0))))
% 0.22/0.57         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('sup-', [status(thm)], ['59', '60'])).
% 0.22/0.57  thf('62', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.57      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.57  thf('63', plain,
% 0.22/0.57      (((v4_relat_1 @ sk_C @ k1_xboole_0))
% 0.22/0.57         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.57  thf('64', plain,
% 0.22/0.57      ((((v1_xboole_0 @ k1_xboole_0) | ((k1_relat_1 @ sk_C) = (k1_xboole_0))))
% 0.22/0.57         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.22/0.57  thf('65', plain,
% 0.22/0.57      (![X26 : $i]:
% 0.22/0.57         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.22/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.57  thf('66', plain,
% 0.22/0.57      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.22/0.57         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('split', [status(esa)], ['24'])).
% 0.22/0.57  thf('67', plain,
% 0.22/0.57      (![X26 : $i]:
% 0.22/0.57         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.22/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.57  thf('68', plain,
% 0.22/0.57      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.22/0.57         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('69', plain,
% 0.22/0.57      ((((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.22/0.57          (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))
% 0.22/0.57        | ~ (l1_struct_0 @ sk_A))),
% 0.22/0.57      inference('sup-', [status(thm)], ['67', '68'])).
% 0.22/0.57  thf('70', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('71', plain,
% 0.22/0.57      (((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.22/0.57         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.22/0.57      inference('demod', [status(thm)], ['69', '70'])).
% 0.22/0.57  thf('72', plain,
% 0.22/0.57      ((((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.22/0.57          (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A)))
% 0.22/0.57         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('sup-', [status(thm)], ['66', '71'])).
% 0.22/0.57  thf('73', plain,
% 0.22/0.57      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.22/0.57         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('split', [status(esa)], ['24'])).
% 0.22/0.57  thf('74', plain,
% 0.22/0.57      ((((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.22/0.57          (k2_struct_0 @ sk_B)) != (k1_xboole_0)))
% 0.22/0.57         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('demod', [status(thm)], ['72', '73'])).
% 0.22/0.57  thf('75', plain,
% 0.22/0.57      (((((k8_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.22/0.57           (k2_struct_0 @ sk_B)) != (k1_xboole_0))
% 0.22/0.57         | ~ (l1_struct_0 @ sk_B)))
% 0.22/0.57         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('sup-', [status(thm)], ['65', '74'])).
% 0.22/0.57  thf('76', plain, ((l1_struct_0 @ sk_B)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('77', plain,
% 0.22/0.57      ((((k8_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.22/0.57          (k2_struct_0 @ sk_B)) != (k1_xboole_0)))
% 0.22/0.57         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('demod', [status(thm)], ['75', '76'])).
% 0.22/0.57  thf('78', plain,
% 0.22/0.57      (![X26 : $i]:
% 0.22/0.57         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.22/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.57  thf('79', plain,
% 0.22/0.57      (((m1_subset_1 @ sk_C @ 
% 0.22/0.57         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B)))))
% 0.22/0.57         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('sup+', [status(thm)], ['26', '31'])).
% 0.22/0.57  thf('80', plain,
% 0.22/0.57      ((((m1_subset_1 @ sk_C @ 
% 0.22/0.57          (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B))))
% 0.22/0.57         | ~ (l1_struct_0 @ sk_B)))
% 0.22/0.57         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('sup+', [status(thm)], ['78', '79'])).
% 0.22/0.57  thf('81', plain, ((l1_struct_0 @ sk_B)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('82', plain,
% 0.22/0.57      (((m1_subset_1 @ sk_C @ 
% 0.22/0.57         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B)))))
% 0.22/0.57         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('demod', [status(thm)], ['80', '81'])).
% 0.22/0.57  thf(t38_relset_1, axiom,
% 0.22/0.57    (![A:$i,B:$i,C:$i]:
% 0.22/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.57       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.22/0.57         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.22/0.57  thf('83', plain,
% 0.22/0.57      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.57         (((k8_relset_1 @ X18 @ X19 @ X20 @ X19)
% 0.22/0.57            = (k1_relset_1 @ X18 @ X19 @ X20))
% 0.22/0.57          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.22/0.57      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.22/0.57  thf('84', plain,
% 0.22/0.57      ((((k8_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.22/0.57          (k2_struct_0 @ sk_B))
% 0.22/0.57          = (k1_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C)))
% 0.22/0.57         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('sup-', [status(thm)], ['82', '83'])).
% 0.22/0.57  thf('85', plain,
% 0.22/0.57      (((m1_subset_1 @ sk_C @ 
% 0.22/0.57         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B)))))
% 0.22/0.57         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('demod', [status(thm)], ['80', '81'])).
% 0.22/0.57  thf(redefinition_k1_relset_1, axiom,
% 0.22/0.57    (![A:$i,B:$i,C:$i]:
% 0.22/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.57       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.22/0.57  thf('86', plain,
% 0.22/0.57      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.22/0.57         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 0.22/0.57          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.22/0.57      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.22/0.57  thf('87', plain,
% 0.22/0.57      ((((k1_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.22/0.57          = (k1_relat_1 @ sk_C)))
% 0.22/0.57         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('sup-', [status(thm)], ['85', '86'])).
% 0.22/0.57  thf('88', plain,
% 0.22/0.57      ((((k8_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.22/0.57          (k2_struct_0 @ sk_B)) = (k1_relat_1 @ sk_C)))
% 0.22/0.57         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('demod', [status(thm)], ['84', '87'])).
% 0.22/0.57  thf('89', plain,
% 0.22/0.57      ((((k1_relat_1 @ sk_C) != (k1_xboole_0)))
% 0.22/0.57         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('demod', [status(thm)], ['77', '88'])).
% 0.22/0.57  thf('90', plain,
% 0.22/0.57      (((v1_xboole_0 @ k1_xboole_0))
% 0.22/0.57         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('simplify_reflect-', [status(thm)], ['64', '89'])).
% 0.22/0.57  thf('91', plain,
% 0.22/0.57      (((v1_xboole_0 @ (k1_relat_1 @ sk_C)))
% 0.22/0.57         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('demod', [status(thm)], ['42', '90'])).
% 0.22/0.57  thf('92', plain,
% 0.22/0.57      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.57      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.22/0.57  thf('93', plain,
% 0.22/0.57      ((((k1_relat_1 @ sk_C) = (k1_xboole_0)))
% 0.22/0.57         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('sup-', [status(thm)], ['91', '92'])).
% 0.22/0.57  thf('94', plain,
% 0.22/0.57      ((((k1_relat_1 @ sk_C) != (k1_xboole_0)))
% 0.22/0.57         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.57      inference('demod', [status(thm)], ['77', '88'])).
% 0.22/0.57  thf('95', plain, (~ (((k2_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.22/0.57      inference('simplify_reflect-', [status(thm)], ['93', '94'])).
% 0.22/0.57  thf('96', plain,
% 0.22/0.57      (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0))) | 
% 0.22/0.57       (((k2_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.22/0.57      inference('split', [status(esa)], ['24'])).
% 0.22/0.57  thf('97', plain, (~ (((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.22/0.57      inference('sat_resolution*', [status(thm)], ['95', '96'])).
% 0.22/0.57  thf('98', plain, (((k2_struct_0 @ sk_B) != (k1_xboole_0))),
% 0.22/0.57      inference('simpl_trail', [status(thm)], ['25', '97'])).
% 0.22/0.57  thf('99', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.22/0.57      inference('simplify_reflect-', [status(thm)], ['23', '98'])).
% 0.22/0.57  thf('100', plain,
% 0.22/0.57      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.22/0.57      inference('sup+', [status(thm)], ['0', '99'])).
% 0.22/0.57  thf('101', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('102', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.22/0.57      inference('demod', [status(thm)], ['100', '101'])).
% 0.22/0.57  thf('103', plain,
% 0.22/0.57      (![X26 : $i]:
% 0.22/0.57         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.22/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.57  thf('104', plain,
% 0.22/0.57      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.22/0.57         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('105', plain,
% 0.22/0.57      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.22/0.57          (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))
% 0.22/0.57        | ~ (l1_struct_0 @ sk_B))),
% 0.22/0.57      inference('sup-', [status(thm)], ['103', '104'])).
% 0.22/0.57  thf('106', plain, ((l1_struct_0 @ sk_B)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('107', plain,
% 0.22/0.57      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.22/0.57         (k2_struct_0 @ sk_B)) != (k2_struct_0 @ sk_A))),
% 0.22/0.57      inference('demod', [status(thm)], ['105', '106'])).
% 0.22/0.57  thf('108', plain,
% 0.22/0.57      (![X26 : $i]:
% 0.22/0.57         (((k2_struct_0 @ X26) = (u1_struct_0 @ X26)) | ~ (l1_struct_0 @ X26))),
% 0.22/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.57  thf('109', plain,
% 0.22/0.57      ((m1_subset_1 @ sk_C @ 
% 0.22/0.57        (k1_zfmisc_1 @ 
% 0.22/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('110', plain,
% 0.22/0.57      (((m1_subset_1 @ sk_C @ 
% 0.22/0.57         (k1_zfmisc_1 @ 
% 0.22/0.57          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.22/0.57        | ~ (l1_struct_0 @ sk_B))),
% 0.22/0.57      inference('sup+', [status(thm)], ['108', '109'])).
% 0.22/0.57  thf('111', plain, ((l1_struct_0 @ sk_B)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('112', plain,
% 0.22/0.57      ((m1_subset_1 @ sk_C @ 
% 0.22/0.57        (k1_zfmisc_1 @ 
% 0.22/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.22/0.57      inference('demod', [status(thm)], ['110', '111'])).
% 0.22/0.57  thf('113', plain,
% 0.22/0.57      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.57         (((k8_relset_1 @ X18 @ X19 @ X20 @ X19)
% 0.22/0.57            = (k1_relset_1 @ X18 @ X19 @ X20))
% 0.22/0.57          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.22/0.57      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.22/0.57  thf('114', plain,
% 0.22/0.57      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.22/0.57         (k2_struct_0 @ sk_B))
% 0.22/0.57         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))),
% 0.22/0.57      inference('sup-', [status(thm)], ['112', '113'])).
% 0.22/0.57  thf('115', plain,
% 0.22/0.57      ((m1_subset_1 @ sk_C @ 
% 0.22/0.57        (k1_zfmisc_1 @ 
% 0.22/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.22/0.57      inference('demod', [status(thm)], ['110', '111'])).
% 0.22/0.57  thf('116', plain,
% 0.22/0.57      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.22/0.57         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 0.22/0.57          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.22/0.57      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.22/0.57  thf('117', plain,
% 0.22/0.57      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.22/0.57         = (k1_relat_1 @ sk_C))),
% 0.22/0.57      inference('sup-', [status(thm)], ['115', '116'])).
% 0.22/0.57  thf('118', plain,
% 0.22/0.57      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 0.22/0.57         (k2_struct_0 @ sk_B)) = (k1_relat_1 @ sk_C))),
% 0.22/0.57      inference('demod', [status(thm)], ['114', '117'])).
% 0.22/0.57  thf('119', plain, (((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))),
% 0.22/0.57      inference('demod', [status(thm)], ['107', '118'])).
% 0.22/0.57  thf('120', plain, ($false),
% 0.22/0.57      inference('simplify_reflect-', [status(thm)], ['102', '119'])).
% 0.22/0.57  
% 0.22/0.57  % SZS output end Refutation
% 0.22/0.57  
% 0.22/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
