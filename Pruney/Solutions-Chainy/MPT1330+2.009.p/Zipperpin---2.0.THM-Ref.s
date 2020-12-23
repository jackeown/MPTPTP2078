%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pauxewaIII

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:42 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  190 (1229 expanded)
%              Number of leaves         :   39 ( 363 expanded)
%              Depth                    :   27
%              Number of atoms          : 1498 (19908 expanded)
%              Number of equality atoms :  131 (1588 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
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
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('4',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r1_tarski @ sk_C @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf('6',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( r1_tarski @ sk_C @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) ) )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['0','7'])).

thf('9',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X1: $i,X3: $i] :
      ( ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('14',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('19',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( v1_partfun1 @ X27 @ X28 )
      | ~ ( v1_funct_2 @ X27 @ X28 @ X29 )
      | ~ ( v1_funct_1 @ X27 )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('20',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('23',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21','26'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('28',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v1_partfun1 @ X31 @ X30 )
      | ( ( k1_relat_1 @ X31 )
        = X30 )
      | ~ ( v4_relat_1 @ X31 @ X30 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('31',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('32',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('34',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v4_relat_1 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('35',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','32','35'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('37',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('38',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k2_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B_1 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['13','38'])).

thf('40',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( ( k2_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( ( k2_struct_0 @ sk_B_1 )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['42'])).

thf('44',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['42'])).

thf('45',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('46',plain,
    ( ( r1_tarski @ sk_C @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X1: $i,X3: $i] :
      ( ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('48',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( v1_partfun1 @ X27 @ X28 )
      | ~ ( v1_funct_2 @ X27 @ X28 @ X29 )
      | ~ ( v1_funct_1 @ X27 )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('50',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ k1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v1_partfun1 @ sk_C @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['42'])).

thf('53',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('54',plain,
    ( ( v1_funct_2 @ sk_C @ k1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v1_partfun1 @ sk_C @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['50','51','54'])).

thf(t6_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i,G: $i] :
                  ( ( ( r2_hidden @ C @ D )
                    & ( r2_hidden @ D @ E )
                    & ( r2_hidden @ E @ F )
                    & ( r2_hidden @ F @ G )
                    & ( r2_hidden @ G @ B ) )
                 => ( r1_xboole_0 @ C @ A ) ) ) ) )).

thf('56',plain,(
    ! [X21: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X21 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('58',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('59',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v4_relat_1 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('60',plain,
    ( ( v4_relat_1 @ sk_C @ k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('61',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v4_relat_1 @ X7 @ X8 )
      | ( r1_tarski @ ( k1_relat_1 @ X7 ) @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('62',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['30','31'])).

thf('64',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X1: $i,X3: $i] :
      ( ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('66',plain,
    ( ( m1_subset_1 @ ( k1_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('67',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('68',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_C ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','68'])).

thf('70',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_C ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,
    ( ! [X0: $i] :
        ( ( ( k1_relat_1 @ sk_C )
          = k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','70'])).

thf('72',plain,
    ( ( ( v1_partfun1 @ sk_C @ k1_xboole_0 )
      | ( ( k1_relat_1 @ sk_C )
        = k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','71'])).

thf('73',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v1_partfun1 @ X31 @ X30 )
      | ( ( k1_relat_1 @ X31 )
        = X30 )
      | ~ ( v4_relat_1 @ X31 @ X30 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('74',plain,
    ( ( ( ( k1_relat_1 @ sk_C )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v4_relat_1 @ sk_C @ k1_xboole_0 )
      | ( ( k1_relat_1 @ sk_C )
        = k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['30','31'])).

thf('76',plain,
    ( ( v4_relat_1 @ sk_C @ k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('77',plain,
    ( ( ( ( k1_relat_1 @ sk_C )
        = k1_xboole_0 )
      | ( ( k1_relat_1 @ sk_C )
        = k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('80',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['42'])).

thf('81',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('82',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['80','85'])).

thf('87',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['42'])).

thf('88',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( ( ( k8_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
       != k1_xboole_0 )
      | ~ ( l1_struct_0 @ sk_B_1 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['79','88'])).

thf('90',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('93',plain,
    ( ( r1_tarski @ sk_C @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('94',plain,
    ( ( ( r1_tarski @ sk_C @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) ) )
      | ~ ( l1_struct_0 @ sk_B_1 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( r1_tarski @ sk_C @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X1: $i,X3: $i] :
      ( ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('98',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('99',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k8_relset_1 @ X18 @ X19 @ X20 @ X19 )
        = ( k1_relset_1 @ X18 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('100',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
      = ( k1_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('102',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('103',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) @ sk_C )
      = ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
      = ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['100','103'])).

thf('105',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['91','104'])).

thf('106',plain,(
    ( k2_struct_0 @ sk_A )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['78','105'])).

thf('107',plain,
    ( ( ( k2_struct_0 @ sk_B_1 )
     != k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['42'])).

thf('108',plain,(
    ( k2_struct_0 @ sk_B_1 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['106','107'])).

thf('109',plain,(
    ( k2_struct_0 @ sk_B_1 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['43','108'])).

thf('110',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['41','109'])).

thf('111',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['12','110'])).

thf('112',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k8_relset_1 @ X18 @ X19 @ X20 @ X19 )
        = ( k1_relset_1 @ X18 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('113',plain,
    ( ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B_1 ) @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
    = ( k1_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('115',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('116',plain,
    ( ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['41','109'])).

thf('118',plain,
    ( ( k1_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B_1 ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B_1 ) @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['113','118'])).

thf('120',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('121',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['41','109'])).

thf('126',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('128',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( v1_partfun1 @ X27 @ X28 )
      | ~ ( v1_funct_2 @ X27 @ X28 @ X29 )
      | ~ ( v1_funct_1 @ X27 )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('130',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['130','131','132'])).

thf('134',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v1_partfun1 @ X31 @ X30 )
      | ( ( k1_relat_1 @ X31 )
        = X30 )
      | ~ ( v4_relat_1 @ X31 @ X30 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('135',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['30','31'])).

thf('137',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v4_relat_1 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('139',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['135','136','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('142',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,
    ( ( ( k2_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B_1 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['127','142'])).

thf('144',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( ( k2_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,(
    ( k2_struct_0 @ sk_B_1 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['43','108'])).

thf('147',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['145','146'])).

thf('148',plain,(
    ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B_1 ) @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['126','147'])).

thf('149',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['119','148'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pauxewaIII
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:30:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.69  % Solved by: fo/fo7.sh
% 0.45/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.69  % done 421 iterations in 0.236s
% 0.45/0.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.69  % SZS output start Refutation
% 0.45/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.69  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.69  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.69  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.69  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.45/0.69  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.45/0.69  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.45/0.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.69  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.45/0.69  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.69  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.69  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.45/0.69  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.69  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.45/0.69  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.45/0.69  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.45/0.69  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.69  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.45/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.69  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.45/0.69  thf(sk_B_type, type, sk_B: $i > $i).
% 0.45/0.69  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.45/0.69  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.69  thf(d3_struct_0, axiom,
% 0.45/0.69    (![A:$i]:
% 0.45/0.69     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.45/0.69  thf('0', plain,
% 0.45/0.69      (![X32 : $i]:
% 0.45/0.69         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.45/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.69  thf('1', plain,
% 0.45/0.69      (![X32 : $i]:
% 0.45/0.69         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.45/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.69  thf(t52_tops_2, conjecture,
% 0.45/0.69    (![A:$i]:
% 0.45/0.69     ( ( l1_struct_0 @ A ) =>
% 0.45/0.69       ( ![B:$i]:
% 0.45/0.69         ( ( l1_struct_0 @ B ) =>
% 0.45/0.69           ( ![C:$i]:
% 0.45/0.69             ( ( ( v1_funct_1 @ C ) & 
% 0.45/0.69                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.69                 ( m1_subset_1 @
% 0.45/0.69                   C @ 
% 0.45/0.69                   ( k1_zfmisc_1 @
% 0.45/0.69                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.45/0.69               ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.45/0.69                   ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.69                 ( ( k8_relset_1 @
% 0.45/0.69                     ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.45/0.69                     ( k2_struct_0 @ B ) ) =
% 0.45/0.69                   ( k2_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.45/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.69    (~( ![A:$i]:
% 0.45/0.69        ( ( l1_struct_0 @ A ) =>
% 0.45/0.69          ( ![B:$i]:
% 0.45/0.69            ( ( l1_struct_0 @ B ) =>
% 0.45/0.69              ( ![C:$i]:
% 0.45/0.69                ( ( ( v1_funct_1 @ C ) & 
% 0.45/0.69                    ( v1_funct_2 @
% 0.45/0.69                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.69                    ( m1_subset_1 @
% 0.45/0.69                      C @ 
% 0.45/0.69                      ( k1_zfmisc_1 @
% 0.45/0.69                        ( k2_zfmisc_1 @
% 0.45/0.69                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.45/0.69                  ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.45/0.69                      ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.69                    ( ( k8_relset_1 @
% 0.45/0.69                        ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.45/0.69                        ( k2_struct_0 @ B ) ) =
% 0.45/0.69                      ( k2_struct_0 @ A ) ) ) ) ) ) ) ) )),
% 0.45/0.69    inference('cnf.neg', [status(esa)], [t52_tops_2])).
% 0.45/0.69  thf('2', plain,
% 0.45/0.69      ((m1_subset_1 @ sk_C @ 
% 0.45/0.69        (k1_zfmisc_1 @ 
% 0.45/0.69         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf(t3_subset, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.45/0.69  thf('3', plain,
% 0.45/0.69      (![X1 : $i, X2 : $i]:
% 0.45/0.69         ((r1_tarski @ X1 @ X2) | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.45/0.69      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.69  thf('4', plain,
% 0.45/0.69      ((r1_tarski @ sk_C @ 
% 0.45/0.69        (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['2', '3'])).
% 0.45/0.69  thf('5', plain,
% 0.45/0.69      (((r1_tarski @ sk_C @ 
% 0.45/0.69         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1)))
% 0.45/0.69        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.69      inference('sup+', [status(thm)], ['1', '4'])).
% 0.45/0.69  thf('6', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('7', plain,
% 0.45/0.69      ((r1_tarski @ sk_C @ 
% 0.45/0.69        (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1)))),
% 0.45/0.69      inference('demod', [status(thm)], ['5', '6'])).
% 0.45/0.69  thf('8', plain,
% 0.45/0.69      (((r1_tarski @ sk_C @ 
% 0.45/0.69         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1)))
% 0.45/0.69        | ~ (l1_struct_0 @ sk_B_1))),
% 0.45/0.69      inference('sup+', [status(thm)], ['0', '7'])).
% 0.45/0.69  thf('9', plain, ((l1_struct_0 @ sk_B_1)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('10', plain,
% 0.45/0.69      ((r1_tarski @ sk_C @ 
% 0.45/0.69        (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1)))),
% 0.45/0.69      inference('demod', [status(thm)], ['8', '9'])).
% 0.45/0.69  thf('11', plain,
% 0.45/0.69      (![X1 : $i, X3 : $i]:
% 0.45/0.69         ((m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X3)) | ~ (r1_tarski @ X1 @ X3))),
% 0.45/0.69      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.69  thf('12', plain,
% 0.45/0.69      ((m1_subset_1 @ sk_C @ 
% 0.45/0.69        (k1_zfmisc_1 @ 
% 0.45/0.69         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1))))),
% 0.45/0.69      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.69  thf('13', plain,
% 0.45/0.69      (![X32 : $i]:
% 0.45/0.69         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.45/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.69  thf('14', plain,
% 0.45/0.69      (![X32 : $i]:
% 0.45/0.69         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.45/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.69  thf('15', plain,
% 0.45/0.69      ((m1_subset_1 @ sk_C @ 
% 0.45/0.69        (k1_zfmisc_1 @ 
% 0.45/0.69         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('16', plain,
% 0.45/0.69      (((m1_subset_1 @ sk_C @ 
% 0.45/0.69         (k1_zfmisc_1 @ 
% 0.45/0.69          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))
% 0.45/0.69        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.69      inference('sup+', [status(thm)], ['14', '15'])).
% 0.45/0.69  thf('17', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('18', plain,
% 0.45/0.69      ((m1_subset_1 @ sk_C @ 
% 0.45/0.69        (k1_zfmisc_1 @ 
% 0.45/0.69         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.45/0.69      inference('demod', [status(thm)], ['16', '17'])).
% 0.45/0.69  thf(cc5_funct_2, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.45/0.69       ( ![C:$i]:
% 0.45/0.69         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.69           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.45/0.69             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.45/0.69  thf('19', plain,
% 0.45/0.69      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.45/0.69         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.45/0.69          | (v1_partfun1 @ X27 @ X28)
% 0.45/0.69          | ~ (v1_funct_2 @ X27 @ X28 @ X29)
% 0.45/0.69          | ~ (v1_funct_1 @ X27)
% 0.45/0.69          | (v1_xboole_0 @ X29))),
% 0.45/0.69      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.45/0.69  thf('20', plain,
% 0.45/0.69      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.45/0.69        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.69        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))
% 0.45/0.69        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['18', '19'])).
% 0.45/0.69  thf('21', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('22', plain,
% 0.45/0.69      (![X32 : $i]:
% 0.45/0.69         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.45/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.69  thf('23', plain,
% 0.45/0.69      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('24', plain,
% 0.45/0.69      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))
% 0.45/0.69        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.69      inference('sup+', [status(thm)], ['22', '23'])).
% 0.45/0.69  thf('25', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('26', plain,
% 0.45/0.69      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 0.45/0.69      inference('demod', [status(thm)], ['24', '25'])).
% 0.45/0.69  thf('27', plain,
% 0.45/0.69      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.45/0.69        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.45/0.69      inference('demod', [status(thm)], ['20', '21', '26'])).
% 0.45/0.69  thf(d4_partfun1, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.45/0.69       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.45/0.69  thf('28', plain,
% 0.45/0.69      (![X30 : $i, X31 : $i]:
% 0.45/0.69         (~ (v1_partfun1 @ X31 @ X30)
% 0.45/0.69          | ((k1_relat_1 @ X31) = (X30))
% 0.45/0.69          | ~ (v4_relat_1 @ X31 @ X30)
% 0.45/0.69          | ~ (v1_relat_1 @ X31))),
% 0.45/0.69      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.45/0.69  thf('29', plain,
% 0.45/0.69      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.45/0.69        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.69        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.45/0.69        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['27', '28'])).
% 0.45/0.69  thf('30', plain,
% 0.45/0.69      ((m1_subset_1 @ sk_C @ 
% 0.45/0.69        (k1_zfmisc_1 @ 
% 0.45/0.69         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf(cc1_relset_1, axiom,
% 0.45/0.69    (![A:$i,B:$i,C:$i]:
% 0.45/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.69       ( v1_relat_1 @ C ) ))).
% 0.45/0.69  thf('31', plain,
% 0.45/0.69      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.45/0.69         ((v1_relat_1 @ X9)
% 0.45/0.69          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.45/0.69      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.45/0.69  thf('32', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.69      inference('sup-', [status(thm)], ['30', '31'])).
% 0.45/0.69  thf('33', plain,
% 0.45/0.69      ((m1_subset_1 @ sk_C @ 
% 0.45/0.69        (k1_zfmisc_1 @ 
% 0.45/0.69         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.45/0.69      inference('demod', [status(thm)], ['16', '17'])).
% 0.45/0.69  thf(cc2_relset_1, axiom,
% 0.45/0.69    (![A:$i,B:$i,C:$i]:
% 0.45/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.69       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.45/0.69  thf('34', plain,
% 0.45/0.69      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.45/0.69         ((v4_relat_1 @ X12 @ X13)
% 0.45/0.69          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.45/0.69      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.45/0.69  thf('35', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.45/0.69      inference('sup-', [status(thm)], ['33', '34'])).
% 0.45/0.69  thf('36', plain,
% 0.45/0.69      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.45/0.69        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.45/0.69      inference('demod', [status(thm)], ['29', '32', '35'])).
% 0.45/0.69  thf(l13_xboole_0, axiom,
% 0.45/0.69    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.45/0.69  thf('37', plain,
% 0.45/0.69      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.45/0.69      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.45/0.69  thf('38', plain,
% 0.45/0.69      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))
% 0.45/0.69        | ((u1_struct_0 @ sk_B_1) = (k1_xboole_0)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['36', '37'])).
% 0.45/0.69  thf('39', plain,
% 0.45/0.69      ((((k2_struct_0 @ sk_B_1) = (k1_xboole_0))
% 0.45/0.69        | ~ (l1_struct_0 @ sk_B_1)
% 0.45/0.69        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.45/0.69      inference('sup+', [status(thm)], ['13', '38'])).
% 0.45/0.69  thf('40', plain, ((l1_struct_0 @ sk_B_1)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('41', plain,
% 0.45/0.69      ((((k2_struct_0 @ sk_B_1) = (k1_xboole_0))
% 0.45/0.69        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.45/0.69      inference('demod', [status(thm)], ['39', '40'])).
% 0.45/0.69  thf('42', plain,
% 0.45/0.69      ((((k2_struct_0 @ sk_A) = (k1_xboole_0))
% 0.45/0.69        | ((k2_struct_0 @ sk_B_1) != (k1_xboole_0)))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('43', plain,
% 0.45/0.69      ((((k2_struct_0 @ sk_B_1) != (k1_xboole_0)))
% 0.45/0.69         <= (~ (((k2_struct_0 @ sk_B_1) = (k1_xboole_0))))),
% 0.45/0.69      inference('split', [status(esa)], ['42'])).
% 0.45/0.69  thf('44', plain,
% 0.45/0.69      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.45/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.45/0.69      inference('split', [status(esa)], ['42'])).
% 0.45/0.69  thf('45', plain,
% 0.45/0.69      ((r1_tarski @ sk_C @ 
% 0.45/0.69        (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1)))),
% 0.45/0.69      inference('demod', [status(thm)], ['5', '6'])).
% 0.45/0.69  thf('46', plain,
% 0.45/0.69      (((r1_tarski @ sk_C @ 
% 0.45/0.69         (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B_1))))
% 0.45/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.45/0.69      inference('sup+', [status(thm)], ['44', '45'])).
% 0.45/0.69  thf('47', plain,
% 0.45/0.69      (![X1 : $i, X3 : $i]:
% 0.45/0.69         ((m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X3)) | ~ (r1_tarski @ X1 @ X3))),
% 0.45/0.69      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.69  thf('48', plain,
% 0.45/0.69      (((m1_subset_1 @ sk_C @ 
% 0.45/0.69         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B_1)))))
% 0.45/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.45/0.69      inference('sup-', [status(thm)], ['46', '47'])).
% 0.45/0.69  thf('49', plain,
% 0.45/0.69      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.45/0.69         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.45/0.69          | (v1_partfun1 @ X27 @ X28)
% 0.45/0.69          | ~ (v1_funct_2 @ X27 @ X28 @ X29)
% 0.45/0.69          | ~ (v1_funct_1 @ X27)
% 0.45/0.69          | (v1_xboole_0 @ X29))),
% 0.45/0.69      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.45/0.69  thf('50', plain,
% 0.45/0.69      ((((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.45/0.69         | ~ (v1_funct_1 @ sk_C)
% 0.45/0.69         | ~ (v1_funct_2 @ sk_C @ k1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.45/0.69         | (v1_partfun1 @ sk_C @ k1_xboole_0)))
% 0.45/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.45/0.69      inference('sup-', [status(thm)], ['48', '49'])).
% 0.45/0.69  thf('51', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('52', plain,
% 0.45/0.69      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.45/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.45/0.69      inference('split', [status(esa)], ['42'])).
% 0.45/0.69  thf('53', plain,
% 0.45/0.69      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 0.45/0.69      inference('demod', [status(thm)], ['24', '25'])).
% 0.45/0.69  thf('54', plain,
% 0.45/0.69      (((v1_funct_2 @ sk_C @ k1_xboole_0 @ (u1_struct_0 @ sk_B_1)))
% 0.45/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.45/0.69      inference('sup+', [status(thm)], ['52', '53'])).
% 0.45/0.69  thf('55', plain,
% 0.45/0.69      ((((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.45/0.69         | (v1_partfun1 @ sk_C @ k1_xboole_0)))
% 0.45/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.45/0.69      inference('demod', [status(thm)], ['50', '51', '54'])).
% 0.45/0.69  thf(t6_mcart_1, axiom,
% 0.45/0.69    (![A:$i]:
% 0.45/0.69     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.45/0.69          ( ![B:$i]:
% 0.45/0.69            ( ~( ( r2_hidden @ B @ A ) & 
% 0.45/0.69                 ( ![C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.45/0.69                   ( ( ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ E ) & 
% 0.45/0.69                       ( r2_hidden @ E @ F ) & ( r2_hidden @ F @ G ) & 
% 0.45/0.69                       ( r2_hidden @ G @ B ) ) =>
% 0.45/0.69                     ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 0.45/0.69  thf('56', plain,
% 0.45/0.69      (![X21 : $i]:
% 0.45/0.69         (((X21) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X21) @ X21))),
% 0.45/0.69      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.45/0.69  thf('57', plain,
% 0.45/0.69      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.45/0.69      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.45/0.69  thf('58', plain,
% 0.45/0.69      (((m1_subset_1 @ sk_C @ 
% 0.45/0.69         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B_1)))))
% 0.45/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.45/0.69      inference('sup-', [status(thm)], ['46', '47'])).
% 0.45/0.69  thf('59', plain,
% 0.45/0.69      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.45/0.69         ((v4_relat_1 @ X12 @ X13)
% 0.45/0.69          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.45/0.69      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.45/0.69  thf('60', plain,
% 0.45/0.69      (((v4_relat_1 @ sk_C @ k1_xboole_0))
% 0.45/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.45/0.69      inference('sup-', [status(thm)], ['58', '59'])).
% 0.45/0.69  thf(d18_relat_1, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( v1_relat_1 @ B ) =>
% 0.45/0.69       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.45/0.69  thf('61', plain,
% 0.45/0.69      (![X7 : $i, X8 : $i]:
% 0.45/0.69         (~ (v4_relat_1 @ X7 @ X8)
% 0.45/0.69          | (r1_tarski @ (k1_relat_1 @ X7) @ X8)
% 0.45/0.69          | ~ (v1_relat_1 @ X7))),
% 0.45/0.69      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.45/0.69  thf('62', plain,
% 0.45/0.69      (((~ (v1_relat_1 @ sk_C)
% 0.45/0.69         | (r1_tarski @ (k1_relat_1 @ sk_C) @ k1_xboole_0)))
% 0.45/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.45/0.69      inference('sup-', [status(thm)], ['60', '61'])).
% 0.45/0.69  thf('63', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.69      inference('sup-', [status(thm)], ['30', '31'])).
% 0.45/0.69  thf('64', plain,
% 0.45/0.69      (((r1_tarski @ (k1_relat_1 @ sk_C) @ k1_xboole_0))
% 0.45/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.45/0.69      inference('demod', [status(thm)], ['62', '63'])).
% 0.45/0.69  thf('65', plain,
% 0.45/0.69      (![X1 : $i, X3 : $i]:
% 0.45/0.69         ((m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X3)) | ~ (r1_tarski @ X1 @ X3))),
% 0.45/0.69      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.69  thf('66', plain,
% 0.45/0.69      (((m1_subset_1 @ (k1_relat_1 @ sk_C) @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.45/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.45/0.69      inference('sup-', [status(thm)], ['64', '65'])).
% 0.45/0.69  thf(t5_subset, axiom,
% 0.45/0.69    (![A:$i,B:$i,C:$i]:
% 0.45/0.69     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.45/0.69          ( v1_xboole_0 @ C ) ) ))).
% 0.45/0.69  thf('67', plain,
% 0.45/0.69      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.45/0.69         (~ (r2_hidden @ X4 @ X5)
% 0.45/0.69          | ~ (v1_xboole_0 @ X6)
% 0.45/0.69          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.45/0.69      inference('cnf', [status(esa)], [t5_subset])).
% 0.45/0.69  thf('68', plain,
% 0.45/0.69      ((![X0 : $i]:
% 0.45/0.69          (~ (v1_xboole_0 @ k1_xboole_0)
% 0.45/0.69           | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C))))
% 0.45/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.45/0.69      inference('sup-', [status(thm)], ['66', '67'])).
% 0.45/0.69  thf('69', plain,
% 0.45/0.69      ((![X0 : $i, X1 : $i]:
% 0.45/0.69          (~ (v1_xboole_0 @ X0)
% 0.45/0.69           | ~ (v1_xboole_0 @ X0)
% 0.45/0.69           | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_C))))
% 0.45/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.45/0.69      inference('sup-', [status(thm)], ['57', '68'])).
% 0.45/0.69  thf('70', plain,
% 0.45/0.69      ((![X0 : $i, X1 : $i]:
% 0.45/0.69          (~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_C)) | ~ (v1_xboole_0 @ X0)))
% 0.45/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.45/0.69      inference('simplify', [status(thm)], ['69'])).
% 0.45/0.69  thf('71', plain,
% 0.45/0.69      ((![X0 : $i]:
% 0.45/0.69          (((k1_relat_1 @ sk_C) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.45/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.45/0.69      inference('sup-', [status(thm)], ['56', '70'])).
% 0.45/0.69  thf('72', plain,
% 0.45/0.69      ((((v1_partfun1 @ sk_C @ k1_xboole_0)
% 0.45/0.69         | ((k1_relat_1 @ sk_C) = (k1_xboole_0))))
% 0.45/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.45/0.69      inference('sup-', [status(thm)], ['55', '71'])).
% 0.45/0.69  thf('73', plain,
% 0.45/0.69      (![X30 : $i, X31 : $i]:
% 0.45/0.69         (~ (v1_partfun1 @ X31 @ X30)
% 0.45/0.69          | ((k1_relat_1 @ X31) = (X30))
% 0.45/0.69          | ~ (v4_relat_1 @ X31 @ X30)
% 0.45/0.69          | ~ (v1_relat_1 @ X31))),
% 0.45/0.69      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.45/0.69  thf('74', plain,
% 0.45/0.69      (((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 0.45/0.69         | ~ (v1_relat_1 @ sk_C)
% 0.45/0.69         | ~ (v4_relat_1 @ sk_C @ k1_xboole_0)
% 0.45/0.69         | ((k1_relat_1 @ sk_C) = (k1_xboole_0))))
% 0.45/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.45/0.69      inference('sup-', [status(thm)], ['72', '73'])).
% 0.45/0.69  thf('75', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.69      inference('sup-', [status(thm)], ['30', '31'])).
% 0.45/0.69  thf('76', plain,
% 0.45/0.69      (((v4_relat_1 @ sk_C @ k1_xboole_0))
% 0.45/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.45/0.69      inference('sup-', [status(thm)], ['58', '59'])).
% 0.45/0.69  thf('77', plain,
% 0.45/0.69      (((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 0.45/0.69         | ((k1_relat_1 @ sk_C) = (k1_xboole_0))))
% 0.45/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.45/0.69      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.45/0.69  thf('78', plain,
% 0.45/0.69      ((((k1_relat_1 @ sk_C) = (k1_xboole_0)))
% 0.45/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.45/0.69      inference('simplify', [status(thm)], ['77'])).
% 0.45/0.69  thf('79', plain,
% 0.45/0.69      (![X32 : $i]:
% 0.45/0.69         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.45/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.69  thf('80', plain,
% 0.45/0.69      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.45/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.45/0.69      inference('split', [status(esa)], ['42'])).
% 0.45/0.69  thf('81', plain,
% 0.45/0.69      (![X32 : $i]:
% 0.45/0.69         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.45/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.69  thf('82', plain,
% 0.45/0.69      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C @ 
% 0.45/0.69         (k2_struct_0 @ sk_B_1)) != (k2_struct_0 @ sk_A))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('83', plain,
% 0.45/0.69      ((((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C @ 
% 0.45/0.69          (k2_struct_0 @ sk_B_1)) != (k2_struct_0 @ sk_A))
% 0.45/0.69        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.69      inference('sup-', [status(thm)], ['81', '82'])).
% 0.45/0.69  thf('84', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('85', plain,
% 0.45/0.69      (((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C @ 
% 0.45/0.69         (k2_struct_0 @ sk_B_1)) != (k2_struct_0 @ sk_A))),
% 0.45/0.69      inference('demod', [status(thm)], ['83', '84'])).
% 0.45/0.69  thf('86', plain,
% 0.45/0.69      ((((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ sk_C @ 
% 0.45/0.69          (k2_struct_0 @ sk_B_1)) != (k2_struct_0 @ sk_A)))
% 0.45/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.45/0.69      inference('sup-', [status(thm)], ['80', '85'])).
% 0.45/0.69  thf('87', plain,
% 0.45/0.69      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.45/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.45/0.69      inference('split', [status(esa)], ['42'])).
% 0.45/0.69  thf('88', plain,
% 0.45/0.69      ((((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ sk_C @ 
% 0.45/0.69          (k2_struct_0 @ sk_B_1)) != (k1_xboole_0)))
% 0.45/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.45/0.69      inference('demod', [status(thm)], ['86', '87'])).
% 0.45/0.69  thf('89', plain,
% 0.45/0.69      (((((k8_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B_1) @ sk_C @ 
% 0.45/0.69           (k2_struct_0 @ sk_B_1)) != (k1_xboole_0))
% 0.45/0.69         | ~ (l1_struct_0 @ sk_B_1)))
% 0.45/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.45/0.69      inference('sup-', [status(thm)], ['79', '88'])).
% 0.45/0.69  thf('90', plain, ((l1_struct_0 @ sk_B_1)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('91', plain,
% 0.45/0.69      ((((k8_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B_1) @ sk_C @ 
% 0.45/0.69          (k2_struct_0 @ sk_B_1)) != (k1_xboole_0)))
% 0.45/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.45/0.69      inference('demod', [status(thm)], ['89', '90'])).
% 0.45/0.69  thf('92', plain,
% 0.45/0.69      (![X32 : $i]:
% 0.45/0.69         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.45/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.69  thf('93', plain,
% 0.45/0.69      (((r1_tarski @ sk_C @ 
% 0.45/0.69         (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B_1))))
% 0.45/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.45/0.69      inference('sup+', [status(thm)], ['44', '45'])).
% 0.45/0.69  thf('94', plain,
% 0.45/0.69      ((((r1_tarski @ sk_C @ 
% 0.45/0.69          (k2_zfmisc_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B_1)))
% 0.45/0.69         | ~ (l1_struct_0 @ sk_B_1)))
% 0.45/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.45/0.69      inference('sup+', [status(thm)], ['92', '93'])).
% 0.45/0.69  thf('95', plain, ((l1_struct_0 @ sk_B_1)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('96', plain,
% 0.45/0.69      (((r1_tarski @ sk_C @ 
% 0.45/0.69         (k2_zfmisc_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B_1))))
% 0.45/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.45/0.69      inference('demod', [status(thm)], ['94', '95'])).
% 0.45/0.69  thf('97', plain,
% 0.45/0.69      (![X1 : $i, X3 : $i]:
% 0.45/0.69         ((m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X3)) | ~ (r1_tarski @ X1 @ X3))),
% 0.45/0.69      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.69  thf('98', plain,
% 0.45/0.69      (((m1_subset_1 @ sk_C @ 
% 0.45/0.69         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B_1)))))
% 0.45/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.45/0.69      inference('sup-', [status(thm)], ['96', '97'])).
% 0.45/0.69  thf(t38_relset_1, axiom,
% 0.45/0.69    (![A:$i,B:$i,C:$i]:
% 0.45/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.69       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.45/0.69         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.45/0.69  thf('99', plain,
% 0.45/0.69      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.45/0.69         (((k8_relset_1 @ X18 @ X19 @ X20 @ X19)
% 0.45/0.69            = (k1_relset_1 @ X18 @ X19 @ X20))
% 0.45/0.69          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.45/0.69      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.45/0.69  thf('100', plain,
% 0.45/0.69      ((((k8_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B_1) @ sk_C @ 
% 0.45/0.69          (k2_struct_0 @ sk_B_1))
% 0.45/0.69          = (k1_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B_1) @ sk_C)))
% 0.45/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.45/0.69      inference('sup-', [status(thm)], ['98', '99'])).
% 0.45/0.69  thf('101', plain,
% 0.45/0.69      (((m1_subset_1 @ sk_C @ 
% 0.45/0.69         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B_1)))))
% 0.45/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.45/0.69      inference('sup-', [status(thm)], ['96', '97'])).
% 0.45/0.69  thf(redefinition_k1_relset_1, axiom,
% 0.45/0.69    (![A:$i,B:$i,C:$i]:
% 0.45/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.69       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.45/0.69  thf('102', plain,
% 0.45/0.69      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.45/0.69         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 0.45/0.69          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.45/0.69      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.45/0.69  thf('103', plain,
% 0.45/0.69      ((((k1_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B_1) @ sk_C)
% 0.45/0.69          = (k1_relat_1 @ sk_C)))
% 0.45/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.45/0.69      inference('sup-', [status(thm)], ['101', '102'])).
% 0.45/0.69  thf('104', plain,
% 0.45/0.69      ((((k8_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B_1) @ sk_C @ 
% 0.45/0.69          (k2_struct_0 @ sk_B_1)) = (k1_relat_1 @ sk_C)))
% 0.45/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.45/0.69      inference('demod', [status(thm)], ['100', '103'])).
% 0.45/0.69  thf('105', plain,
% 0.45/0.69      ((((k1_relat_1 @ sk_C) != (k1_xboole_0)))
% 0.45/0.69         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.45/0.69      inference('demod', [status(thm)], ['91', '104'])).
% 0.45/0.69  thf('106', plain, (~ (((k2_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.45/0.69      inference('simplify_reflect-', [status(thm)], ['78', '105'])).
% 0.45/0.69  thf('107', plain,
% 0.45/0.69      (~ (((k2_struct_0 @ sk_B_1) = (k1_xboole_0))) | 
% 0.45/0.69       (((k2_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.45/0.69      inference('split', [status(esa)], ['42'])).
% 0.45/0.69  thf('108', plain, (~ (((k2_struct_0 @ sk_B_1) = (k1_xboole_0)))),
% 0.45/0.69      inference('sat_resolution*', [status(thm)], ['106', '107'])).
% 0.45/0.69  thf('109', plain, (((k2_struct_0 @ sk_B_1) != (k1_xboole_0))),
% 0.45/0.69      inference('simpl_trail', [status(thm)], ['43', '108'])).
% 0.45/0.69  thf('110', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.69      inference('simplify_reflect-', [status(thm)], ['41', '109'])).
% 0.45/0.69  thf('111', plain,
% 0.45/0.69      ((m1_subset_1 @ sk_C @ 
% 0.45/0.69        (k1_zfmisc_1 @ 
% 0.45/0.69         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B_1))))),
% 0.45/0.69      inference('demod', [status(thm)], ['12', '110'])).
% 0.45/0.69  thf('112', plain,
% 0.45/0.69      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.45/0.69         (((k8_relset_1 @ X18 @ X19 @ X20 @ X19)
% 0.45/0.69            = (k1_relset_1 @ X18 @ X19 @ X20))
% 0.45/0.69          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.45/0.69      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.45/0.69  thf('113', plain,
% 0.45/0.69      (((k8_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B_1) @ sk_C @ 
% 0.45/0.69         (k2_struct_0 @ sk_B_1))
% 0.45/0.69         = (k1_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B_1) @ sk_C))),
% 0.45/0.69      inference('sup-', [status(thm)], ['111', '112'])).
% 0.45/0.69  thf('114', plain,
% 0.45/0.69      ((m1_subset_1 @ sk_C @ 
% 0.45/0.69        (k1_zfmisc_1 @ 
% 0.45/0.69         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1))))),
% 0.45/0.69      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.69  thf('115', plain,
% 0.45/0.69      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.45/0.69         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 0.45/0.69          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.45/0.69      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.45/0.69  thf('116', plain,
% 0.45/0.69      (((k1_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1) @ sk_C)
% 0.45/0.69         = (k1_relat_1 @ sk_C))),
% 0.45/0.69      inference('sup-', [status(thm)], ['114', '115'])).
% 0.45/0.69  thf('117', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.69      inference('simplify_reflect-', [status(thm)], ['41', '109'])).
% 0.45/0.69  thf('118', plain,
% 0.45/0.69      (((k1_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B_1) @ sk_C)
% 0.45/0.69         = (k1_relat_1 @ sk_C))),
% 0.45/0.69      inference('demod', [status(thm)], ['116', '117'])).
% 0.45/0.69  thf('119', plain,
% 0.45/0.69      (((k8_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B_1) @ sk_C @ 
% 0.45/0.69         (k2_struct_0 @ sk_B_1)) = (k1_relat_1 @ sk_C))),
% 0.45/0.69      inference('demod', [status(thm)], ['113', '118'])).
% 0.45/0.69  thf('120', plain,
% 0.45/0.69      (![X32 : $i]:
% 0.45/0.69         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.45/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.69  thf('121', plain,
% 0.45/0.69      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C @ 
% 0.45/0.69         (k2_struct_0 @ sk_B_1)) != (k2_struct_0 @ sk_A))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('122', plain,
% 0.45/0.69      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1) @ sk_C @ 
% 0.45/0.69          (k2_struct_0 @ sk_B_1)) != (k2_struct_0 @ sk_A))
% 0.45/0.69        | ~ (l1_struct_0 @ sk_B_1))),
% 0.45/0.69      inference('sup-', [status(thm)], ['120', '121'])).
% 0.45/0.69  thf('123', plain, ((l1_struct_0 @ sk_B_1)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('124', plain,
% 0.45/0.69      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1) @ sk_C @ 
% 0.45/0.69         (k2_struct_0 @ sk_B_1)) != (k2_struct_0 @ sk_A))),
% 0.45/0.69      inference('demod', [status(thm)], ['122', '123'])).
% 0.45/0.69  thf('125', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.69      inference('simplify_reflect-', [status(thm)], ['41', '109'])).
% 0.45/0.69  thf('126', plain,
% 0.45/0.69      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1) @ sk_C @ 
% 0.45/0.69         (k2_struct_0 @ sk_B_1)) != (k1_relat_1 @ sk_C))),
% 0.45/0.69      inference('demod', [status(thm)], ['124', '125'])).
% 0.45/0.69  thf('127', plain,
% 0.45/0.69      (![X32 : $i]:
% 0.45/0.69         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 0.45/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.69  thf('128', plain,
% 0.45/0.69      ((m1_subset_1 @ sk_C @ 
% 0.45/0.69        (k1_zfmisc_1 @ 
% 0.45/0.69         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('129', plain,
% 0.45/0.69      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.45/0.69         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.45/0.69          | (v1_partfun1 @ X27 @ X28)
% 0.45/0.69          | ~ (v1_funct_2 @ X27 @ X28 @ X29)
% 0.45/0.69          | ~ (v1_funct_1 @ X27)
% 0.45/0.69          | (v1_xboole_0 @ X29))),
% 0.45/0.69      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.45/0.69  thf('130', plain,
% 0.45/0.69      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.45/0.69        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.69        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))
% 0.45/0.69        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['128', '129'])).
% 0.45/0.69  thf('131', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('132', plain,
% 0.45/0.69      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('133', plain,
% 0.45/0.69      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.45/0.69        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.45/0.69      inference('demod', [status(thm)], ['130', '131', '132'])).
% 0.45/0.69  thf('134', plain,
% 0.45/0.69      (![X30 : $i, X31 : $i]:
% 0.45/0.69         (~ (v1_partfun1 @ X31 @ X30)
% 0.45/0.69          | ((k1_relat_1 @ X31) = (X30))
% 0.45/0.69          | ~ (v4_relat_1 @ X31 @ X30)
% 0.45/0.69          | ~ (v1_relat_1 @ X31))),
% 0.45/0.69      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.45/0.69  thf('135', plain,
% 0.45/0.69      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.45/0.69        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.69        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.45/0.69        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['133', '134'])).
% 0.45/0.69  thf('136', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.69      inference('sup-', [status(thm)], ['30', '31'])).
% 0.45/0.69  thf('137', plain,
% 0.45/0.69      ((m1_subset_1 @ sk_C @ 
% 0.45/0.69        (k1_zfmisc_1 @ 
% 0.45/0.69         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('138', plain,
% 0.45/0.69      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.45/0.69         ((v4_relat_1 @ X12 @ X13)
% 0.45/0.69          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.45/0.69      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.45/0.69  thf('139', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.45/0.69      inference('sup-', [status(thm)], ['137', '138'])).
% 0.45/0.69  thf('140', plain,
% 0.45/0.69      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.45/0.69        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.45/0.69      inference('demod', [status(thm)], ['135', '136', '139'])).
% 0.45/0.69  thf('141', plain,
% 0.45/0.69      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.45/0.69      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.45/0.69  thf('142', plain,
% 0.45/0.69      ((((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))
% 0.45/0.69        | ((u1_struct_0 @ sk_B_1) = (k1_xboole_0)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['140', '141'])).
% 0.45/0.69  thf('143', plain,
% 0.45/0.69      ((((k2_struct_0 @ sk_B_1) = (k1_xboole_0))
% 0.45/0.69        | ~ (l1_struct_0 @ sk_B_1)
% 0.45/0.69        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.45/0.69      inference('sup+', [status(thm)], ['127', '142'])).
% 0.45/0.69  thf('144', plain, ((l1_struct_0 @ sk_B_1)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('145', plain,
% 0.45/0.69      ((((k2_struct_0 @ sk_B_1) = (k1_xboole_0))
% 0.45/0.69        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.45/0.69      inference('demod', [status(thm)], ['143', '144'])).
% 0.45/0.69  thf('146', plain, (((k2_struct_0 @ sk_B_1) != (k1_xboole_0))),
% 0.45/0.69      inference('simpl_trail', [status(thm)], ['43', '108'])).
% 0.45/0.69  thf('147', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.45/0.69      inference('simplify_reflect-', [status(thm)], ['145', '146'])).
% 0.45/0.69  thf('148', plain,
% 0.45/0.69      (((k8_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B_1) @ sk_C @ 
% 0.45/0.69         (k2_struct_0 @ sk_B_1)) != (k1_relat_1 @ sk_C))),
% 0.45/0.69      inference('demod', [status(thm)], ['126', '147'])).
% 0.45/0.69  thf('149', plain, ($false),
% 0.45/0.69      inference('simplify_reflect-', [status(thm)], ['119', '148'])).
% 0.45/0.69  
% 0.45/0.69  % SZS output end Refutation
% 0.45/0.69  
% 0.45/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
