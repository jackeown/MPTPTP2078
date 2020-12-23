%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DZglPBuuTL

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:44 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :  194 (1268 expanded)
%              Number of leaves         :   40 ( 375 expanded)
%              Depth                    :   28
%              Number of atoms          : 1522 (20124 expanded)
%              Number of equality atoms :  133 (1594 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
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
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('14',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( v1_partfun1 @ X28 @ X29 )
      | ~ ( v1_funct_2 @ X28 @ X29 @ X30 )
      | ~ ( v1_funct_1 @ X28 )
      | ( v1_xboole_0 @ X30 ) ) ),
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
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
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
    ! [X31: $i,X32: $i] :
      ( ~ ( v1_partfun1 @ X32 @ X31 )
      | ( ( k1_relat_1 @ X32 )
        = X31 )
      | ~ ( v4_relat_1 @ X32 @ X31 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('31',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('33',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('34',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('36',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v4_relat_1 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('37',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','34','37'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('39',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('40',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( k2_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B_1 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['13','40'])).

thf('42',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( ( k2_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( k2_struct_0 @ sk_B_1 )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('46',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('47',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('48',plain,
    ( ( r1_tarski @ sk_C @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X1: $i,X3: $i] :
      ( ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('50',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( v1_partfun1 @ X28 @ X29 )
      | ~ ( v1_funct_2 @ X28 @ X29 @ X30 )
      | ~ ( v1_funct_1 @ X28 )
      | ( v1_xboole_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('52',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ k1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v1_partfun1 @ sk_C @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('55',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('56',plain,
    ( ( v1_funct_2 @ sk_C @ k1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v1_partfun1 @ sk_C @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['52','53','56'])).

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

thf('58',plain,(
    ! [X22: $i] :
      ( ( X22 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X22 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('60',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('61',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v4_relat_1 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('62',plain,
    ( ( v4_relat_1 @ sk_C @ k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('63',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v4_relat_1 @ X9 @ X10 )
      | ( r1_tarski @ ( k1_relat_1 @ X9 ) @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('64',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('66',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X1: $i,X3: $i] :
      ( ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('68',plain,
    ( ( m1_subset_1 @ ( k1_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('69',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('70',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_C ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','70'])).

thf('72',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_C ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,
    ( ! [X0: $i] :
        ( ( ( k1_relat_1 @ sk_C )
          = k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','72'])).

thf('74',plain,
    ( ( ( v1_partfun1 @ sk_C @ k1_xboole_0 )
      | ( ( k1_relat_1 @ sk_C )
        = k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','73'])).

thf('75',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v1_partfun1 @ X32 @ X31 )
      | ( ( k1_relat_1 @ X32 )
        = X31 )
      | ~ ( v4_relat_1 @ X32 @ X31 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('76',plain,
    ( ( ( ( k1_relat_1 @ sk_C )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v4_relat_1 @ sk_C @ k1_xboole_0 )
      | ( ( k1_relat_1 @ sk_C )
        = k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('78',plain,
    ( ( v4_relat_1 @ sk_C @ k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('79',plain,
    ( ( ( ( k1_relat_1 @ sk_C )
        = k1_xboole_0 )
      | ( ( k1_relat_1 @ sk_C )
        = k1_xboole_0 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('82',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('83',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('84',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ( k8_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['82','87'])).

thf('89',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('90',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ( ( k8_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
       != k1_xboole_0 )
      | ~ ( l1_struct_0 @ sk_B_1 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['81','90'])).

thf('92',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('95',plain,
    ( ( r1_tarski @ sk_C @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('96',plain,
    ( ( ( r1_tarski @ sk_C @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) ) )
      | ~ ( l1_struct_0 @ sk_B_1 ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( r1_tarski @ sk_C @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X1: $i,X3: $i] :
      ( ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('100',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('101',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k8_relset_1 @ X19 @ X20 @ X21 @ X20 )
        = ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('102',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
      = ( k1_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) ) ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('104',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('105',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) @ sk_C )
      = ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( ( k8_relset_1 @ k1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
      = ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['102','105'])).

thf('107',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != k1_xboole_0 )
   <= ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['93','106'])).

thf('108',plain,(
    ( k2_struct_0 @ sk_A )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['80','107'])).

thf('109',plain,
    ( ( ( k2_struct_0 @ sk_B_1 )
     != k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('110',plain,(
    ( k2_struct_0 @ sk_B_1 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['108','109'])).

thf('111',plain,(
    ( k2_struct_0 @ sk_B_1 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['45','110'])).

thf('112',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','111'])).

thf('113',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['12','113'])).

thf('115',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k8_relset_1 @ X19 @ X20 @ X21 @ X20 )
        = ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('116',plain,
    ( ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B_1 ) @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
    = ( k1_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('118',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('119',plain,
    ( ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['112'])).

thf('121',plain,
    ( ( k1_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B_1 ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,
    ( ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B_1 ) @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['116','121'])).

thf('123',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('124',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['112'])).

thf('129',plain,(
    ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B_1 ) @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('131',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( v1_partfun1 @ X28 @ X29 )
      | ~ ( v1_funct_2 @ X28 @ X29 @ X30 )
      | ~ ( v1_funct_1 @ X28 )
      | ( v1_xboole_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('133',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['133','134','135'])).

thf('137',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v1_partfun1 @ X32 @ X31 )
      | ( ( k1_relat_1 @ X32 )
        = X31 )
      | ~ ( v4_relat_1 @ X32 @ X31 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('138',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('140',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v4_relat_1 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('142',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['138','139','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('145',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,
    ( ( ( k2_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B_1 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['130','145'])).

thf('147',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( ( k2_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,(
    ( k2_struct_0 @ sk_B_1 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['45','110'])).

thf('150',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['148','149'])).

thf('151',plain,(
    ( k8_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B_1 ) @ sk_C @ ( k2_struct_0 @ sk_B_1 ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['129','150'])).

thf('152',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['122','151'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DZglPBuuTL
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:57:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.54/0.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.54/0.74  % Solved by: fo/fo7.sh
% 0.54/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.74  % done 424 iterations in 0.283s
% 0.54/0.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.54/0.74  % SZS output start Refutation
% 0.54/0.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.54/0.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.54/0.74  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.54/0.74  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.54/0.74  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.54/0.74  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.54/0.74  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.54/0.74  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.54/0.74  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.54/0.74  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.54/0.74  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.54/0.74  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.54/0.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.74  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.54/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.74  thf(sk_B_type, type, sk_B: $i > $i).
% 0.54/0.74  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.54/0.74  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.54/0.74  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.54/0.74  thf(sk_C_type, type, sk_C: $i).
% 0.54/0.74  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.54/0.74  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.54/0.74  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.54/0.74  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.54/0.74  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.54/0.74  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.54/0.74  thf(d3_struct_0, axiom,
% 0.54/0.74    (![A:$i]:
% 0.54/0.74     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.54/0.74  thf('0', plain,
% 0.54/0.74      (![X33 : $i]:
% 0.54/0.74         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.54/0.74      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.54/0.74  thf('1', plain,
% 0.54/0.74      (![X33 : $i]:
% 0.54/0.74         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.54/0.74      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.54/0.74  thf(t52_tops_2, conjecture,
% 0.54/0.74    (![A:$i]:
% 0.54/0.74     ( ( l1_struct_0 @ A ) =>
% 0.54/0.74       ( ![B:$i]:
% 0.54/0.74         ( ( l1_struct_0 @ B ) =>
% 0.54/0.74           ( ![C:$i]:
% 0.54/0.74             ( ( ( v1_funct_1 @ C ) & 
% 0.54/0.74                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.54/0.74                 ( m1_subset_1 @
% 0.54/0.74                   C @ 
% 0.54/0.74                   ( k1_zfmisc_1 @
% 0.54/0.74                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.54/0.74               ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.54/0.74                   ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.54/0.74                 ( ( k8_relset_1 @
% 0.54/0.74                     ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.54/0.74                     ( k2_struct_0 @ B ) ) =
% 0.54/0.74                   ( k2_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.54/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.74    (~( ![A:$i]:
% 0.54/0.74        ( ( l1_struct_0 @ A ) =>
% 0.54/0.74          ( ![B:$i]:
% 0.54/0.74            ( ( l1_struct_0 @ B ) =>
% 0.54/0.74              ( ![C:$i]:
% 0.54/0.74                ( ( ( v1_funct_1 @ C ) & 
% 0.54/0.74                    ( v1_funct_2 @
% 0.54/0.74                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.54/0.74                    ( m1_subset_1 @
% 0.54/0.74                      C @ 
% 0.54/0.74                      ( k1_zfmisc_1 @
% 0.54/0.74                        ( k2_zfmisc_1 @
% 0.54/0.74                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.54/0.74                  ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.54/0.74                      ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.54/0.74                    ( ( k8_relset_1 @
% 0.54/0.74                        ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.54/0.74                        ( k2_struct_0 @ B ) ) =
% 0.54/0.74                      ( k2_struct_0 @ A ) ) ) ) ) ) ) ) )),
% 0.54/0.74    inference('cnf.neg', [status(esa)], [t52_tops_2])).
% 0.54/0.74  thf('2', plain,
% 0.54/0.74      ((m1_subset_1 @ sk_C @ 
% 0.54/0.74        (k1_zfmisc_1 @ 
% 0.54/0.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf(t3_subset, axiom,
% 0.54/0.74    (![A:$i,B:$i]:
% 0.54/0.74     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.54/0.74  thf('3', plain,
% 0.54/0.74      (![X1 : $i, X2 : $i]:
% 0.54/0.74         ((r1_tarski @ X1 @ X2) | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.54/0.74      inference('cnf', [status(esa)], [t3_subset])).
% 0.54/0.74  thf('4', plain,
% 0.54/0.74      ((r1_tarski @ sk_C @ 
% 0.54/0.74        (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['2', '3'])).
% 0.54/0.74  thf('5', plain,
% 0.54/0.74      (((r1_tarski @ sk_C @ 
% 0.54/0.74         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1)))
% 0.54/0.74        | ~ (l1_struct_0 @ sk_A))),
% 0.54/0.74      inference('sup+', [status(thm)], ['1', '4'])).
% 0.54/0.74  thf('6', plain, ((l1_struct_0 @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('7', plain,
% 0.54/0.74      ((r1_tarski @ sk_C @ 
% 0.54/0.74        (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1)))),
% 0.54/0.74      inference('demod', [status(thm)], ['5', '6'])).
% 0.54/0.74  thf('8', plain,
% 0.54/0.74      (((r1_tarski @ sk_C @ 
% 0.54/0.74         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1)))
% 0.54/0.74        | ~ (l1_struct_0 @ sk_B_1))),
% 0.54/0.74      inference('sup+', [status(thm)], ['0', '7'])).
% 0.54/0.74  thf('9', plain, ((l1_struct_0 @ sk_B_1)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('10', plain,
% 0.54/0.74      ((r1_tarski @ sk_C @ 
% 0.54/0.74        (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1)))),
% 0.54/0.74      inference('demod', [status(thm)], ['8', '9'])).
% 0.54/0.74  thf('11', plain,
% 0.54/0.74      (![X1 : $i, X3 : $i]:
% 0.54/0.74         ((m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X3)) | ~ (r1_tarski @ X1 @ X3))),
% 0.54/0.74      inference('cnf', [status(esa)], [t3_subset])).
% 0.54/0.74  thf('12', plain,
% 0.54/0.74      ((m1_subset_1 @ sk_C @ 
% 0.54/0.74        (k1_zfmisc_1 @ 
% 0.54/0.74         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1))))),
% 0.54/0.74      inference('sup-', [status(thm)], ['10', '11'])).
% 0.54/0.74  thf('13', plain,
% 0.54/0.74      (![X33 : $i]:
% 0.54/0.74         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.54/0.74      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.54/0.74  thf('14', plain,
% 0.54/0.74      (![X33 : $i]:
% 0.54/0.74         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.54/0.74      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.54/0.74  thf('15', plain,
% 0.54/0.74      ((m1_subset_1 @ sk_C @ 
% 0.54/0.74        (k1_zfmisc_1 @ 
% 0.54/0.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('16', plain,
% 0.54/0.74      (((m1_subset_1 @ sk_C @ 
% 0.54/0.74         (k1_zfmisc_1 @ 
% 0.54/0.74          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))
% 0.54/0.74        | ~ (l1_struct_0 @ sk_A))),
% 0.54/0.74      inference('sup+', [status(thm)], ['14', '15'])).
% 0.54/0.74  thf('17', plain, ((l1_struct_0 @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('18', plain,
% 0.54/0.74      ((m1_subset_1 @ sk_C @ 
% 0.54/0.74        (k1_zfmisc_1 @ 
% 0.54/0.74         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.54/0.74      inference('demod', [status(thm)], ['16', '17'])).
% 0.54/0.74  thf(cc5_funct_2, axiom,
% 0.54/0.74    (![A:$i,B:$i]:
% 0.54/0.74     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.54/0.74       ( ![C:$i]:
% 0.54/0.74         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.74           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.54/0.74             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.54/0.74  thf('19', plain,
% 0.54/0.74      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.54/0.74         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.54/0.74          | (v1_partfun1 @ X28 @ X29)
% 0.54/0.75          | ~ (v1_funct_2 @ X28 @ X29 @ X30)
% 0.54/0.75          | ~ (v1_funct_1 @ X28)
% 0.54/0.75          | (v1_xboole_0 @ X30))),
% 0.54/0.75      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.54/0.75  thf('20', plain,
% 0.54/0.75      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.54/0.75        | ~ (v1_funct_1 @ sk_C)
% 0.54/0.75        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))
% 0.54/0.75        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['18', '19'])).
% 0.54/0.75  thf('21', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('22', plain,
% 0.54/0.75      (![X33 : $i]:
% 0.54/0.75         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.54/0.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.54/0.75  thf('23', plain,
% 0.54/0.75      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('24', plain,
% 0.54/0.75      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))
% 0.54/0.75        | ~ (l1_struct_0 @ sk_A))),
% 0.54/0.75      inference('sup+', [status(thm)], ['22', '23'])).
% 0.54/0.75  thf('25', plain, ((l1_struct_0 @ sk_A)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('26', plain,
% 0.54/0.75      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 0.54/0.75      inference('demod', [status(thm)], ['24', '25'])).
% 0.54/0.75  thf('27', plain,
% 0.54/0.75      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.54/0.75        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.54/0.75      inference('demod', [status(thm)], ['20', '21', '26'])).
% 0.54/0.75  thf(d4_partfun1, axiom,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.54/0.75       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.54/0.75  thf('28', plain,
% 0.54/0.75      (![X31 : $i, X32 : $i]:
% 0.54/0.75         (~ (v1_partfun1 @ X32 @ X31)
% 0.54/0.75          | ((k1_relat_1 @ X32) = (X31))
% 0.54/0.75          | ~ (v4_relat_1 @ X32 @ X31)
% 0.54/0.75          | ~ (v1_relat_1 @ X32))),
% 0.54/0.75      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.54/0.75  thf('29', plain,
% 0.54/0.75      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.54/0.75        | ~ (v1_relat_1 @ sk_C)
% 0.54/0.75        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.54/0.75        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['27', '28'])).
% 0.54/0.75  thf('30', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_C @ 
% 0.54/0.75        (k1_zfmisc_1 @ 
% 0.54/0.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf(cc2_relat_1, axiom,
% 0.54/0.75    (![A:$i]:
% 0.54/0.75     ( ( v1_relat_1 @ A ) =>
% 0.54/0.75       ( ![B:$i]:
% 0.54/0.75         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.54/0.75  thf('31', plain,
% 0.54/0.75      (![X7 : $i, X8 : $i]:
% 0.54/0.75         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.54/0.75          | (v1_relat_1 @ X7)
% 0.54/0.75          | ~ (v1_relat_1 @ X8))),
% 0.54/0.75      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.54/0.75  thf('32', plain,
% 0.54/0.75      ((~ (v1_relat_1 @ 
% 0.54/0.75           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1)))
% 0.54/0.75        | (v1_relat_1 @ sk_C))),
% 0.54/0.75      inference('sup-', [status(thm)], ['30', '31'])).
% 0.54/0.75  thf(fc6_relat_1, axiom,
% 0.54/0.75    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.54/0.75  thf('33', plain,
% 0.54/0.75      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 0.54/0.75      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.54/0.75  thf('34', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.75      inference('demod', [status(thm)], ['32', '33'])).
% 0.54/0.75  thf('35', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_C @ 
% 0.54/0.75        (k1_zfmisc_1 @ 
% 0.54/0.75         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.54/0.75      inference('demod', [status(thm)], ['16', '17'])).
% 0.54/0.75  thf(cc2_relset_1, axiom,
% 0.54/0.75    (![A:$i,B:$i,C:$i]:
% 0.54/0.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.75       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.54/0.75  thf('36', plain,
% 0.54/0.75      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.54/0.75         ((v4_relat_1 @ X13 @ X14)
% 0.54/0.75          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.54/0.75      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.54/0.75  thf('37', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.54/0.75      inference('sup-', [status(thm)], ['35', '36'])).
% 0.54/0.75  thf('38', plain,
% 0.54/0.75      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.54/0.75        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.54/0.75      inference('demod', [status(thm)], ['29', '34', '37'])).
% 0.54/0.75  thf(l13_xboole_0, axiom,
% 0.54/0.75    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.54/0.75  thf('39', plain,
% 0.54/0.75      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.54/0.75      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.54/0.75  thf('40', plain,
% 0.54/0.75      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))
% 0.54/0.75        | ((u1_struct_0 @ sk_B_1) = (k1_xboole_0)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['38', '39'])).
% 0.54/0.75  thf('41', plain,
% 0.54/0.75      ((((k2_struct_0 @ sk_B_1) = (k1_xboole_0))
% 0.54/0.75        | ~ (l1_struct_0 @ sk_B_1)
% 0.54/0.75        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.54/0.75      inference('sup+', [status(thm)], ['13', '40'])).
% 0.54/0.75  thf('42', plain, ((l1_struct_0 @ sk_B_1)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('43', plain,
% 0.54/0.75      ((((k2_struct_0 @ sk_B_1) = (k1_xboole_0))
% 0.54/0.75        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.54/0.75      inference('demod', [status(thm)], ['41', '42'])).
% 0.54/0.75  thf('44', plain,
% 0.54/0.75      ((((k2_struct_0 @ sk_A) = (k1_xboole_0))
% 0.54/0.75        | ((k2_struct_0 @ sk_B_1) != (k1_xboole_0)))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('45', plain,
% 0.54/0.75      ((((k2_struct_0 @ sk_B_1) != (k1_xboole_0)))
% 0.54/0.75         <= (~ (((k2_struct_0 @ sk_B_1) = (k1_xboole_0))))),
% 0.54/0.75      inference('split', [status(esa)], ['44'])).
% 0.54/0.75  thf('46', plain,
% 0.54/0.75      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.54/0.75         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('split', [status(esa)], ['44'])).
% 0.54/0.75  thf('47', plain,
% 0.54/0.75      ((r1_tarski @ sk_C @ 
% 0.54/0.75        (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1)))),
% 0.54/0.75      inference('demod', [status(thm)], ['5', '6'])).
% 0.54/0.75  thf('48', plain,
% 0.54/0.75      (((r1_tarski @ sk_C @ 
% 0.54/0.75         (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B_1))))
% 0.54/0.75         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('sup+', [status(thm)], ['46', '47'])).
% 0.54/0.75  thf('49', plain,
% 0.54/0.75      (![X1 : $i, X3 : $i]:
% 0.54/0.75         ((m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X3)) | ~ (r1_tarski @ X1 @ X3))),
% 0.54/0.75      inference('cnf', [status(esa)], [t3_subset])).
% 0.54/0.75  thf('50', plain,
% 0.54/0.75      (((m1_subset_1 @ sk_C @ 
% 0.54/0.75         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B_1)))))
% 0.54/0.75         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('sup-', [status(thm)], ['48', '49'])).
% 0.54/0.75  thf('51', plain,
% 0.54/0.75      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.54/0.75         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.54/0.75          | (v1_partfun1 @ X28 @ X29)
% 0.54/0.75          | ~ (v1_funct_2 @ X28 @ X29 @ X30)
% 0.54/0.75          | ~ (v1_funct_1 @ X28)
% 0.54/0.75          | (v1_xboole_0 @ X30))),
% 0.54/0.75      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.54/0.75  thf('52', plain,
% 0.54/0.75      ((((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.54/0.75         | ~ (v1_funct_1 @ sk_C)
% 0.54/0.75         | ~ (v1_funct_2 @ sk_C @ k1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.54/0.75         | (v1_partfun1 @ sk_C @ k1_xboole_0)))
% 0.54/0.75         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('sup-', [status(thm)], ['50', '51'])).
% 0.54/0.75  thf('53', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('54', plain,
% 0.54/0.75      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.54/0.75         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('split', [status(esa)], ['44'])).
% 0.54/0.75  thf('55', plain,
% 0.54/0.75      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 0.54/0.75      inference('demod', [status(thm)], ['24', '25'])).
% 0.54/0.75  thf('56', plain,
% 0.54/0.75      (((v1_funct_2 @ sk_C @ k1_xboole_0 @ (u1_struct_0 @ sk_B_1)))
% 0.54/0.75         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('sup+', [status(thm)], ['54', '55'])).
% 0.54/0.75  thf('57', plain,
% 0.54/0.75      ((((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.54/0.75         | (v1_partfun1 @ sk_C @ k1_xboole_0)))
% 0.54/0.75         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('demod', [status(thm)], ['52', '53', '56'])).
% 0.54/0.75  thf(t6_mcart_1, axiom,
% 0.54/0.75    (![A:$i]:
% 0.54/0.75     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.54/0.75          ( ![B:$i]:
% 0.54/0.75            ( ~( ( r2_hidden @ B @ A ) & 
% 0.54/0.75                 ( ![C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.54/0.75                   ( ( ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ E ) & 
% 0.54/0.75                       ( r2_hidden @ E @ F ) & ( r2_hidden @ F @ G ) & 
% 0.54/0.75                       ( r2_hidden @ G @ B ) ) =>
% 0.54/0.75                     ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 0.54/0.75  thf('58', plain,
% 0.54/0.75      (![X22 : $i]:
% 0.54/0.75         (((X22) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X22) @ X22))),
% 0.54/0.75      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.54/0.75  thf('59', plain,
% 0.54/0.75      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.54/0.75      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.54/0.75  thf('60', plain,
% 0.54/0.75      (((m1_subset_1 @ sk_C @ 
% 0.54/0.75         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B_1)))))
% 0.54/0.75         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('sup-', [status(thm)], ['48', '49'])).
% 0.54/0.75  thf('61', plain,
% 0.54/0.75      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.54/0.75         ((v4_relat_1 @ X13 @ X14)
% 0.54/0.75          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.54/0.75      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.54/0.75  thf('62', plain,
% 0.54/0.75      (((v4_relat_1 @ sk_C @ k1_xboole_0))
% 0.54/0.75         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('sup-', [status(thm)], ['60', '61'])).
% 0.54/0.75  thf(d18_relat_1, axiom,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( v1_relat_1 @ B ) =>
% 0.54/0.75       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.54/0.75  thf('63', plain,
% 0.54/0.75      (![X9 : $i, X10 : $i]:
% 0.54/0.75         (~ (v4_relat_1 @ X9 @ X10)
% 0.54/0.75          | (r1_tarski @ (k1_relat_1 @ X9) @ X10)
% 0.54/0.75          | ~ (v1_relat_1 @ X9))),
% 0.54/0.75      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.54/0.75  thf('64', plain,
% 0.54/0.75      (((~ (v1_relat_1 @ sk_C)
% 0.54/0.75         | (r1_tarski @ (k1_relat_1 @ sk_C) @ k1_xboole_0)))
% 0.54/0.75         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('sup-', [status(thm)], ['62', '63'])).
% 0.54/0.75  thf('65', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.75      inference('demod', [status(thm)], ['32', '33'])).
% 0.54/0.75  thf('66', plain,
% 0.54/0.75      (((r1_tarski @ (k1_relat_1 @ sk_C) @ k1_xboole_0))
% 0.54/0.75         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('demod', [status(thm)], ['64', '65'])).
% 0.54/0.75  thf('67', plain,
% 0.54/0.75      (![X1 : $i, X3 : $i]:
% 0.54/0.75         ((m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X3)) | ~ (r1_tarski @ X1 @ X3))),
% 0.54/0.75      inference('cnf', [status(esa)], [t3_subset])).
% 0.54/0.75  thf('68', plain,
% 0.54/0.75      (((m1_subset_1 @ (k1_relat_1 @ sk_C) @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.54/0.75         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('sup-', [status(thm)], ['66', '67'])).
% 0.54/0.75  thf(t5_subset, axiom,
% 0.54/0.75    (![A:$i,B:$i,C:$i]:
% 0.54/0.75     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.54/0.75          ( v1_xboole_0 @ C ) ) ))).
% 0.54/0.75  thf('69', plain,
% 0.54/0.75      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.54/0.75         (~ (r2_hidden @ X4 @ X5)
% 0.54/0.75          | ~ (v1_xboole_0 @ X6)
% 0.54/0.75          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.54/0.75      inference('cnf', [status(esa)], [t5_subset])).
% 0.54/0.75  thf('70', plain,
% 0.54/0.75      ((![X0 : $i]:
% 0.54/0.75          (~ (v1_xboole_0 @ k1_xboole_0)
% 0.54/0.75           | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C))))
% 0.54/0.75         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('sup-', [status(thm)], ['68', '69'])).
% 0.54/0.75  thf('71', plain,
% 0.54/0.75      ((![X0 : $i, X1 : $i]:
% 0.54/0.75          (~ (v1_xboole_0 @ X0)
% 0.54/0.75           | ~ (v1_xboole_0 @ X0)
% 0.54/0.75           | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_C))))
% 0.54/0.75         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('sup-', [status(thm)], ['59', '70'])).
% 0.54/0.75  thf('72', plain,
% 0.54/0.75      ((![X0 : $i, X1 : $i]:
% 0.54/0.75          (~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_C)) | ~ (v1_xboole_0 @ X0)))
% 0.54/0.75         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('simplify', [status(thm)], ['71'])).
% 0.54/0.75  thf('73', plain,
% 0.54/0.75      ((![X0 : $i]:
% 0.54/0.75          (((k1_relat_1 @ sk_C) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.54/0.75         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('sup-', [status(thm)], ['58', '72'])).
% 0.54/0.75  thf('74', plain,
% 0.54/0.75      ((((v1_partfun1 @ sk_C @ k1_xboole_0)
% 0.54/0.75         | ((k1_relat_1 @ sk_C) = (k1_xboole_0))))
% 0.54/0.75         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('sup-', [status(thm)], ['57', '73'])).
% 0.54/0.75  thf('75', plain,
% 0.54/0.75      (![X31 : $i, X32 : $i]:
% 0.54/0.75         (~ (v1_partfun1 @ X32 @ X31)
% 0.54/0.75          | ((k1_relat_1 @ X32) = (X31))
% 0.54/0.75          | ~ (v4_relat_1 @ X32 @ X31)
% 0.54/0.75          | ~ (v1_relat_1 @ X32))),
% 0.54/0.75      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.54/0.75  thf('76', plain,
% 0.54/0.75      (((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 0.54/0.75         | ~ (v1_relat_1 @ sk_C)
% 0.54/0.75         | ~ (v4_relat_1 @ sk_C @ k1_xboole_0)
% 0.54/0.75         | ((k1_relat_1 @ sk_C) = (k1_xboole_0))))
% 0.54/0.75         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('sup-', [status(thm)], ['74', '75'])).
% 0.54/0.75  thf('77', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.75      inference('demod', [status(thm)], ['32', '33'])).
% 0.54/0.75  thf('78', plain,
% 0.54/0.75      (((v4_relat_1 @ sk_C @ k1_xboole_0))
% 0.54/0.75         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('sup-', [status(thm)], ['60', '61'])).
% 0.54/0.75  thf('79', plain,
% 0.54/0.75      (((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 0.54/0.75         | ((k1_relat_1 @ sk_C) = (k1_xboole_0))))
% 0.54/0.75         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.54/0.75  thf('80', plain,
% 0.54/0.75      ((((k1_relat_1 @ sk_C) = (k1_xboole_0)))
% 0.54/0.75         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('simplify', [status(thm)], ['79'])).
% 0.54/0.75  thf('81', plain,
% 0.54/0.75      (![X33 : $i]:
% 0.54/0.75         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.54/0.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.54/0.75  thf('82', plain,
% 0.54/0.75      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.54/0.75         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('split', [status(esa)], ['44'])).
% 0.54/0.75  thf('83', plain,
% 0.54/0.75      (![X33 : $i]:
% 0.54/0.75         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.54/0.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.54/0.75  thf('84', plain,
% 0.54/0.75      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C @ 
% 0.54/0.75         (k2_struct_0 @ sk_B_1)) != (k2_struct_0 @ sk_A))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('85', plain,
% 0.54/0.75      ((((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C @ 
% 0.54/0.75          (k2_struct_0 @ sk_B_1)) != (k2_struct_0 @ sk_A))
% 0.54/0.75        | ~ (l1_struct_0 @ sk_A))),
% 0.54/0.75      inference('sup-', [status(thm)], ['83', '84'])).
% 0.54/0.75  thf('86', plain, ((l1_struct_0 @ sk_A)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('87', plain,
% 0.54/0.75      (((k8_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C @ 
% 0.54/0.75         (k2_struct_0 @ sk_B_1)) != (k2_struct_0 @ sk_A))),
% 0.54/0.75      inference('demod', [status(thm)], ['85', '86'])).
% 0.54/0.75  thf('88', plain,
% 0.54/0.75      ((((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ sk_C @ 
% 0.54/0.75          (k2_struct_0 @ sk_B_1)) != (k2_struct_0 @ sk_A)))
% 0.54/0.75         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('sup-', [status(thm)], ['82', '87'])).
% 0.54/0.75  thf('89', plain,
% 0.54/0.75      ((((k2_struct_0 @ sk_A) = (k1_xboole_0)))
% 0.54/0.75         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('split', [status(esa)], ['44'])).
% 0.54/0.75  thf('90', plain,
% 0.54/0.75      ((((k8_relset_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ sk_C @ 
% 0.54/0.75          (k2_struct_0 @ sk_B_1)) != (k1_xboole_0)))
% 0.54/0.75         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('demod', [status(thm)], ['88', '89'])).
% 0.54/0.75  thf('91', plain,
% 0.54/0.75      (((((k8_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B_1) @ sk_C @ 
% 0.54/0.75           (k2_struct_0 @ sk_B_1)) != (k1_xboole_0))
% 0.54/0.75         | ~ (l1_struct_0 @ sk_B_1)))
% 0.54/0.75         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('sup-', [status(thm)], ['81', '90'])).
% 0.54/0.75  thf('92', plain, ((l1_struct_0 @ sk_B_1)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('93', plain,
% 0.54/0.75      ((((k8_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B_1) @ sk_C @ 
% 0.54/0.75          (k2_struct_0 @ sk_B_1)) != (k1_xboole_0)))
% 0.54/0.75         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('demod', [status(thm)], ['91', '92'])).
% 0.54/0.75  thf('94', plain,
% 0.54/0.75      (![X33 : $i]:
% 0.54/0.75         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.54/0.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.54/0.75  thf('95', plain,
% 0.54/0.75      (((r1_tarski @ sk_C @ 
% 0.54/0.75         (k2_zfmisc_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_B_1))))
% 0.54/0.75         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('sup+', [status(thm)], ['46', '47'])).
% 0.54/0.75  thf('96', plain,
% 0.54/0.75      ((((r1_tarski @ sk_C @ 
% 0.54/0.75          (k2_zfmisc_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B_1)))
% 0.54/0.75         | ~ (l1_struct_0 @ sk_B_1)))
% 0.54/0.75         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('sup+', [status(thm)], ['94', '95'])).
% 0.54/0.75  thf('97', plain, ((l1_struct_0 @ sk_B_1)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('98', plain,
% 0.54/0.75      (((r1_tarski @ sk_C @ 
% 0.54/0.75         (k2_zfmisc_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B_1))))
% 0.54/0.75         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('demod', [status(thm)], ['96', '97'])).
% 0.54/0.75  thf('99', plain,
% 0.54/0.75      (![X1 : $i, X3 : $i]:
% 0.54/0.75         ((m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X3)) | ~ (r1_tarski @ X1 @ X3))),
% 0.54/0.75      inference('cnf', [status(esa)], [t3_subset])).
% 0.54/0.75  thf('100', plain,
% 0.54/0.75      (((m1_subset_1 @ sk_C @ 
% 0.54/0.75         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B_1)))))
% 0.54/0.75         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('sup-', [status(thm)], ['98', '99'])).
% 0.54/0.75  thf(t38_relset_1, axiom,
% 0.54/0.75    (![A:$i,B:$i,C:$i]:
% 0.54/0.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.75       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.54/0.75         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.54/0.75  thf('101', plain,
% 0.54/0.75      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.54/0.75         (((k8_relset_1 @ X19 @ X20 @ X21 @ X20)
% 0.54/0.75            = (k1_relset_1 @ X19 @ X20 @ X21))
% 0.54/0.75          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.54/0.75      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.54/0.75  thf('102', plain,
% 0.54/0.75      ((((k8_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B_1) @ sk_C @ 
% 0.54/0.75          (k2_struct_0 @ sk_B_1))
% 0.54/0.75          = (k1_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B_1) @ sk_C)))
% 0.54/0.75         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('sup-', [status(thm)], ['100', '101'])).
% 0.54/0.75  thf('103', plain,
% 0.54/0.75      (((m1_subset_1 @ sk_C @ 
% 0.54/0.75         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B_1)))))
% 0.54/0.75         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('sup-', [status(thm)], ['98', '99'])).
% 0.54/0.75  thf(redefinition_k1_relset_1, axiom,
% 0.54/0.75    (![A:$i,B:$i,C:$i]:
% 0.54/0.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.75       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.54/0.75  thf('104', plain,
% 0.54/0.75      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.54/0.75         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 0.54/0.75          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.54/0.75      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.54/0.75  thf('105', plain,
% 0.54/0.75      ((((k1_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B_1) @ sk_C)
% 0.54/0.75          = (k1_relat_1 @ sk_C)))
% 0.54/0.75         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('sup-', [status(thm)], ['103', '104'])).
% 0.54/0.75  thf('106', plain,
% 0.54/0.75      ((((k8_relset_1 @ k1_xboole_0 @ (k2_struct_0 @ sk_B_1) @ sk_C @ 
% 0.54/0.75          (k2_struct_0 @ sk_B_1)) = (k1_relat_1 @ sk_C)))
% 0.54/0.75         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('demod', [status(thm)], ['102', '105'])).
% 0.54/0.75  thf('107', plain,
% 0.54/0.75      ((((k1_relat_1 @ sk_C) != (k1_xboole_0)))
% 0.54/0.75         <= ((((k2_struct_0 @ sk_A) = (k1_xboole_0))))),
% 0.54/0.75      inference('demod', [status(thm)], ['93', '106'])).
% 0.54/0.75  thf('108', plain, (~ (((k2_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.54/0.75      inference('simplify_reflect-', [status(thm)], ['80', '107'])).
% 0.54/0.75  thf('109', plain,
% 0.54/0.75      (~ (((k2_struct_0 @ sk_B_1) = (k1_xboole_0))) | 
% 0.54/0.75       (((k2_struct_0 @ sk_A) = (k1_xboole_0)))),
% 0.54/0.75      inference('split', [status(esa)], ['44'])).
% 0.54/0.75  thf('110', plain, (~ (((k2_struct_0 @ sk_B_1) = (k1_xboole_0)))),
% 0.54/0.75      inference('sat_resolution*', [status(thm)], ['108', '109'])).
% 0.54/0.75  thf('111', plain, (((k2_struct_0 @ sk_B_1) != (k1_xboole_0))),
% 0.54/0.75      inference('simpl_trail', [status(thm)], ['45', '110'])).
% 0.54/0.75  thf('112', plain,
% 0.54/0.75      ((((k1_xboole_0) != (k1_xboole_0))
% 0.54/0.75        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['43', '111'])).
% 0.54/0.75  thf('113', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.54/0.75      inference('simplify', [status(thm)], ['112'])).
% 0.54/0.75  thf('114', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_C @ 
% 0.54/0.75        (k1_zfmisc_1 @ 
% 0.54/0.75         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B_1))))),
% 0.54/0.75      inference('demod', [status(thm)], ['12', '113'])).
% 0.54/0.75  thf('115', plain,
% 0.54/0.75      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.54/0.75         (((k8_relset_1 @ X19 @ X20 @ X21 @ X20)
% 0.54/0.75            = (k1_relset_1 @ X19 @ X20 @ X21))
% 0.54/0.75          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.54/0.75      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.54/0.75  thf('116', plain,
% 0.54/0.75      (((k8_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B_1) @ sk_C @ 
% 0.54/0.75         (k2_struct_0 @ sk_B_1))
% 0.54/0.75         = (k1_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B_1) @ sk_C))),
% 0.54/0.75      inference('sup-', [status(thm)], ['114', '115'])).
% 0.54/0.75  thf('117', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_C @ 
% 0.54/0.75        (k1_zfmisc_1 @ 
% 0.54/0.75         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1))))),
% 0.54/0.75      inference('sup-', [status(thm)], ['10', '11'])).
% 0.54/0.75  thf('118', plain,
% 0.54/0.75      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.54/0.75         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 0.54/0.75          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.54/0.75      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.54/0.75  thf('119', plain,
% 0.54/0.75      (((k1_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1) @ sk_C)
% 0.54/0.75         = (k1_relat_1 @ sk_C))),
% 0.54/0.75      inference('sup-', [status(thm)], ['117', '118'])).
% 0.54/0.75  thf('120', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.54/0.75      inference('simplify', [status(thm)], ['112'])).
% 0.54/0.75  thf('121', plain,
% 0.54/0.75      (((k1_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B_1) @ sk_C)
% 0.54/0.75         = (k1_relat_1 @ sk_C))),
% 0.54/0.75      inference('demod', [status(thm)], ['119', '120'])).
% 0.54/0.75  thf('122', plain,
% 0.54/0.75      (((k8_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B_1) @ sk_C @ 
% 0.54/0.75         (k2_struct_0 @ sk_B_1)) = (k1_relat_1 @ sk_C))),
% 0.54/0.75      inference('demod', [status(thm)], ['116', '121'])).
% 0.54/0.75  thf('123', plain,
% 0.54/0.75      (![X33 : $i]:
% 0.54/0.75         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.54/0.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.54/0.75  thf('124', plain,
% 0.54/0.75      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1) @ sk_C @ 
% 0.54/0.75         (k2_struct_0 @ sk_B_1)) != (k2_struct_0 @ sk_A))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('125', plain,
% 0.54/0.75      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1) @ sk_C @ 
% 0.54/0.75          (k2_struct_0 @ sk_B_1)) != (k2_struct_0 @ sk_A))
% 0.54/0.75        | ~ (l1_struct_0 @ sk_B_1))),
% 0.54/0.75      inference('sup-', [status(thm)], ['123', '124'])).
% 0.54/0.75  thf('126', plain, ((l1_struct_0 @ sk_B_1)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('127', plain,
% 0.54/0.75      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1) @ sk_C @ 
% 0.54/0.75         (k2_struct_0 @ sk_B_1)) != (k2_struct_0 @ sk_A))),
% 0.54/0.75      inference('demod', [status(thm)], ['125', '126'])).
% 0.54/0.75  thf('128', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.54/0.75      inference('simplify', [status(thm)], ['112'])).
% 0.54/0.75  thf('129', plain,
% 0.54/0.75      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B_1) @ sk_C @ 
% 0.54/0.75         (k2_struct_0 @ sk_B_1)) != (k1_relat_1 @ sk_C))),
% 0.54/0.75      inference('demod', [status(thm)], ['127', '128'])).
% 0.54/0.75  thf('130', plain,
% 0.54/0.75      (![X33 : $i]:
% 0.54/0.75         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.54/0.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.54/0.75  thf('131', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_C @ 
% 0.54/0.75        (k1_zfmisc_1 @ 
% 0.54/0.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('132', plain,
% 0.54/0.75      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.54/0.75         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.54/0.75          | (v1_partfun1 @ X28 @ X29)
% 0.54/0.75          | ~ (v1_funct_2 @ X28 @ X29 @ X30)
% 0.54/0.75          | ~ (v1_funct_1 @ X28)
% 0.54/0.75          | (v1_xboole_0 @ X30))),
% 0.54/0.75      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.54/0.75  thf('133', plain,
% 0.54/0.75      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.54/0.75        | ~ (v1_funct_1 @ sk_C)
% 0.54/0.75        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))
% 0.54/0.75        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['131', '132'])).
% 0.54/0.75  thf('134', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('135', plain,
% 0.54/0.75      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('136', plain,
% 0.54/0.75      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.54/0.75        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.54/0.75      inference('demod', [status(thm)], ['133', '134', '135'])).
% 0.54/0.75  thf('137', plain,
% 0.54/0.75      (![X31 : $i, X32 : $i]:
% 0.54/0.75         (~ (v1_partfun1 @ X32 @ X31)
% 0.54/0.75          | ((k1_relat_1 @ X32) = (X31))
% 0.54/0.75          | ~ (v4_relat_1 @ X32 @ X31)
% 0.54/0.75          | ~ (v1_relat_1 @ X32))),
% 0.54/0.75      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.54/0.75  thf('138', plain,
% 0.54/0.75      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.54/0.75        | ~ (v1_relat_1 @ sk_C)
% 0.54/0.75        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.54/0.75        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['136', '137'])).
% 0.54/0.75  thf('139', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.75      inference('demod', [status(thm)], ['32', '33'])).
% 0.54/0.75  thf('140', plain,
% 0.54/0.75      ((m1_subset_1 @ sk_C @ 
% 0.54/0.75        (k1_zfmisc_1 @ 
% 0.54/0.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('141', plain,
% 0.54/0.75      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.54/0.75         ((v4_relat_1 @ X13 @ X14)
% 0.54/0.75          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.54/0.75      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.54/0.75  thf('142', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.54/0.75      inference('sup-', [status(thm)], ['140', '141'])).
% 0.54/0.75  thf('143', plain,
% 0.54/0.75      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.54/0.75        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.54/0.75      inference('demod', [status(thm)], ['138', '139', '142'])).
% 0.54/0.75  thf('144', plain,
% 0.54/0.75      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.54/0.75      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.54/0.75  thf('145', plain,
% 0.54/0.75      ((((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))
% 0.54/0.75        | ((u1_struct_0 @ sk_B_1) = (k1_xboole_0)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['143', '144'])).
% 0.54/0.75  thf('146', plain,
% 0.54/0.75      ((((k2_struct_0 @ sk_B_1) = (k1_xboole_0))
% 0.54/0.75        | ~ (l1_struct_0 @ sk_B_1)
% 0.54/0.75        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.54/0.75      inference('sup+', [status(thm)], ['130', '145'])).
% 0.54/0.75  thf('147', plain, ((l1_struct_0 @ sk_B_1)),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.75  thf('148', plain,
% 0.54/0.75      ((((k2_struct_0 @ sk_B_1) = (k1_xboole_0))
% 0.54/0.75        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.54/0.75      inference('demod', [status(thm)], ['146', '147'])).
% 0.54/0.75  thf('149', plain, (((k2_struct_0 @ sk_B_1) != (k1_xboole_0))),
% 0.54/0.75      inference('simpl_trail', [status(thm)], ['45', '110'])).
% 0.54/0.75  thf('150', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.54/0.75      inference('simplify_reflect-', [status(thm)], ['148', '149'])).
% 0.54/0.75  thf('151', plain,
% 0.54/0.75      (((k8_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B_1) @ sk_C @ 
% 0.54/0.75         (k2_struct_0 @ sk_B_1)) != (k1_relat_1 @ sk_C))),
% 0.54/0.75      inference('demod', [status(thm)], ['129', '150'])).
% 0.54/0.75  thf('152', plain, ($false),
% 0.54/0.75      inference('simplify_reflect-', [status(thm)], ['122', '151'])).
% 0.54/0.75  
% 0.54/0.75  % SZS output end Refutation
% 0.54/0.75  
% 0.54/0.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
