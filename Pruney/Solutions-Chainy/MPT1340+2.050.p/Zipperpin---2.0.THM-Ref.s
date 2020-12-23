%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Y1VSQ0TdMJ

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:14 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :  235 (1327 expanded)
%              Number of leaves         :   46 ( 418 expanded)
%              Depth                    :   21
%              Number of atoms          : 1931 (26773 expanded)
%              Number of equality atoms :  100 ( 702 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
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

thf('2',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
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

thf('10',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( v1_partfun1 @ X19 @ X20 )
      | ~ ( v1_funct_2 @ X19 @ X20 @ X21 )
      | ~ ( v1_funct_1 @ X19 )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('11',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('15',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_partfun1 @ X23 @ X22 )
      | ( ( k1_relat_1 @ X23 )
        = X22 )
      | ~ ( v4_relat_1 @ X23 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('16',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('21',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('23',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v4_relat_1 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('24',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','21','24'])).

thf('26',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( v1_partfun1 @ X19 @ X20 )
      | ~ ( v1_funct_2 @ X19 @ X20 @ X21 )
      | ~ ( v1_funct_1 @ X19 )
      | ( v1_xboole_0 @ X21 ) ) ),
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
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
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
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_partfun1 @ X23 @ X22 )
      | ( ( k1_relat_1 @ X23 )
        = X22 )
      | ~ ( v4_relat_1 @ X23 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
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
    inference(demod,[status(thm)],['19','20'])).

thf('43',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('44',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v4_relat_1 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
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
    ! [X32: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
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
    ! [X32: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
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

thf('61',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('62',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['8','59','60','61'])).

thf('63',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('65',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

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

thf('68',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k2_relset_1 @ X34 @ X33 @ X35 )
       != X33 )
      | ~ ( v2_funct_1 @ X35 )
      | ( ( k2_tops_2 @ X34 @ X33 @ X35 )
        = ( k2_funct_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X34 @ X33 )
      | ~ ( v1_funct_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('69',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('72',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('73',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('77',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_funct_1 @ X5 )
        = ( k4_relat_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('78',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['19','20'])).

thf('80',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('84',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('85',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['83','88'])).

thf('90',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['69','70','75','81','82','91'])).

thf('93',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

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

thf('95',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k2_relset_1 @ X30 @ X29 @ X28 )
       != X29 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('96',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('99',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('100',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('101',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['96','97','98','99','100','101'])).

thf('103',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k2_relset_1 @ X34 @ X33 @ X35 )
       != X33 )
      | ~ ( v2_funct_1 @ X35 )
      | ( ( k2_tops_2 @ X34 @ X33 @ X35 )
        = ( k2_funct_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X34 @ X33 )
      | ~ ( v1_funct_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('105',plain,
    ( ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('107',plain,(
    ! [X6: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('108',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['19','20'])).

thf('110',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('112',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('113',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k2_relset_1 @ X30 @ X29 @ X28 )
       != X29 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X28 ) @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
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
    inference(demod,[status(thm)],['73','74'])).

thf('117',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('118',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('119',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['114','115','116','117','118','119'])).

thf('121',plain,(
    v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('123',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X12 ) )
        = X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('124',plain,
    ( ( ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['122','123'])).

thf('125',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['19','20'])).

thf('126',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['124','125','126','127'])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('129',plain,(
    ! [X4: $i] :
      ( ( ( k1_relat_1 @ X4 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('130',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('131',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X11 ) @ X11 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('132',plain,
    ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['130','131'])).

thf('133',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['19','20'])).

thf('134',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ sk_C )
    = ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['132','133','134','135'])).

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

thf('137',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( v2_funct_1 @ X9 )
      | ( ( k2_relat_1 @ X9 )
       != ( k1_relat_1 @ X10 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('138',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( v2_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('139',plain,(
    ! [X8: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('140',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['19','20'])).

thf('141',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('143',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('144',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('145',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['143','144'])).

thf('146',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['19','20'])).

thf('147',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['145','146','147'])).

thf('149',plain,
    ( ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( v2_funct_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['138','139','140','141','142','148'])).

thf('150',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ( v2_funct_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['129','149'])).

thf('151',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['19','20'])).

thf('152',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ( v2_funct_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,(
    v2_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['152'])).

thf('154',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('155',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k2_relset_1 @ X17 @ X18 @ X16 )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('156',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('158',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_funct_1 @ X5 )
        = ( k4_relat_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('159',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ( ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) )
      = ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['145','146','147'])).

thf('161',plain,
    ( ( ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) )
      = ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['124','125','126','127'])).

thf('163',plain,
    ( ( sk_C
      = ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,(
    v2_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['152'])).

thf('165',plain,
    ( sk_C
    = ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X4: $i] :
      ( ( ( k2_relat_1 @ X4 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('167',plain,
    ( ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['165','166'])).

thf('168',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['145','146','147'])).

thf('169',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['167','168'])).

thf('170',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('171',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['169','170'])).

thf('172',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['156','171'])).

thf('173',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
      = sk_C )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['105','111','121','128','153','172'])).

thf('174',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
    = sk_C ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['62','93','174'])).

thf('176',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('177',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(reflexivity_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_funct_2 @ A @ B @ C @ C ) ) )).

thf('178',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( r2_funct_2 @ X24 @ X25 @ X26 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_2 @ X27 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_funct_2])).

thf('179',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['179','180','181'])).

thf('183',plain,
    ( ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['176','182'])).

thf('184',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('186',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['183','184','185'])).

thf('187',plain,(
    $false ),
    inference(demod,[status(thm)],['175','186'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Y1VSQ0TdMJ
% 0.17/0.36  % Computer   : n001.cluster.edu
% 0.17/0.36  % Model      : x86_64 x86_64
% 0.17/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.36  % Memory     : 8042.1875MB
% 0.17/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.36  % CPULimit   : 60
% 0.17/0.36  % DateTime   : Tue Dec  1 13:24:30 EST 2020
% 0.17/0.37  % CPUTime    : 
% 0.17/0.37  % Running portfolio for 600 s
% 0.17/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.37  % Number of cores: 8
% 0.17/0.37  % Python version: Python 3.6.8
% 0.17/0.37  % Running in FO mode
% 0.46/0.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.69  % Solved by: fo/fo7.sh
% 0.46/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.69  % done 405 iterations in 0.213s
% 0.46/0.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.69  % SZS output start Refutation
% 0.46/0.69  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.46/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.69  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.46/0.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.69  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.46/0.69  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.46/0.69  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.69  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.46/0.69  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.69  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.69  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.69  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.46/0.69  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.46/0.69  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.69  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.46/0.69  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.69  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.46/0.69  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.46/0.69  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.46/0.69  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.69  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.46/0.69  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.69  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.46/0.69  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.46/0.69  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.69  thf(d3_struct_0, axiom,
% 0.46/0.69    (![A:$i]:
% 0.46/0.69     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.46/0.69  thf('0', plain,
% 0.46/0.69      (![X31 : $i]:
% 0.46/0.69         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.46/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.69  thf('1', plain,
% 0.46/0.69      (![X31 : $i]:
% 0.46/0.69         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.46/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.69  thf(t64_tops_2, conjecture,
% 0.46/0.69    (![A:$i]:
% 0.46/0.69     ( ( l1_struct_0 @ A ) =>
% 0.46/0.69       ( ![B:$i]:
% 0.46/0.69         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.46/0.69           ( ![C:$i]:
% 0.46/0.69             ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.69                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.46/0.69                 ( m1_subset_1 @
% 0.46/0.69                   C @ 
% 0.46/0.69                   ( k1_zfmisc_1 @
% 0.46/0.69                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.46/0.69               ( ( ( ( k2_relset_1 @
% 0.46/0.69                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.46/0.69                     ( k2_struct_0 @ B ) ) & 
% 0.46/0.69                   ( v2_funct_1 @ C ) ) =>
% 0.46/0.69                 ( r2_funct_2 @
% 0.46/0.69                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.46/0.69                   ( k2_tops_2 @
% 0.46/0.69                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.46/0.69                     ( k2_tops_2 @
% 0.46/0.69                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.46/0.69                   C ) ) ) ) ) ) ))).
% 0.46/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.69    (~( ![A:$i]:
% 0.46/0.69        ( ( l1_struct_0 @ A ) =>
% 0.46/0.69          ( ![B:$i]:
% 0.46/0.69            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.46/0.69              ( ![C:$i]:
% 0.46/0.69                ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.69                    ( v1_funct_2 @
% 0.46/0.69                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.46/0.69                    ( m1_subset_1 @
% 0.46/0.69                      C @ 
% 0.46/0.69                      ( k1_zfmisc_1 @
% 0.46/0.69                        ( k2_zfmisc_1 @
% 0.46/0.69                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.46/0.69                  ( ( ( ( k2_relset_1 @
% 0.46/0.69                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.46/0.69                        ( k2_struct_0 @ B ) ) & 
% 0.46/0.69                      ( v2_funct_1 @ C ) ) =>
% 0.46/0.69                    ( r2_funct_2 @
% 0.46/0.69                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.46/0.69                      ( k2_tops_2 @
% 0.46/0.69                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.46/0.69                        ( k2_tops_2 @
% 0.46/0.69                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.46/0.69                      C ) ) ) ) ) ) ) )),
% 0.46/0.69    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.46/0.69  thf('2', plain,
% 0.46/0.69      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.69          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.69           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.69          sk_C)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('3', plain,
% 0.46/0.69      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.69           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.69            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.69           sk_C)
% 0.46/0.69        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.69      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.69  thf('4', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('5', plain,
% 0.46/0.69      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.69          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.69           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.69          sk_C)),
% 0.46/0.69      inference('demod', [status(thm)], ['3', '4'])).
% 0.46/0.69  thf('6', plain,
% 0.46/0.69      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.69           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.69            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.69           sk_C)
% 0.46/0.69        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.69      inference('sup-', [status(thm)], ['0', '5'])).
% 0.46/0.69  thf('7', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('8', plain,
% 0.46/0.69      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.69          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.69           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.69          sk_C)),
% 0.46/0.69      inference('demod', [status(thm)], ['6', '7'])).
% 0.46/0.69  thf('9', plain,
% 0.46/0.69      ((m1_subset_1 @ sk_C @ 
% 0.46/0.69        (k1_zfmisc_1 @ 
% 0.46/0.69         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf(cc5_funct_2, axiom,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.46/0.69       ( ![C:$i]:
% 0.46/0.69         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.69           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.46/0.69             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.46/0.69  thf('10', plain,
% 0.46/0.69      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.46/0.69         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.46/0.69          | (v1_partfun1 @ X19 @ X20)
% 0.46/0.69          | ~ (v1_funct_2 @ X19 @ X20 @ X21)
% 0.46/0.69          | ~ (v1_funct_1 @ X19)
% 0.46/0.69          | (v1_xboole_0 @ X21))),
% 0.46/0.69      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.46/0.69  thf('11', plain,
% 0.46/0.69      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.69        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.69        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.69        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['9', '10'])).
% 0.46/0.69  thf('12', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('13', plain,
% 0.46/0.69      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('14', plain,
% 0.46/0.69      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.69        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.46/0.69      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.46/0.69  thf(d4_partfun1, axiom,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.46/0.69       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.46/0.69  thf('15', plain,
% 0.46/0.69      (![X22 : $i, X23 : $i]:
% 0.46/0.69         (~ (v1_partfun1 @ X23 @ X22)
% 0.46/0.69          | ((k1_relat_1 @ X23) = (X22))
% 0.46/0.69          | ~ (v4_relat_1 @ X23 @ X22)
% 0.46/0.69          | ~ (v1_relat_1 @ X23))),
% 0.46/0.69      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.46/0.69  thf('16', plain,
% 0.46/0.69      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.69        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.69        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.46/0.69        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['14', '15'])).
% 0.46/0.69  thf('17', plain,
% 0.46/0.69      ((m1_subset_1 @ sk_C @ 
% 0.46/0.69        (k1_zfmisc_1 @ 
% 0.46/0.69         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf(cc2_relat_1, axiom,
% 0.46/0.69    (![A:$i]:
% 0.46/0.69     ( ( v1_relat_1 @ A ) =>
% 0.46/0.69       ( ![B:$i]:
% 0.46/0.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.46/0.69  thf('18', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]:
% 0.46/0.69         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.46/0.69          | (v1_relat_1 @ X0)
% 0.46/0.69          | ~ (v1_relat_1 @ X1))),
% 0.46/0.69      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.46/0.69  thf('19', plain,
% 0.46/0.69      ((~ (v1_relat_1 @ 
% 0.46/0.69           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.46/0.69        | (v1_relat_1 @ sk_C))),
% 0.46/0.69      inference('sup-', [status(thm)], ['17', '18'])).
% 0.46/0.69  thf(fc6_relat_1, axiom,
% 0.46/0.69    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.46/0.69  thf('20', plain,
% 0.46/0.69      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.46/0.69      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.46/0.69  thf('21', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.69      inference('demod', [status(thm)], ['19', '20'])).
% 0.46/0.69  thf('22', plain,
% 0.46/0.69      ((m1_subset_1 @ sk_C @ 
% 0.46/0.69        (k1_zfmisc_1 @ 
% 0.46/0.69         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf(cc2_relset_1, axiom,
% 0.46/0.69    (![A:$i,B:$i,C:$i]:
% 0.46/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.69       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.46/0.69  thf('23', plain,
% 0.46/0.69      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.69         ((v4_relat_1 @ X13 @ X14)
% 0.46/0.69          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.46/0.69      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.69  thf('24', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.46/0.69      inference('sup-', [status(thm)], ['22', '23'])).
% 0.46/0.69  thf('25', plain,
% 0.46/0.69      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.69        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.46/0.69      inference('demod', [status(thm)], ['16', '21', '24'])).
% 0.46/0.69  thf('26', plain,
% 0.46/0.69      (![X31 : $i]:
% 0.46/0.69         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.46/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.69  thf('27', plain,
% 0.46/0.69      ((m1_subset_1 @ sk_C @ 
% 0.46/0.69        (k1_zfmisc_1 @ 
% 0.46/0.69         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('28', plain,
% 0.46/0.69      (((m1_subset_1 @ sk_C @ 
% 0.46/0.69         (k1_zfmisc_1 @ 
% 0.46/0.69          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.46/0.69        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.69      inference('sup+', [status(thm)], ['26', '27'])).
% 0.46/0.69  thf('29', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('30', plain,
% 0.46/0.69      ((m1_subset_1 @ sk_C @ 
% 0.46/0.69        (k1_zfmisc_1 @ 
% 0.46/0.69         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.69      inference('demod', [status(thm)], ['28', '29'])).
% 0.46/0.69  thf('31', plain,
% 0.46/0.69      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.46/0.69         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.46/0.69          | (v1_partfun1 @ X19 @ X20)
% 0.46/0.69          | ~ (v1_funct_2 @ X19 @ X20 @ X21)
% 0.46/0.69          | ~ (v1_funct_1 @ X19)
% 0.46/0.69          | (v1_xboole_0 @ X21))),
% 0.46/0.69      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.46/0.69  thf('32', plain,
% 0.46/0.69      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.69        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.69        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.69        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['30', '31'])).
% 0.46/0.69  thf('33', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('34', plain,
% 0.46/0.69      (![X31 : $i]:
% 0.46/0.69         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.46/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.69  thf('35', plain,
% 0.46/0.69      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('36', plain,
% 0.46/0.69      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.69        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.69      inference('sup+', [status(thm)], ['34', '35'])).
% 0.46/0.69  thf('37', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('38', plain,
% 0.46/0.69      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.69      inference('demod', [status(thm)], ['36', '37'])).
% 0.46/0.69  thf('39', plain,
% 0.46/0.69      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.69        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.46/0.69      inference('demod', [status(thm)], ['32', '33', '38'])).
% 0.46/0.69  thf('40', plain,
% 0.46/0.69      (![X22 : $i, X23 : $i]:
% 0.46/0.69         (~ (v1_partfun1 @ X23 @ X22)
% 0.46/0.69          | ((k1_relat_1 @ X23) = (X22))
% 0.46/0.69          | ~ (v4_relat_1 @ X23 @ X22)
% 0.46/0.69          | ~ (v1_relat_1 @ X23))),
% 0.46/0.69      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.46/0.69  thf('41', plain,
% 0.46/0.69      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.69        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.69        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.46/0.69        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['39', '40'])).
% 0.46/0.69  thf('42', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.69      inference('demod', [status(thm)], ['19', '20'])).
% 0.46/0.69  thf('43', plain,
% 0.46/0.69      ((m1_subset_1 @ sk_C @ 
% 0.46/0.69        (k1_zfmisc_1 @ 
% 0.46/0.69         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.69      inference('demod', [status(thm)], ['28', '29'])).
% 0.46/0.69  thf('44', plain,
% 0.46/0.69      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.69         ((v4_relat_1 @ X13 @ X14)
% 0.46/0.69          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.46/0.69      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.69  thf('45', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.46/0.69      inference('sup-', [status(thm)], ['43', '44'])).
% 0.46/0.69  thf('46', plain,
% 0.46/0.69      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.69        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.46/0.69      inference('demod', [status(thm)], ['41', '42', '45'])).
% 0.46/0.69  thf(fc2_struct_0, axiom,
% 0.46/0.69    (![A:$i]:
% 0.46/0.69     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.46/0.69       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.46/0.69  thf('47', plain,
% 0.46/0.69      (![X32 : $i]:
% 0.46/0.69         (~ (v1_xboole_0 @ (u1_struct_0 @ X32))
% 0.46/0.69          | ~ (l1_struct_0 @ X32)
% 0.46/0.69          | (v2_struct_0 @ X32))),
% 0.46/0.69      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.46/0.69  thf('48', plain,
% 0.46/0.69      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))
% 0.46/0.69        | (v2_struct_0 @ sk_B)
% 0.46/0.69        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.69      inference('sup-', [status(thm)], ['46', '47'])).
% 0.46/0.69  thf('49', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('50', plain,
% 0.46/0.69      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 0.46/0.69      inference('demod', [status(thm)], ['48', '49'])).
% 0.46/0.69  thf('51', plain, (~ (v2_struct_0 @ sk_B)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('52', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.69      inference('clc', [status(thm)], ['50', '51'])).
% 0.46/0.69  thf('53', plain,
% 0.46/0.69      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.69        | ((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)))),
% 0.46/0.69      inference('demod', [status(thm)], ['25', '52'])).
% 0.46/0.69  thf('54', plain,
% 0.46/0.69      (![X32 : $i]:
% 0.46/0.69         (~ (v1_xboole_0 @ (u1_struct_0 @ X32))
% 0.46/0.69          | ~ (l1_struct_0 @ X32)
% 0.46/0.69          | (v2_struct_0 @ X32))),
% 0.46/0.69      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.46/0.69  thf('55', plain,
% 0.46/0.69      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))
% 0.46/0.69        | (v2_struct_0 @ sk_B)
% 0.46/0.69        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.69      inference('sup-', [status(thm)], ['53', '54'])).
% 0.46/0.69  thf('56', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('57', plain,
% 0.46/0.69      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 0.46/0.69      inference('demod', [status(thm)], ['55', '56'])).
% 0.46/0.69  thf('58', plain, (~ (v2_struct_0 @ sk_B)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('59', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.46/0.69      inference('clc', [status(thm)], ['57', '58'])).
% 0.46/0.69  thf('60', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.46/0.69      inference('clc', [status(thm)], ['57', '58'])).
% 0.46/0.69  thf('61', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.46/0.69      inference('clc', [status(thm)], ['57', '58'])).
% 0.46/0.69  thf('62', plain,
% 0.46/0.69      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.69          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.69           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.69          sk_C)),
% 0.46/0.69      inference('demod', [status(thm)], ['8', '59', '60', '61'])).
% 0.46/0.69  thf('63', plain,
% 0.46/0.69      (![X31 : $i]:
% 0.46/0.69         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.46/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.69  thf('64', plain,
% 0.46/0.69      ((m1_subset_1 @ sk_C @ 
% 0.46/0.69        (k1_zfmisc_1 @ 
% 0.46/0.69         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.69      inference('demod', [status(thm)], ['28', '29'])).
% 0.46/0.69  thf('65', plain,
% 0.46/0.69      (((m1_subset_1 @ sk_C @ 
% 0.46/0.69         (k1_zfmisc_1 @ 
% 0.46/0.69          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.46/0.69        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.69      inference('sup+', [status(thm)], ['63', '64'])).
% 0.46/0.69  thf('66', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('67', plain,
% 0.46/0.69      ((m1_subset_1 @ sk_C @ 
% 0.46/0.69        (k1_zfmisc_1 @ 
% 0.46/0.69         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.46/0.69      inference('demod', [status(thm)], ['65', '66'])).
% 0.46/0.69  thf(d4_tops_2, axiom,
% 0.46/0.69    (![A:$i,B:$i,C:$i]:
% 0.46/0.69     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.69         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.69       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.46/0.69         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.46/0.69  thf('68', plain,
% 0.46/0.69      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.46/0.69         (((k2_relset_1 @ X34 @ X33 @ X35) != (X33))
% 0.46/0.69          | ~ (v2_funct_1 @ X35)
% 0.46/0.69          | ((k2_tops_2 @ X34 @ X33 @ X35) = (k2_funct_1 @ X35))
% 0.46/0.69          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.46/0.69          | ~ (v1_funct_2 @ X35 @ X34 @ X33)
% 0.46/0.69          | ~ (v1_funct_1 @ X35))),
% 0.46/0.69      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.46/0.69  thf('69', plain,
% 0.46/0.69      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.69        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.46/0.69        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.69            = (k2_funct_1 @ sk_C))
% 0.46/0.69        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.69        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.69            != (k2_struct_0 @ sk_B)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['67', '68'])).
% 0.46/0.69  thf('70', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('71', plain,
% 0.46/0.69      (![X31 : $i]:
% 0.46/0.69         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.46/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.69  thf('72', plain,
% 0.46/0.69      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.69      inference('demod', [status(thm)], ['36', '37'])).
% 0.46/0.69  thf('73', plain,
% 0.46/0.69      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.46/0.69        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.69      inference('sup+', [status(thm)], ['71', '72'])).
% 0.46/0.69  thf('74', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('75', plain,
% 0.46/0.69      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.46/0.69      inference('demod', [status(thm)], ['73', '74'])).
% 0.46/0.69  thf('76', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf(d9_funct_1, axiom,
% 0.46/0.69    (![A:$i]:
% 0.46/0.69     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.69       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.46/0.69  thf('77', plain,
% 0.46/0.69      (![X5 : $i]:
% 0.46/0.69         (~ (v2_funct_1 @ X5)
% 0.46/0.69          | ((k2_funct_1 @ X5) = (k4_relat_1 @ X5))
% 0.46/0.69          | ~ (v1_funct_1 @ X5)
% 0.46/0.69          | ~ (v1_relat_1 @ X5))),
% 0.46/0.69      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.46/0.69  thf('78', plain,
% 0.46/0.69      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.69        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 0.46/0.69        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.69      inference('sup-', [status(thm)], ['76', '77'])).
% 0.46/0.69  thf('79', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.69      inference('demod', [status(thm)], ['19', '20'])).
% 0.46/0.69  thf('80', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('81', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.46/0.69      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.46/0.69  thf('82', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('83', plain,
% 0.46/0.69      (![X31 : $i]:
% 0.46/0.69         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.46/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.69  thf('84', plain,
% 0.46/0.69      (![X31 : $i]:
% 0.46/0.69         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.46/0.69      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.69  thf('85', plain,
% 0.46/0.69      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.69         = (k2_struct_0 @ sk_B))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('86', plain,
% 0.46/0.69      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.69          = (k2_struct_0 @ sk_B))
% 0.46/0.69        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.69      inference('sup+', [status(thm)], ['84', '85'])).
% 0.46/0.69  thf('87', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('88', plain,
% 0.46/0.69      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.69         = (k2_struct_0 @ sk_B))),
% 0.46/0.69      inference('demod', [status(thm)], ['86', '87'])).
% 0.46/0.69  thf('89', plain,
% 0.46/0.69      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.69          = (k2_struct_0 @ sk_B))
% 0.46/0.69        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.69      inference('sup+', [status(thm)], ['83', '88'])).
% 0.46/0.69  thf('90', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('91', plain,
% 0.46/0.69      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.69         = (k2_struct_0 @ sk_B))),
% 0.46/0.69      inference('demod', [status(thm)], ['89', '90'])).
% 0.46/0.69  thf('92', plain,
% 0.46/0.69      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.69          = (k4_relat_1 @ sk_C))
% 0.46/0.69        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.46/0.69      inference('demod', [status(thm)], ['69', '70', '75', '81', '82', '91'])).
% 0.46/0.69  thf('93', plain,
% 0.46/0.69      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.69         = (k4_relat_1 @ sk_C))),
% 0.46/0.69      inference('simplify', [status(thm)], ['92'])).
% 0.46/0.69  thf('94', plain,
% 0.46/0.69      ((m1_subset_1 @ sk_C @ 
% 0.46/0.69        (k1_zfmisc_1 @ 
% 0.46/0.69         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.46/0.69      inference('demod', [status(thm)], ['65', '66'])).
% 0.46/0.69  thf(t31_funct_2, axiom,
% 0.46/0.69    (![A:$i,B:$i,C:$i]:
% 0.46/0.69     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.69         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.69       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.46/0.69         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.46/0.69           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.46/0.69           ( m1_subset_1 @
% 0.46/0.69             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.46/0.69  thf('95', plain,
% 0.46/0.69      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.46/0.69         (~ (v2_funct_1 @ X28)
% 0.46/0.69          | ((k2_relset_1 @ X30 @ X29 @ X28) != (X29))
% 0.46/0.69          | (m1_subset_1 @ (k2_funct_1 @ X28) @ 
% 0.46/0.69             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.46/0.69          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 0.46/0.69          | ~ (v1_funct_2 @ X28 @ X30 @ X29)
% 0.46/0.69          | ~ (v1_funct_1 @ X28))),
% 0.46/0.69      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.46/0.69  thf('96', plain,
% 0.46/0.69      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.69        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.46/0.69        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.69           (k1_zfmisc_1 @ 
% 0.46/0.69            (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.46/0.69        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.69            != (k2_struct_0 @ sk_B))
% 0.46/0.69        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.69      inference('sup-', [status(thm)], ['94', '95'])).
% 0.46/0.69  thf('97', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('98', plain,
% 0.46/0.69      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.46/0.69      inference('demod', [status(thm)], ['73', '74'])).
% 0.46/0.69  thf('99', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.46/0.69      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.46/0.69  thf('100', plain,
% 0.46/0.69      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.69         = (k2_struct_0 @ sk_B))),
% 0.46/0.69      inference('demod', [status(thm)], ['89', '90'])).
% 0.46/0.69  thf('101', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('102', plain,
% 0.46/0.69      (((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.46/0.69         (k1_zfmisc_1 @ 
% 0.46/0.69          (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.46/0.69        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.46/0.69      inference('demod', [status(thm)], ['96', '97', '98', '99', '100', '101'])).
% 0.46/0.69  thf('103', plain,
% 0.46/0.69      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.46/0.69        (k1_zfmisc_1 @ 
% 0.46/0.69         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.46/0.69      inference('simplify', [status(thm)], ['102'])).
% 0.46/0.69  thf('104', plain,
% 0.46/0.69      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.46/0.69         (((k2_relset_1 @ X34 @ X33 @ X35) != (X33))
% 0.46/0.69          | ~ (v2_funct_1 @ X35)
% 0.46/0.69          | ((k2_tops_2 @ X34 @ X33 @ X35) = (k2_funct_1 @ X35))
% 0.46/0.69          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.46/0.69          | ~ (v1_funct_2 @ X35 @ X34 @ X33)
% 0.46/0.69          | ~ (v1_funct_1 @ X35))),
% 0.46/0.69      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.46/0.69  thf('105', plain,
% 0.46/0.69      ((~ (v1_funct_1 @ (k4_relat_1 @ sk_C))
% 0.46/0.69        | ~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.46/0.69             (k2_struct_0 @ sk_A))
% 0.46/0.69        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.69            (k4_relat_1 @ sk_C)) = (k2_funct_1 @ (k4_relat_1 @ sk_C)))
% 0.46/0.69        | ~ (v2_funct_1 @ (k4_relat_1 @ sk_C))
% 0.46/0.69        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.69            (k4_relat_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['103', '104'])).
% 0.46/0.69  thf('106', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.46/0.69      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.46/0.69  thf(dt_k2_funct_1, axiom,
% 0.46/0.69    (![A:$i]:
% 0.46/0.69     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.69       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.46/0.69         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.46/0.69  thf('107', plain,
% 0.46/0.69      (![X6 : $i]:
% 0.46/0.69         ((v1_funct_1 @ (k2_funct_1 @ X6))
% 0.46/0.69          | ~ (v1_funct_1 @ X6)
% 0.46/0.69          | ~ (v1_relat_1 @ X6))),
% 0.46/0.69      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.69  thf('108', plain,
% 0.46/0.69      (((v1_funct_1 @ (k4_relat_1 @ sk_C))
% 0.46/0.69        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.69        | ~ (v1_funct_1 @ sk_C))),
% 0.46/0.69      inference('sup+', [status(thm)], ['106', '107'])).
% 0.46/0.69  thf('109', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.69      inference('demod', [status(thm)], ['19', '20'])).
% 0.46/0.69  thf('110', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('111', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.46/0.69      inference('demod', [status(thm)], ['108', '109', '110'])).
% 0.46/0.69  thf('112', plain,
% 0.46/0.69      ((m1_subset_1 @ sk_C @ 
% 0.46/0.69        (k1_zfmisc_1 @ 
% 0.46/0.69         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.46/0.69      inference('demod', [status(thm)], ['65', '66'])).
% 0.46/0.69  thf('113', plain,
% 0.46/0.69      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.46/0.69         (~ (v2_funct_1 @ X28)
% 0.46/0.69          | ((k2_relset_1 @ X30 @ X29 @ X28) != (X29))
% 0.46/0.69          | (v1_funct_2 @ (k2_funct_1 @ X28) @ X29 @ X30)
% 0.46/0.69          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 0.46/0.69          | ~ (v1_funct_2 @ X28 @ X30 @ X29)
% 0.46/0.69          | ~ (v1_funct_1 @ X28))),
% 0.46/0.69      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.46/0.69  thf('114', plain,
% 0.46/0.69      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.69        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.46/0.69        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.46/0.69           (k2_struct_0 @ sk_A))
% 0.46/0.69        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.69            != (k2_struct_0 @ sk_B))
% 0.46/0.69        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.69      inference('sup-', [status(thm)], ['112', '113'])).
% 0.46/0.69  thf('115', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('116', plain,
% 0.46/0.69      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.46/0.69      inference('demod', [status(thm)], ['73', '74'])).
% 0.46/0.69  thf('117', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.46/0.69      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.46/0.69  thf('118', plain,
% 0.46/0.69      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.69         = (k2_struct_0 @ sk_B))),
% 0.46/0.69      inference('demod', [status(thm)], ['89', '90'])).
% 0.46/0.69  thf('119', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('120', plain,
% 0.46/0.69      (((v1_funct_2 @ (k4_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.46/0.69         (k2_struct_0 @ sk_A))
% 0.46/0.69        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.46/0.69      inference('demod', [status(thm)],
% 0.46/0.69                ['114', '115', '116', '117', '118', '119'])).
% 0.46/0.69  thf('121', plain,
% 0.46/0.69      ((v1_funct_2 @ (k4_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.46/0.69        (k2_struct_0 @ sk_A))),
% 0.46/0.69      inference('simplify', [status(thm)], ['120'])).
% 0.46/0.69  thf('122', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.46/0.69      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.46/0.69  thf(t65_funct_1, axiom,
% 0.46/0.69    (![A:$i]:
% 0.46/0.69     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.69       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.46/0.69  thf('123', plain,
% 0.46/0.69      (![X12 : $i]:
% 0.46/0.69         (~ (v2_funct_1 @ X12)
% 0.46/0.69          | ((k2_funct_1 @ (k2_funct_1 @ X12)) = (X12))
% 0.46/0.69          | ~ (v1_funct_1 @ X12)
% 0.46/0.69          | ~ (v1_relat_1 @ X12))),
% 0.46/0.69      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.46/0.69  thf('124', plain,
% 0.46/0.69      ((((k2_funct_1 @ (k4_relat_1 @ sk_C)) = (sk_C))
% 0.46/0.69        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.69        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.69        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.69      inference('sup+', [status(thm)], ['122', '123'])).
% 0.46/0.69  thf('125', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.69      inference('demod', [status(thm)], ['19', '20'])).
% 0.46/0.69  thf('126', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('127', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('128', plain, (((k2_funct_1 @ (k4_relat_1 @ sk_C)) = (sk_C))),
% 0.46/0.69      inference('demod', [status(thm)], ['124', '125', '126', '127'])).
% 0.46/0.69  thf(t37_relat_1, axiom,
% 0.46/0.69    (![A:$i]:
% 0.46/0.69     ( ( v1_relat_1 @ A ) =>
% 0.46/0.69       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.46/0.69         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.46/0.69  thf('129', plain,
% 0.46/0.69      (![X4 : $i]:
% 0.46/0.69         (((k1_relat_1 @ X4) = (k2_relat_1 @ (k4_relat_1 @ X4)))
% 0.46/0.69          | ~ (v1_relat_1 @ X4))),
% 0.46/0.69      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.46/0.69  thf('130', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.46/0.69      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.46/0.69  thf(t61_funct_1, axiom,
% 0.46/0.69    (![A:$i]:
% 0.46/0.69     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.69       ( ( v2_funct_1 @ A ) =>
% 0.46/0.69         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.46/0.70             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.46/0.70           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.46/0.70             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.46/0.70  thf('131', plain,
% 0.46/0.70      (![X11 : $i]:
% 0.46/0.70         (~ (v2_funct_1 @ X11)
% 0.46/0.70          | ((k5_relat_1 @ (k2_funct_1 @ X11) @ X11)
% 0.46/0.70              = (k6_relat_1 @ (k2_relat_1 @ X11)))
% 0.46/0.70          | ~ (v1_funct_1 @ X11)
% 0.46/0.70          | ~ (v1_relat_1 @ X11))),
% 0.46/0.70      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.46/0.70  thf('132', plain,
% 0.46/0.70      ((((k5_relat_1 @ (k4_relat_1 @ sk_C) @ sk_C)
% 0.46/0.70          = (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 0.46/0.70        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.70        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.70        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.70      inference('sup+', [status(thm)], ['130', '131'])).
% 0.46/0.70  thf('133', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.70      inference('demod', [status(thm)], ['19', '20'])).
% 0.46/0.70  thf('134', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('135', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('136', plain,
% 0.46/0.70      (((k5_relat_1 @ (k4_relat_1 @ sk_C) @ sk_C)
% 0.46/0.70         = (k6_relat_1 @ (k2_relat_1 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)], ['132', '133', '134', '135'])).
% 0.46/0.70  thf(t48_funct_1, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.70       ( ![B:$i]:
% 0.46/0.70         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.46/0.70           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.46/0.70               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.46/0.70             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 0.46/0.70  thf('137', plain,
% 0.46/0.70      (![X9 : $i, X10 : $i]:
% 0.46/0.70         (~ (v1_relat_1 @ X9)
% 0.46/0.70          | ~ (v1_funct_1 @ X9)
% 0.46/0.70          | (v2_funct_1 @ X9)
% 0.46/0.70          | ((k2_relat_1 @ X9) != (k1_relat_1 @ X10))
% 0.46/0.70          | ~ (v2_funct_1 @ (k5_relat_1 @ X9 @ X10))
% 0.46/0.70          | ~ (v1_funct_1 @ X10)
% 0.46/0.70          | ~ (v1_relat_1 @ X10))),
% 0.46/0.70      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.46/0.70  thf('138', plain,
% 0.46/0.70      ((~ (v2_funct_1 @ (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 0.46/0.70        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.70        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.70        | ((k2_relat_1 @ (k4_relat_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 0.46/0.70        | (v2_funct_1 @ (k4_relat_1 @ sk_C))
% 0.46/0.70        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C))
% 0.46/0.70        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['136', '137'])).
% 0.46/0.70  thf(fc4_funct_1, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.46/0.70       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.46/0.70  thf('139', plain, (![X8 : $i]: (v2_funct_1 @ (k6_relat_1 @ X8))),
% 0.46/0.70      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.46/0.70  thf('140', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.70      inference('demod', [status(thm)], ['19', '20'])).
% 0.46/0.70  thf('141', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('142', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['108', '109', '110'])).
% 0.46/0.70  thf('143', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.46/0.70  thf('144', plain,
% 0.46/0.70      (![X6 : $i]:
% 0.46/0.70         ((v1_relat_1 @ (k2_funct_1 @ X6))
% 0.46/0.70          | ~ (v1_funct_1 @ X6)
% 0.46/0.70          | ~ (v1_relat_1 @ X6))),
% 0.46/0.70      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.70  thf('145', plain,
% 0.46/0.70      (((v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.46/0.70        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.70        | ~ (v1_funct_1 @ sk_C))),
% 0.46/0.70      inference('sup+', [status(thm)], ['143', '144'])).
% 0.46/0.70  thf('146', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.70      inference('demod', [status(thm)], ['19', '20'])).
% 0.46/0.70  thf('147', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('148', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['145', '146', '147'])).
% 0.46/0.70  thf('149', plain,
% 0.46/0.70      ((((k2_relat_1 @ (k4_relat_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 0.46/0.70        | (v2_funct_1 @ (k4_relat_1 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)],
% 0.46/0.70                ['138', '139', '140', '141', '142', '148'])).
% 0.46/0.70  thf('150', plain,
% 0.46/0.70      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 0.46/0.70        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.70        | (v2_funct_1 @ (k4_relat_1 @ sk_C)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['129', '149'])).
% 0.46/0.70  thf('151', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.70      inference('demod', [status(thm)], ['19', '20'])).
% 0.46/0.70  thf('152', plain,
% 0.46/0.70      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 0.46/0.70        | (v2_funct_1 @ (k4_relat_1 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)], ['150', '151'])).
% 0.46/0.70  thf('153', plain, ((v2_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.46/0.70      inference('simplify', [status(thm)], ['152'])).
% 0.46/0.70  thf('154', plain,
% 0.46/0.70      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.46/0.70      inference('simplify', [status(thm)], ['102'])).
% 0.46/0.70  thf(redefinition_k2_relset_1, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.70       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.46/0.70  thf('155', plain,
% 0.46/0.70      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.46/0.70         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 0.46/0.70          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.46/0.70      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.46/0.70  thf('156', plain,
% 0.46/0.70      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.70         (k4_relat_1 @ sk_C)) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['154', '155'])).
% 0.46/0.70  thf('157', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['108', '109', '110'])).
% 0.46/0.70  thf('158', plain,
% 0.46/0.70      (![X5 : $i]:
% 0.46/0.70         (~ (v2_funct_1 @ X5)
% 0.46/0.70          | ((k2_funct_1 @ X5) = (k4_relat_1 @ X5))
% 0.46/0.70          | ~ (v1_funct_1 @ X5)
% 0.46/0.70          | ~ (v1_relat_1 @ X5))),
% 0.46/0.70      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.46/0.70  thf('159', plain,
% 0.46/0.70      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.46/0.70        | ((k2_funct_1 @ (k4_relat_1 @ sk_C))
% 0.46/0.70            = (k4_relat_1 @ (k4_relat_1 @ sk_C)))
% 0.46/0.70        | ~ (v2_funct_1 @ (k4_relat_1 @ sk_C)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['157', '158'])).
% 0.46/0.70  thf('160', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['145', '146', '147'])).
% 0.46/0.70  thf('161', plain,
% 0.46/0.70      ((((k2_funct_1 @ (k4_relat_1 @ sk_C))
% 0.46/0.70          = (k4_relat_1 @ (k4_relat_1 @ sk_C)))
% 0.46/0.70        | ~ (v2_funct_1 @ (k4_relat_1 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)], ['159', '160'])).
% 0.46/0.70  thf('162', plain, (((k2_funct_1 @ (k4_relat_1 @ sk_C)) = (sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['124', '125', '126', '127'])).
% 0.46/0.70  thf('163', plain,
% 0.46/0.70      ((((sk_C) = (k4_relat_1 @ (k4_relat_1 @ sk_C)))
% 0.46/0.70        | ~ (v2_funct_1 @ (k4_relat_1 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)], ['161', '162'])).
% 0.46/0.70  thf('164', plain, ((v2_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.46/0.70      inference('simplify', [status(thm)], ['152'])).
% 0.46/0.70  thf('165', plain, (((sk_C) = (k4_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)], ['163', '164'])).
% 0.46/0.70  thf('166', plain,
% 0.46/0.70      (![X4 : $i]:
% 0.46/0.70         (((k2_relat_1 @ X4) = (k1_relat_1 @ (k4_relat_1 @ X4)))
% 0.46/0.70          | ~ (v1_relat_1 @ X4))),
% 0.46/0.70      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.46/0.70  thf('167', plain,
% 0.46/0.70      ((((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))
% 0.46/0.70        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.46/0.70      inference('sup+', [status(thm)], ['165', '166'])).
% 0.46/0.70  thf('168', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['145', '146', '147'])).
% 0.46/0.70  thf('169', plain,
% 0.46/0.70      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['167', '168'])).
% 0.46/0.70  thf('170', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.70      inference('clc', [status(thm)], ['50', '51'])).
% 0.46/0.70  thf('171', plain,
% 0.46/0.70      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['169', '170'])).
% 0.46/0.70  thf('172', plain,
% 0.46/0.70      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.70         (k4_relat_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.46/0.70      inference('demod', [status(thm)], ['156', '171'])).
% 0.46/0.70  thf('173', plain,
% 0.46/0.70      ((((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.70          (k4_relat_1 @ sk_C)) = (sk_C))
% 0.46/0.70        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)))),
% 0.46/0.70      inference('demod', [status(thm)],
% 0.46/0.70                ['105', '111', '121', '128', '153', '172'])).
% 0.46/0.70  thf('174', plain,
% 0.46/0.70      (((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.70         (k4_relat_1 @ sk_C)) = (sk_C))),
% 0.46/0.70      inference('simplify', [status(thm)], ['173'])).
% 0.46/0.70  thf('175', plain,
% 0.46/0.70      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.70          sk_C)),
% 0.46/0.70      inference('demod', [status(thm)], ['62', '93', '174'])).
% 0.46/0.70  thf('176', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.70      inference('demod', [status(thm)], ['28', '29'])).
% 0.46/0.70  thf('177', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ 
% 0.46/0.70         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.70      inference('demod', [status(thm)], ['28', '29'])).
% 0.46/0.70  thf(reflexivity_r2_funct_2, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.70     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.70         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.46/0.70         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.46/0.70         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.70       ( r2_funct_2 @ A @ B @ C @ C ) ))).
% 0.53/0.70  thf('178', plain,
% 0.53/0.70      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.53/0.70         ((r2_funct_2 @ X24 @ X25 @ X26 @ X26)
% 0.53/0.70          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.53/0.70          | ~ (v1_funct_2 @ X26 @ X24 @ X25)
% 0.53/0.70          | ~ (v1_funct_1 @ X26)
% 0.53/0.70          | ~ (v1_funct_1 @ X27)
% 0.53/0.70          | ~ (v1_funct_2 @ X27 @ X24 @ X25)
% 0.53/0.70          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.53/0.70      inference('cnf', [status(esa)], [reflexivity_r2_funct_2])).
% 0.53/0.70  thf('179', plain,
% 0.53/0.70      (![X0 : $i]:
% 0.53/0.70         (~ (m1_subset_1 @ X0 @ 
% 0.53/0.70             (k1_zfmisc_1 @ 
% 0.53/0.70              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.53/0.70          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.53/0.70          | ~ (v1_funct_1 @ X0)
% 0.53/0.70          | ~ (v1_funct_1 @ sk_C)
% 0.53/0.70          | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.53/0.70          | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.53/0.70             sk_C))),
% 0.53/0.70      inference('sup-', [status(thm)], ['177', '178'])).
% 0.53/0.70  thf('180', plain, ((v1_funct_1 @ sk_C)),
% 0.53/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.70  thf('181', plain,
% 0.53/0.70      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.53/0.70      inference('demod', [status(thm)], ['36', '37'])).
% 0.53/0.70  thf('182', plain,
% 0.53/0.70      (![X0 : $i]:
% 0.53/0.70         (~ (m1_subset_1 @ X0 @ 
% 0.53/0.70             (k1_zfmisc_1 @ 
% 0.53/0.70              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.53/0.70          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.53/0.70          | ~ (v1_funct_1 @ X0)
% 0.53/0.70          | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.53/0.70             sk_C))),
% 0.53/0.70      inference('demod', [status(thm)], ['179', '180', '181'])).
% 0.53/0.70  thf('183', plain,
% 0.53/0.70      (((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)
% 0.53/0.70        | ~ (v1_funct_1 @ sk_C)
% 0.53/0.70        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.53/0.70      inference('sup-', [status(thm)], ['176', '182'])).
% 0.53/0.70  thf('184', plain, ((v1_funct_1 @ sk_C)),
% 0.53/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.70  thf('185', plain,
% 0.53/0.70      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.53/0.70      inference('demod', [status(thm)], ['36', '37'])).
% 0.53/0.70  thf('186', plain,
% 0.53/0.70      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.53/0.70      inference('demod', [status(thm)], ['183', '184', '185'])).
% 0.53/0.70  thf('187', plain, ($false), inference('demod', [status(thm)], ['175', '186'])).
% 0.53/0.70  
% 0.53/0.70  % SZS output end Refutation
% 0.53/0.70  
% 0.53/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
