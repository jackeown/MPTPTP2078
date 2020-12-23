%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0ysBKPscsI

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:17 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  269 (1276 expanded)
%              Number of leaves         :   44 ( 393 expanded)
%              Depth                    :   36
%              Number of atoms          : 2578 (26939 expanded)
%              Number of equality atoms :  122 ( 750 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

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
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X11 ) )
        = X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
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
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
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

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('11',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( v1_partfun1 @ X18 @ X19 )
      | ~ ( v1_funct_2 @ X18 @ X19 @ X20 )
      | ~ ( v1_funct_1 @ X18 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('12',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('16',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_partfun1 @ X22 @ X21 )
      | ( ( k1_relat_1 @ X22 )
        = X21 )
      | ~ ( v4_relat_1 @ X22 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('17',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('22',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('24',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v4_relat_1 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('25',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','22','25'])).

thf('27',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
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

thf('32',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( v1_partfun1 @ X18 @ X19 )
      | ~ ( v1_funct_2 @ X18 @ X19 @ X20 )
      | ~ ( v1_funct_1 @ X18 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('36',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34','39'])).

thf('41',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_partfun1 @ X22 @ X21 )
      | ( ( k1_relat_1 @ X22 )
        = X21 )
      | ~ ( v4_relat_1 @ X22 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('45',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v4_relat_1 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('46',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43','46'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('48',plain,(
    ! [X31: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('49',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','53'])).

thf('55',plain,(
    ! [X31: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('56',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('62',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('63',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['9','60','61','62'])).

thf('64',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('66',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

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

thf('69',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k2_relset_1 @ X33 @ X32 @ X34 )
       != X32 )
      | ~ ( v2_funct_1 @ X34 )
      | ( ( k2_tops_2 @ X33 @ X32 @ X34 )
        = ( k2_funct_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X33 @ X32 )
      | ~ ( v1_funct_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('70',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('73',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('74',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('79',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('80',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['78','83'])).

thf('85',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['70','71','76','77','86'])).

thf('88',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['63','88'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('90',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k1_relat_1 @ X9 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('91',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

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

thf('92',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v2_funct_1 @ X27 )
      | ( ( k2_relset_1 @ X29 @ X28 @ X27 )
       != X28 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X29 @ X28 )
      | ~ ( v1_funct_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('93',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('96',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('97',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['93','94','95','96','97'])).

thf('99',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k2_relset_1 @ X33 @ X32 @ X34 )
       != X32 )
      | ~ ( v2_funct_1 @ X34 )
      | ( ( k2_tops_2 @ X33 @ X32 @ X34 )
        = ( k2_funct_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X33 @ X32 )
      | ~ ( v1_funct_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('101',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('103',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v2_funct_1 @ X27 )
      | ( ( k2_relset_1 @ X29 @ X28 @ X27 )
       != X28 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X29 @ X28 )
      | ~ ( v1_funct_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('104',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('107',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('108',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['104','105','106','107','108'])).

thf('110',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('112',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v2_funct_1 @ X27 )
      | ( ( k2_relset_1 @ X29 @ X28 @ X27 )
       != X28 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X27 ) @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X29 @ X28 )
      | ~ ( v1_funct_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('113',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('116',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('117',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['113','114','115','116','117'])).

thf('119',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k1_relat_1 @ X9 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('121',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('122',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X11 ) )
        = X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('123',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k1_relat_1 @ X9 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('124',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('125',plain,(
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

thf('126',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X10 ) @ X10 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( v2_funct_1 @ X7 )
      | ( ( k2_relat_1 @ X7 )
       != ( k1_relat_1 @ X8 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
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
    ! [X6: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X6 ) ) ),
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
    inference(simplify,[status(thm)],['109'])).

thf('139',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('140',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X11 ) )
        = X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('142',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('143',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('144',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X11 ) )
        = X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('145',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X10 ) @ X10 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['143','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['142','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['141','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['140','152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['139','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['154'])).

thf('156',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ),
    inference('sup-',[status(thm)],['138','155'])).

thf('157',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('158',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ),
    inference(demod,[status(thm)],['156','157','158','159'])).

thf('161',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ),
    inference('sup-',[status(thm)],['137','160'])).

thf('162',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('163',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['161','162','163','164'])).

thf('166',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['122','165'])).

thf('167',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('168',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('169',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['169','170'])).

thf('172',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('173',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_relat_1 @ ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['166','171','172','173','174'])).

thf('176',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( v2_funct_1 @ X7 )
      | ( ( k2_relat_1 @ X7 )
       != ( k1_relat_1 @ X8 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('177',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ ( k2_struct_0 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    ! [X6: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('179',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('180',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('182',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['109'])).

thf('183',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['177','178','179','180','181','182'])).

thf('184',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['121','183'])).

thf('185',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('186',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['184','185','186'])).

thf('188',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['120','187'])).

thf('189',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('190',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('191',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['188','189','190','191','192'])).

thf('194',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['193'])).

thf('195',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('196',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('197',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['101','110','119','194','197'])).

thf('199',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['90','198'])).

thf('200',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('201',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('202',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['199','200','201','202','203'])).

thf('205',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['204'])).

thf('206',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['89','205'])).

thf('207',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','206'])).

thf('208',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('209',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['207','208','209','210'])).

thf('212',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('213',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(reflexivity_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_funct_2 @ A @ B @ C @ C ) ) )).

thf('214',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( r2_funct_2 @ X23 @ X24 @ X25 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_2 @ X26 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_funct_2])).

thf('215',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['213','214'])).

thf('216',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('218',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['215','216','217'])).

thf('219',plain,
    ( ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['212','218'])).

thf('220',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('222',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['219','220','221'])).

thf('223',plain,(
    $false ),
    inference(demod,[status(thm)],['211','222'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0ysBKPscsI
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 21:23:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.46/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.63  % Solved by: fo/fo7.sh
% 0.46/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.63  % done 430 iterations in 0.171s
% 0.46/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.63  % SZS output start Refutation
% 0.46/0.63  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.46/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.63  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.46/0.63  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.63  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.63  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.46/0.63  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.63  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.46/0.63  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.46/0.63  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.46/0.63  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.63  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.63  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.63  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.63  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.46/0.63  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.46/0.63  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.46/0.63  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.46/0.63  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.46/0.63  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.46/0.63  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.46/0.63  thf(t65_funct_1, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.63       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.46/0.63  thf('0', plain,
% 0.46/0.63      (![X11 : $i]:
% 0.46/0.63         (~ (v2_funct_1 @ X11)
% 0.46/0.63          | ((k2_funct_1 @ (k2_funct_1 @ X11)) = (X11))
% 0.46/0.63          | ~ (v1_funct_1 @ X11)
% 0.46/0.63          | ~ (v1_relat_1 @ X11))),
% 0.46/0.63      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.46/0.63  thf(d3_struct_0, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.46/0.63  thf('1', plain,
% 0.46/0.63      (![X30 : $i]:
% 0.46/0.63         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 0.46/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.63  thf('2', plain,
% 0.46/0.63      (![X30 : $i]:
% 0.46/0.63         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 0.46/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.63  thf(t64_tops_2, conjecture,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( l1_struct_0 @ A ) =>
% 0.46/0.63       ( ![B:$i]:
% 0.46/0.63         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.46/0.63           ( ![C:$i]:
% 0.46/0.63             ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.63                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.46/0.63                 ( m1_subset_1 @
% 0.46/0.63                   C @ 
% 0.46/0.63                   ( k1_zfmisc_1 @
% 0.46/0.63                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.46/0.63               ( ( ( ( k2_relset_1 @
% 0.46/0.63                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.46/0.63                     ( k2_struct_0 @ B ) ) & 
% 0.46/0.63                   ( v2_funct_1 @ C ) ) =>
% 0.46/0.63                 ( r2_funct_2 @
% 0.46/0.63                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.46/0.63                   ( k2_tops_2 @
% 0.46/0.63                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.46/0.63                     ( k2_tops_2 @
% 0.46/0.63                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.46/0.63                   C ) ) ) ) ) ) ))).
% 0.46/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.63    (~( ![A:$i]:
% 0.46/0.63        ( ( l1_struct_0 @ A ) =>
% 0.46/0.63          ( ![B:$i]:
% 0.46/0.63            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.46/0.63              ( ![C:$i]:
% 0.46/0.63                ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.63                    ( v1_funct_2 @
% 0.46/0.63                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.46/0.63                    ( m1_subset_1 @
% 0.46/0.63                      C @ 
% 0.46/0.63                      ( k1_zfmisc_1 @
% 0.46/0.63                        ( k2_zfmisc_1 @
% 0.46/0.63                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.46/0.63                  ( ( ( ( k2_relset_1 @
% 0.46/0.63                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.46/0.63                        ( k2_struct_0 @ B ) ) & 
% 0.46/0.63                      ( v2_funct_1 @ C ) ) =>
% 0.46/0.63                    ( r2_funct_2 @
% 0.46/0.63                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.46/0.63                      ( k2_tops_2 @
% 0.46/0.63                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.46/0.63                        ( k2_tops_2 @
% 0.46/0.63                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.46/0.63                      C ) ) ) ) ) ) ) )),
% 0.46/0.63    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.46/0.63  thf('3', plain,
% 0.46/0.63      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.63          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.63           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.63          sk_C)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('4', plain,
% 0.46/0.63      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.63           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.63            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.63           sk_C)
% 0.46/0.63        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.63      inference('sup-', [status(thm)], ['2', '3'])).
% 0.46/0.63  thf('5', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('6', plain,
% 0.46/0.63      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.63          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.63           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.63          sk_C)),
% 0.46/0.63      inference('demod', [status(thm)], ['4', '5'])).
% 0.46/0.63  thf('7', plain,
% 0.46/0.63      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.63           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.63            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.63           sk_C)
% 0.46/0.63        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.63      inference('sup-', [status(thm)], ['1', '6'])).
% 0.46/0.63  thf('8', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('9', plain,
% 0.46/0.63      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.63          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.63           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.63          sk_C)),
% 0.46/0.63      inference('demod', [status(thm)], ['7', '8'])).
% 0.46/0.63  thf('10', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C @ 
% 0.46/0.63        (k1_zfmisc_1 @ 
% 0.46/0.63         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(cc5_funct_2, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.46/0.63       ( ![C:$i]:
% 0.46/0.63         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.63           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.46/0.63             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.46/0.63  thf('11', plain,
% 0.46/0.63      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.46/0.63          | (v1_partfun1 @ X18 @ X19)
% 0.46/0.63          | ~ (v1_funct_2 @ X18 @ X19 @ X20)
% 0.46/0.63          | ~ (v1_funct_1 @ X18)
% 0.46/0.63          | (v1_xboole_0 @ X20))),
% 0.46/0.63      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.46/0.63  thf('12', plain,
% 0.46/0.63      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.63        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.63        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.63        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['10', '11'])).
% 0.46/0.63  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('14', plain,
% 0.46/0.63      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('15', plain,
% 0.46/0.63      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.63        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.46/0.63  thf(d4_partfun1, axiom,
% 0.46/0.63    (![A:$i,B:$i]:
% 0.46/0.63     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.46/0.63       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.46/0.63  thf('16', plain,
% 0.46/0.63      (![X21 : $i, X22 : $i]:
% 0.46/0.63         (~ (v1_partfun1 @ X22 @ X21)
% 0.46/0.63          | ((k1_relat_1 @ X22) = (X21))
% 0.46/0.63          | ~ (v4_relat_1 @ X22 @ X21)
% 0.46/0.63          | ~ (v1_relat_1 @ X22))),
% 0.46/0.63      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.46/0.63  thf('17', plain,
% 0.46/0.63      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.63        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.63        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.46/0.63        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['15', '16'])).
% 0.46/0.63  thf('18', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C @ 
% 0.46/0.63        (k1_zfmisc_1 @ 
% 0.46/0.63         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(cc2_relat_1, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( v1_relat_1 @ A ) =>
% 0.46/0.63       ( ![B:$i]:
% 0.46/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.46/0.63  thf('19', plain,
% 0.46/0.63      (![X0 : $i, X1 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.46/0.63          | (v1_relat_1 @ X0)
% 0.46/0.63          | ~ (v1_relat_1 @ X1))),
% 0.46/0.63      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.46/0.63  thf('20', plain,
% 0.46/0.63      ((~ (v1_relat_1 @ 
% 0.46/0.63           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.46/0.63        | (v1_relat_1 @ sk_C))),
% 0.46/0.63      inference('sup-', [status(thm)], ['18', '19'])).
% 0.46/0.63  thf(fc6_relat_1, axiom,
% 0.46/0.63    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.46/0.63  thf('21', plain,
% 0.46/0.63      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.46/0.63      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.46/0.63  thf('22', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.63      inference('demod', [status(thm)], ['20', '21'])).
% 0.46/0.63  thf('23', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C @ 
% 0.46/0.63        (k1_zfmisc_1 @ 
% 0.46/0.63         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(cc2_relset_1, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.63       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.46/0.63  thf('24', plain,
% 0.46/0.63      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.46/0.63         ((v4_relat_1 @ X12 @ X13)
% 0.46/0.63          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.46/0.63      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.63  thf('25', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['23', '24'])).
% 0.46/0.63  thf('26', plain,
% 0.46/0.63      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.63        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('demod', [status(thm)], ['17', '22', '25'])).
% 0.46/0.63  thf('27', plain,
% 0.46/0.63      (![X30 : $i]:
% 0.46/0.63         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 0.46/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.63  thf('28', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C @ 
% 0.46/0.63        (k1_zfmisc_1 @ 
% 0.46/0.63         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('29', plain,
% 0.46/0.63      (((m1_subset_1 @ sk_C @ 
% 0.46/0.63         (k1_zfmisc_1 @ 
% 0.46/0.63          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.46/0.63        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.63      inference('sup+', [status(thm)], ['27', '28'])).
% 0.46/0.63  thf('30', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('31', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C @ 
% 0.46/0.63        (k1_zfmisc_1 @ 
% 0.46/0.63         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.63      inference('demod', [status(thm)], ['29', '30'])).
% 0.46/0.63  thf('32', plain,
% 0.46/0.63      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.46/0.63          | (v1_partfun1 @ X18 @ X19)
% 0.46/0.63          | ~ (v1_funct_2 @ X18 @ X19 @ X20)
% 0.46/0.63          | ~ (v1_funct_1 @ X18)
% 0.46/0.63          | (v1_xboole_0 @ X20))),
% 0.46/0.63      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.46/0.63  thf('33', plain,
% 0.46/0.63      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.63        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.63        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.63        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['31', '32'])).
% 0.46/0.63  thf('34', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('35', plain,
% 0.46/0.63      (![X30 : $i]:
% 0.46/0.63         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 0.46/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.63  thf('36', plain,
% 0.46/0.63      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('37', plain,
% 0.46/0.63      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.63        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.63      inference('sup+', [status(thm)], ['35', '36'])).
% 0.46/0.63  thf('38', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('39', plain,
% 0.46/0.63      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.63      inference('demod', [status(thm)], ['37', '38'])).
% 0.46/0.63  thf('40', plain,
% 0.46/0.63      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.63        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.46/0.63      inference('demod', [status(thm)], ['33', '34', '39'])).
% 0.46/0.63  thf('41', plain,
% 0.46/0.63      (![X21 : $i, X22 : $i]:
% 0.46/0.63         (~ (v1_partfun1 @ X22 @ X21)
% 0.46/0.63          | ((k1_relat_1 @ X22) = (X21))
% 0.46/0.63          | ~ (v4_relat_1 @ X22 @ X21)
% 0.46/0.63          | ~ (v1_relat_1 @ X22))),
% 0.46/0.63      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.46/0.63  thf('42', plain,
% 0.46/0.63      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.63        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.63        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.46/0.63        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['40', '41'])).
% 0.46/0.63  thf('43', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.63      inference('demod', [status(thm)], ['20', '21'])).
% 0.46/0.63  thf('44', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C @ 
% 0.46/0.63        (k1_zfmisc_1 @ 
% 0.46/0.63         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.63      inference('demod', [status(thm)], ['29', '30'])).
% 0.46/0.63  thf('45', plain,
% 0.46/0.63      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.46/0.63         ((v4_relat_1 @ X12 @ X13)
% 0.46/0.63          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.46/0.63      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.63  thf('46', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.46/0.63      inference('sup-', [status(thm)], ['44', '45'])).
% 0.46/0.63  thf('47', plain,
% 0.46/0.63      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.63        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.46/0.63      inference('demod', [status(thm)], ['42', '43', '46'])).
% 0.46/0.63  thf(fc2_struct_0, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.46/0.63       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.46/0.63  thf('48', plain,
% 0.46/0.63      (![X31 : $i]:
% 0.46/0.63         (~ (v1_xboole_0 @ (u1_struct_0 @ X31))
% 0.46/0.63          | ~ (l1_struct_0 @ X31)
% 0.46/0.63          | (v2_struct_0 @ X31))),
% 0.46/0.63      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.46/0.63  thf('49', plain,
% 0.46/0.63      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))
% 0.46/0.63        | (v2_struct_0 @ sk_B)
% 0.46/0.63        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.63      inference('sup-', [status(thm)], ['47', '48'])).
% 0.46/0.63  thf('50', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('51', plain,
% 0.46/0.63      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 0.46/0.63      inference('demod', [status(thm)], ['49', '50'])).
% 0.46/0.63  thf('52', plain, (~ (v2_struct_0 @ sk_B)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('53', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.63      inference('clc', [status(thm)], ['51', '52'])).
% 0.46/0.63  thf('54', plain,
% 0.46/0.63      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.63        | ((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)))),
% 0.46/0.63      inference('demod', [status(thm)], ['26', '53'])).
% 0.46/0.63  thf('55', plain,
% 0.46/0.63      (![X31 : $i]:
% 0.46/0.63         (~ (v1_xboole_0 @ (u1_struct_0 @ X31))
% 0.46/0.63          | ~ (l1_struct_0 @ X31)
% 0.46/0.63          | (v2_struct_0 @ X31))),
% 0.46/0.63      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.46/0.63  thf('56', plain,
% 0.46/0.63      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))
% 0.46/0.63        | (v2_struct_0 @ sk_B)
% 0.46/0.63        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.63      inference('sup-', [status(thm)], ['54', '55'])).
% 0.46/0.63  thf('57', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('58', plain,
% 0.46/0.63      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 0.46/0.63      inference('demod', [status(thm)], ['56', '57'])).
% 0.46/0.63  thf('59', plain, (~ (v2_struct_0 @ sk_B)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('60', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.46/0.63      inference('clc', [status(thm)], ['58', '59'])).
% 0.46/0.63  thf('61', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.46/0.63      inference('clc', [status(thm)], ['58', '59'])).
% 0.46/0.63  thf('62', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.46/0.63      inference('clc', [status(thm)], ['58', '59'])).
% 0.46/0.63  thf('63', plain,
% 0.46/0.63      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.63          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.63           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.63          sk_C)),
% 0.46/0.63      inference('demod', [status(thm)], ['9', '60', '61', '62'])).
% 0.46/0.63  thf('64', plain,
% 0.46/0.63      (![X30 : $i]:
% 0.46/0.63         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 0.46/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.63  thf('65', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C @ 
% 0.46/0.63        (k1_zfmisc_1 @ 
% 0.46/0.63         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.63      inference('demod', [status(thm)], ['29', '30'])).
% 0.46/0.63  thf('66', plain,
% 0.46/0.63      (((m1_subset_1 @ sk_C @ 
% 0.46/0.63         (k1_zfmisc_1 @ 
% 0.46/0.63          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.46/0.63        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.63      inference('sup+', [status(thm)], ['64', '65'])).
% 0.46/0.63  thf('67', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('68', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C @ 
% 0.46/0.63        (k1_zfmisc_1 @ 
% 0.46/0.63         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.46/0.63      inference('demod', [status(thm)], ['66', '67'])).
% 0.46/0.63  thf(d4_tops_2, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.63         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.63       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.46/0.63         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.46/0.63  thf('69', plain,
% 0.46/0.63      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.46/0.63         (((k2_relset_1 @ X33 @ X32 @ X34) != (X32))
% 0.46/0.63          | ~ (v2_funct_1 @ X34)
% 0.46/0.63          | ((k2_tops_2 @ X33 @ X32 @ X34) = (k2_funct_1 @ X34))
% 0.46/0.63          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 0.46/0.63          | ~ (v1_funct_2 @ X34 @ X33 @ X32)
% 0.46/0.63          | ~ (v1_funct_1 @ X34))),
% 0.46/0.63      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.46/0.63  thf('70', plain,
% 0.46/0.63      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.63        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.46/0.63        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.63            = (k2_funct_1 @ sk_C))
% 0.46/0.63        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.63        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.63            != (k2_struct_0 @ sk_B)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['68', '69'])).
% 0.46/0.63  thf('71', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('72', plain,
% 0.46/0.63      (![X30 : $i]:
% 0.46/0.63         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 0.46/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.63  thf('73', plain,
% 0.46/0.63      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.63      inference('demod', [status(thm)], ['37', '38'])).
% 0.46/0.63  thf('74', plain,
% 0.46/0.63      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.46/0.63        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.63      inference('sup+', [status(thm)], ['72', '73'])).
% 0.46/0.63  thf('75', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('76', plain,
% 0.46/0.63      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.46/0.63      inference('demod', [status(thm)], ['74', '75'])).
% 0.46/0.63  thf('77', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('78', plain,
% 0.46/0.63      (![X30 : $i]:
% 0.46/0.63         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 0.46/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.63  thf('79', plain,
% 0.46/0.63      (![X30 : $i]:
% 0.46/0.63         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 0.46/0.63      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.63  thf('80', plain,
% 0.46/0.63      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.63         = (k2_struct_0 @ sk_B))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('81', plain,
% 0.46/0.63      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.63          = (k2_struct_0 @ sk_B))
% 0.46/0.63        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.63      inference('sup+', [status(thm)], ['79', '80'])).
% 0.46/0.63  thf('82', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('83', plain,
% 0.46/0.63      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.63         = (k2_struct_0 @ sk_B))),
% 0.46/0.63      inference('demod', [status(thm)], ['81', '82'])).
% 0.46/0.63  thf('84', plain,
% 0.46/0.63      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.63          = (k2_struct_0 @ sk_B))
% 0.46/0.63        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.63      inference('sup+', [status(thm)], ['78', '83'])).
% 0.46/0.63  thf('85', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('86', plain,
% 0.46/0.63      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.63         = (k2_struct_0 @ sk_B))),
% 0.46/0.63      inference('demod', [status(thm)], ['84', '85'])).
% 0.46/0.63  thf('87', plain,
% 0.46/0.63      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.63          = (k2_funct_1 @ sk_C))
% 0.46/0.63        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.46/0.63      inference('demod', [status(thm)], ['70', '71', '76', '77', '86'])).
% 0.46/0.63  thf('88', plain,
% 0.46/0.63      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.63         = (k2_funct_1 @ sk_C))),
% 0.46/0.63      inference('simplify', [status(thm)], ['87'])).
% 0.46/0.63  thf('89', plain,
% 0.46/0.63      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.63          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.63           (k2_funct_1 @ sk_C)) @ 
% 0.46/0.63          sk_C)),
% 0.46/0.63      inference('demod', [status(thm)], ['63', '88'])).
% 0.46/0.63  thf(t55_funct_1, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.63       ( ( v2_funct_1 @ A ) =>
% 0.46/0.63         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.46/0.63           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.46/0.63  thf('90', plain,
% 0.46/0.63      (![X9 : $i]:
% 0.46/0.63         (~ (v2_funct_1 @ X9)
% 0.46/0.63          | ((k1_relat_1 @ X9) = (k2_relat_1 @ (k2_funct_1 @ X9)))
% 0.46/0.63          | ~ (v1_funct_1 @ X9)
% 0.46/0.63          | ~ (v1_relat_1 @ X9))),
% 0.46/0.63      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.46/0.63  thf('91', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C @ 
% 0.46/0.63        (k1_zfmisc_1 @ 
% 0.46/0.63         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.46/0.63      inference('demod', [status(thm)], ['66', '67'])).
% 0.46/0.63  thf(t31_funct_2, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.63         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.63       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.46/0.63         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.46/0.63           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.46/0.63           ( m1_subset_1 @
% 0.46/0.63             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.46/0.63  thf('92', plain,
% 0.46/0.63      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.46/0.63         (~ (v2_funct_1 @ X27)
% 0.46/0.63          | ((k2_relset_1 @ X29 @ X28 @ X27) != (X28))
% 0.46/0.63          | (m1_subset_1 @ (k2_funct_1 @ X27) @ 
% 0.46/0.63             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.46/0.63          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28)))
% 0.46/0.63          | ~ (v1_funct_2 @ X27 @ X29 @ X28)
% 0.46/0.63          | ~ (v1_funct_1 @ X27))),
% 0.46/0.63      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.46/0.63  thf('93', plain,
% 0.46/0.63      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.63        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.46/0.63        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.63           (k1_zfmisc_1 @ 
% 0.46/0.63            (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.46/0.63        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.63            != (k2_struct_0 @ sk_B))
% 0.46/0.63        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.63      inference('sup-', [status(thm)], ['91', '92'])).
% 0.46/0.63  thf('94', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('95', plain,
% 0.46/0.63      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.46/0.63      inference('demod', [status(thm)], ['74', '75'])).
% 0.46/0.63  thf('96', plain,
% 0.46/0.63      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.63         = (k2_struct_0 @ sk_B))),
% 0.46/0.63      inference('demod', [status(thm)], ['84', '85'])).
% 0.46/0.63  thf('97', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('98', plain,
% 0.46/0.63      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.63         (k1_zfmisc_1 @ 
% 0.46/0.63          (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.46/0.63        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.46/0.63      inference('demod', [status(thm)], ['93', '94', '95', '96', '97'])).
% 0.46/0.63  thf('99', plain,
% 0.46/0.63      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.63        (k1_zfmisc_1 @ 
% 0.46/0.63         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.46/0.63      inference('simplify', [status(thm)], ['98'])).
% 0.46/0.63  thf('100', plain,
% 0.46/0.63      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.46/0.63         (((k2_relset_1 @ X33 @ X32 @ X34) != (X32))
% 0.46/0.63          | ~ (v2_funct_1 @ X34)
% 0.46/0.63          | ((k2_tops_2 @ X33 @ X32 @ X34) = (k2_funct_1 @ X34))
% 0.46/0.63          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 0.46/0.63          | ~ (v1_funct_2 @ X34 @ X33 @ X32)
% 0.46/0.63          | ~ (v1_funct_1 @ X34))),
% 0.46/0.63      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.46/0.63  thf('101', plain,
% 0.46/0.63      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.63        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.46/0.63             (k2_struct_0 @ sk_A))
% 0.46/0.63        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.63            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.63        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.63        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.63            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['99', '100'])).
% 0.46/0.63  thf('102', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C @ 
% 0.46/0.63        (k1_zfmisc_1 @ 
% 0.46/0.63         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.46/0.63      inference('demod', [status(thm)], ['66', '67'])).
% 0.46/0.63  thf('103', plain,
% 0.46/0.63      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.46/0.63         (~ (v2_funct_1 @ X27)
% 0.46/0.63          | ((k2_relset_1 @ X29 @ X28 @ X27) != (X28))
% 0.46/0.63          | (v1_funct_1 @ (k2_funct_1 @ X27))
% 0.46/0.63          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28)))
% 0.46/0.63          | ~ (v1_funct_2 @ X27 @ X29 @ X28)
% 0.46/0.63          | ~ (v1_funct_1 @ X27))),
% 0.46/0.63      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.46/0.63  thf('104', plain,
% 0.46/0.63      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.63        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.46/0.63        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.63        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.63            != (k2_struct_0 @ sk_B))
% 0.46/0.63        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.63      inference('sup-', [status(thm)], ['102', '103'])).
% 0.46/0.63  thf('105', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('106', plain,
% 0.46/0.63      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.46/0.63      inference('demod', [status(thm)], ['74', '75'])).
% 0.46/0.63  thf('107', plain,
% 0.46/0.63      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.63         = (k2_struct_0 @ sk_B))),
% 0.46/0.63      inference('demod', [status(thm)], ['84', '85'])).
% 0.46/0.63  thf('108', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('109', plain,
% 0.46/0.63      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.63        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.46/0.63      inference('demod', [status(thm)], ['104', '105', '106', '107', '108'])).
% 0.46/0.63  thf('110', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.63      inference('simplify', [status(thm)], ['109'])).
% 0.46/0.63  thf('111', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C @ 
% 0.46/0.63        (k1_zfmisc_1 @ 
% 0.46/0.63         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.46/0.63      inference('demod', [status(thm)], ['66', '67'])).
% 0.46/0.63  thf('112', plain,
% 0.46/0.63      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.46/0.63         (~ (v2_funct_1 @ X27)
% 0.46/0.63          | ((k2_relset_1 @ X29 @ X28 @ X27) != (X28))
% 0.46/0.63          | (v1_funct_2 @ (k2_funct_1 @ X27) @ X28 @ X29)
% 0.46/0.63          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28)))
% 0.46/0.63          | ~ (v1_funct_2 @ X27 @ X29 @ X28)
% 0.46/0.63          | ~ (v1_funct_1 @ X27))),
% 0.46/0.63      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.46/0.63  thf('113', plain,
% 0.46/0.63      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.63        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.46/0.63        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.46/0.63           (k2_struct_0 @ sk_A))
% 0.46/0.63        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.63            != (k2_struct_0 @ sk_B))
% 0.46/0.63        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.63      inference('sup-', [status(thm)], ['111', '112'])).
% 0.46/0.63  thf('114', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('115', plain,
% 0.46/0.63      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.46/0.63      inference('demod', [status(thm)], ['74', '75'])).
% 0.46/0.63  thf('116', plain,
% 0.46/0.63      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.63         = (k2_struct_0 @ sk_B))),
% 0.46/0.63      inference('demod', [status(thm)], ['84', '85'])).
% 0.46/0.63  thf('117', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('118', plain,
% 0.46/0.63      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.46/0.63         (k2_struct_0 @ sk_A))
% 0.46/0.63        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.46/0.63      inference('demod', [status(thm)], ['113', '114', '115', '116', '117'])).
% 0.46/0.63  thf('119', plain,
% 0.46/0.63      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.46/0.63        (k2_struct_0 @ sk_A))),
% 0.46/0.63      inference('simplify', [status(thm)], ['118'])).
% 0.46/0.63  thf('120', plain,
% 0.46/0.63      (![X9 : $i]:
% 0.46/0.63         (~ (v2_funct_1 @ X9)
% 0.46/0.63          | ((k1_relat_1 @ X9) = (k2_relat_1 @ (k2_funct_1 @ X9)))
% 0.46/0.63          | ~ (v1_funct_1 @ X9)
% 0.46/0.63          | ~ (v1_relat_1 @ X9))),
% 0.46/0.63      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.46/0.63  thf(dt_k2_funct_1, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.63       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.46/0.63         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.46/0.63  thf('121', plain,
% 0.46/0.63      (![X4 : $i]:
% 0.46/0.63         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.46/0.63          | ~ (v1_funct_1 @ X4)
% 0.46/0.63          | ~ (v1_relat_1 @ X4))),
% 0.46/0.63      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.63  thf('122', plain,
% 0.46/0.63      (![X11 : $i]:
% 0.46/0.63         (~ (v2_funct_1 @ X11)
% 0.46/0.63          | ((k2_funct_1 @ (k2_funct_1 @ X11)) = (X11))
% 0.46/0.63          | ~ (v1_funct_1 @ X11)
% 0.46/0.63          | ~ (v1_relat_1 @ X11))),
% 0.46/0.63      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.46/0.63  thf('123', plain,
% 0.46/0.63      (![X9 : $i]:
% 0.46/0.63         (~ (v2_funct_1 @ X9)
% 0.46/0.63          | ((k1_relat_1 @ X9) = (k2_relat_1 @ (k2_funct_1 @ X9)))
% 0.46/0.63          | ~ (v1_funct_1 @ X9)
% 0.46/0.63          | ~ (v1_relat_1 @ X9))),
% 0.46/0.63      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.46/0.63  thf('124', plain,
% 0.46/0.63      (![X4 : $i]:
% 0.46/0.63         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 0.46/0.63          | ~ (v1_funct_1 @ X4)
% 0.46/0.63          | ~ (v1_relat_1 @ X4))),
% 0.46/0.63      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.63  thf('125', plain,
% 0.46/0.63      (![X4 : $i]:
% 0.46/0.63         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.46/0.63          | ~ (v1_funct_1 @ X4)
% 0.46/0.63          | ~ (v1_relat_1 @ X4))),
% 0.46/0.63      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.63  thf(t61_funct_1, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.63       ( ( v2_funct_1 @ A ) =>
% 0.46/0.63         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.46/0.63             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.46/0.63           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.46/0.63             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.46/0.63  thf('126', plain,
% 0.46/0.63      (![X10 : $i]:
% 0.46/0.63         (~ (v2_funct_1 @ X10)
% 0.46/0.63          | ((k5_relat_1 @ (k2_funct_1 @ X10) @ X10)
% 0.46/0.63              = (k6_relat_1 @ (k2_relat_1 @ X10)))
% 0.46/0.63          | ~ (v1_funct_1 @ X10)
% 0.46/0.63          | ~ (v1_relat_1 @ X10))),
% 0.46/0.63      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.46/0.63  thf(t48_funct_1, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.63       ( ![B:$i]:
% 0.46/0.63         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.46/0.63           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.46/0.63               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.46/0.63             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 0.46/0.63  thf('127', plain,
% 0.46/0.63      (![X7 : $i, X8 : $i]:
% 0.46/0.63         (~ (v1_relat_1 @ X7)
% 0.46/0.63          | ~ (v1_funct_1 @ X7)
% 0.46/0.63          | (v2_funct_1 @ X7)
% 0.46/0.63          | ((k2_relat_1 @ X7) != (k1_relat_1 @ X8))
% 0.46/0.63          | ~ (v2_funct_1 @ (k5_relat_1 @ X7 @ X8))
% 0.46/0.63          | ~ (v1_funct_1 @ X8)
% 0.46/0.63          | ~ (v1_relat_1 @ X8))),
% 0.46/0.63      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.46/0.63  thf('128', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (v2_funct_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.46/0.63          | ~ (v1_relat_1 @ X0)
% 0.46/0.63          | ~ (v1_funct_1 @ X0)
% 0.46/0.63          | ~ (v2_funct_1 @ X0)
% 0.46/0.63          | ~ (v1_relat_1 @ X0)
% 0.46/0.63          | ~ (v1_funct_1 @ X0)
% 0.46/0.63          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.46/0.63          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.63          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.63          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['126', '127'])).
% 0.46/0.63  thf(fc4_funct_1, axiom,
% 0.46/0.63    (![A:$i]:
% 0.46/0.63     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.46/0.63       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.46/0.63  thf('129', plain, (![X6 : $i]: (v2_funct_1 @ (k6_relat_1 @ X6))),
% 0.46/0.63      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.46/0.63  thf('130', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (v1_relat_1 @ X0)
% 0.46/0.63          | ~ (v1_funct_1 @ X0)
% 0.46/0.63          | ~ (v2_funct_1 @ X0)
% 0.46/0.63          | ~ (v1_relat_1 @ X0)
% 0.46/0.63          | ~ (v1_funct_1 @ X0)
% 0.46/0.63          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.46/0.63          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.63          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.63          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.46/0.63      inference('demod', [status(thm)], ['128', '129'])).
% 0.46/0.63  thf('131', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.63          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.63          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.63          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.46/0.63          | ~ (v2_funct_1 @ X0)
% 0.46/0.63          | ~ (v1_funct_1 @ X0)
% 0.46/0.63          | ~ (v1_relat_1 @ X0))),
% 0.46/0.63      inference('simplify', [status(thm)], ['130'])).
% 0.46/0.63  thf('132', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (v1_relat_1 @ X0)
% 0.46/0.63          | ~ (v1_funct_1 @ X0)
% 0.46/0.63          | ~ (v1_relat_1 @ X0)
% 0.46/0.63          | ~ (v1_funct_1 @ X0)
% 0.46/0.63          | ~ (v2_funct_1 @ X0)
% 0.46/0.63          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.46/0.63          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.63          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['125', '131'])).
% 0.46/0.63  thf('133', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.63          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.63          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.46/0.63          | ~ (v2_funct_1 @ X0)
% 0.46/0.63          | ~ (v1_funct_1 @ X0)
% 0.46/0.63          | ~ (v1_relat_1 @ X0))),
% 0.46/0.63      inference('simplify', [status(thm)], ['132'])).
% 0.46/0.63  thf('134', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (v1_relat_1 @ X0)
% 0.46/0.63          | ~ (v1_funct_1 @ X0)
% 0.46/0.63          | ~ (v1_relat_1 @ X0)
% 0.46/0.63          | ~ (v1_funct_1 @ X0)
% 0.46/0.63          | ~ (v2_funct_1 @ X0)
% 0.46/0.63          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.46/0.63          | (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['124', '133'])).
% 0.46/0.63  thf('135', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.63          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.46/0.63          | ~ (v2_funct_1 @ X0)
% 0.46/0.63          | ~ (v1_funct_1 @ X0)
% 0.46/0.63          | ~ (v1_relat_1 @ X0))),
% 0.46/0.63      inference('simplify', [status(thm)], ['134'])).
% 0.46/0.63  thf('136', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 0.46/0.63          | ~ (v1_relat_1 @ X0)
% 0.46/0.63          | ~ (v1_funct_1 @ X0)
% 0.46/0.63          | ~ (v2_funct_1 @ X0)
% 0.46/0.63          | ~ (v1_relat_1 @ X0)
% 0.46/0.63          | ~ (v1_funct_1 @ X0)
% 0.46/0.63          | ~ (v2_funct_1 @ X0)
% 0.46/0.63          | (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['123', '135'])).
% 0.46/0.63  thf('137', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.63          | ~ (v2_funct_1 @ X0)
% 0.46/0.63          | ~ (v1_funct_1 @ X0)
% 0.46/0.63          | ~ (v1_relat_1 @ X0))),
% 0.46/0.63      inference('simplify', [status(thm)], ['136'])).
% 0.46/0.63  thf('138', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.63      inference('simplify', [status(thm)], ['109'])).
% 0.46/0.63  thf('139', plain,
% 0.46/0.63      (![X4 : $i]:
% 0.46/0.63         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.46/0.63          | ~ (v1_funct_1 @ X4)
% 0.46/0.63          | ~ (v1_relat_1 @ X4))),
% 0.46/0.63      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.63  thf('140', plain,
% 0.46/0.63      (![X11 : $i]:
% 0.46/0.63         (~ (v2_funct_1 @ X11)
% 0.46/0.63          | ((k2_funct_1 @ (k2_funct_1 @ X11)) = (X11))
% 0.46/0.63          | ~ (v1_funct_1 @ X11)
% 0.46/0.63          | ~ (v1_relat_1 @ X11))),
% 0.46/0.63      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.46/0.63  thf('141', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.63          | ~ (v2_funct_1 @ X0)
% 0.46/0.63          | ~ (v1_funct_1 @ X0)
% 0.46/0.63          | ~ (v1_relat_1 @ X0))),
% 0.46/0.63      inference('simplify', [status(thm)], ['136'])).
% 0.46/0.63  thf('142', plain,
% 0.46/0.63      (![X4 : $i]:
% 0.46/0.63         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 0.46/0.63          | ~ (v1_funct_1 @ X4)
% 0.46/0.63          | ~ (v1_relat_1 @ X4))),
% 0.46/0.63      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.63  thf('143', plain,
% 0.46/0.63      (![X4 : $i]:
% 0.46/0.63         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.46/0.63          | ~ (v1_funct_1 @ X4)
% 0.46/0.63          | ~ (v1_relat_1 @ X4))),
% 0.46/0.63      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.63  thf('144', plain,
% 0.46/0.63      (![X11 : $i]:
% 0.46/0.63         (~ (v2_funct_1 @ X11)
% 0.46/0.63          | ((k2_funct_1 @ (k2_funct_1 @ X11)) = (X11))
% 0.46/0.63          | ~ (v1_funct_1 @ X11)
% 0.46/0.63          | ~ (v1_relat_1 @ X11))),
% 0.46/0.63      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.46/0.63  thf('145', plain,
% 0.46/0.63      (![X10 : $i]:
% 0.46/0.63         (~ (v2_funct_1 @ X10)
% 0.46/0.63          | ((k5_relat_1 @ (k2_funct_1 @ X10) @ X10)
% 0.46/0.63              = (k6_relat_1 @ (k2_relat_1 @ X10)))
% 0.46/0.63          | ~ (v1_funct_1 @ X10)
% 0.46/0.63          | ~ (v1_relat_1 @ X10))),
% 0.46/0.63      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.46/0.63  thf('146', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.46/0.63            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.46/0.63          | ~ (v1_relat_1 @ X0)
% 0.46/0.63          | ~ (v1_funct_1 @ X0)
% 0.46/0.63          | ~ (v2_funct_1 @ X0)
% 0.46/0.63          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.63          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.63          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.46/0.63      inference('sup+', [status(thm)], ['144', '145'])).
% 0.46/0.63  thf('147', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (v1_relat_1 @ X0)
% 0.46/0.63          | ~ (v1_funct_1 @ X0)
% 0.46/0.63          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.63          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.63          | ~ (v2_funct_1 @ X0)
% 0.46/0.63          | ~ (v1_funct_1 @ X0)
% 0.46/0.63          | ~ (v1_relat_1 @ X0)
% 0.46/0.63          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.46/0.63              = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['143', '146'])).
% 0.46/0.63  thf('148', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.46/0.63            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.46/0.63          | ~ (v2_funct_1 @ X0)
% 0.46/0.63          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.63          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.63          | ~ (v1_funct_1 @ X0)
% 0.46/0.63          | ~ (v1_relat_1 @ X0))),
% 0.46/0.63      inference('simplify', [status(thm)], ['147'])).
% 0.46/0.63  thf('149', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (v1_relat_1 @ X0)
% 0.46/0.63          | ~ (v1_funct_1 @ X0)
% 0.46/0.63          | ~ (v1_relat_1 @ X0)
% 0.46/0.63          | ~ (v1_funct_1 @ X0)
% 0.46/0.63          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.63          | ~ (v2_funct_1 @ X0)
% 0.46/0.63          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.46/0.63              = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['142', '148'])).
% 0.46/0.63  thf('150', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.46/0.63            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.46/0.63          | ~ (v2_funct_1 @ X0)
% 0.46/0.63          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.63          | ~ (v1_funct_1 @ X0)
% 0.46/0.63          | ~ (v1_relat_1 @ X0))),
% 0.46/0.63      inference('simplify', [status(thm)], ['149'])).
% 0.46/0.63  thf('151', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (v1_relat_1 @ X0)
% 0.46/0.63          | ~ (v1_funct_1 @ X0)
% 0.46/0.63          | ~ (v2_funct_1 @ X0)
% 0.46/0.63          | ~ (v1_relat_1 @ X0)
% 0.46/0.63          | ~ (v1_funct_1 @ X0)
% 0.46/0.63          | ~ (v2_funct_1 @ X0)
% 0.46/0.63          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.46/0.63              = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['141', '150'])).
% 0.46/0.63  thf('152', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.46/0.63            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.46/0.63          | ~ (v2_funct_1 @ X0)
% 0.46/0.63          | ~ (v1_funct_1 @ X0)
% 0.46/0.63          | ~ (v1_relat_1 @ X0))),
% 0.46/0.63      inference('simplify', [status(thm)], ['151'])).
% 0.46/0.63  thf('153', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.46/0.63            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 0.46/0.63          | ~ (v1_relat_1 @ X0)
% 0.46/0.63          | ~ (v1_funct_1 @ X0)
% 0.46/0.63          | ~ (v2_funct_1 @ X0)
% 0.46/0.63          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.63          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.63          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.46/0.63      inference('sup+', [status(thm)], ['140', '152'])).
% 0.46/0.63  thf('154', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (v1_relat_1 @ X0)
% 0.46/0.63          | ~ (v1_funct_1 @ X0)
% 0.46/0.63          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.63          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.63          | ~ (v2_funct_1 @ X0)
% 0.46/0.63          | ~ (v1_funct_1 @ X0)
% 0.46/0.63          | ~ (v1_relat_1 @ X0)
% 0.46/0.63          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.46/0.63              = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['139', '153'])).
% 0.46/0.63  thf('155', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.46/0.63            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 0.46/0.63          | ~ (v2_funct_1 @ X0)
% 0.46/0.63          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.63          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.63          | ~ (v1_funct_1 @ X0)
% 0.46/0.63          | ~ (v1_relat_1 @ X0))),
% 0.46/0.63      inference('simplify', [status(thm)], ['154'])).
% 0.46/0.63  thf('156', plain,
% 0.46/0.63      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.63        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.63        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.63        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.63        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.46/0.63            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['138', '155'])).
% 0.46/0.63  thf('157', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.63      inference('demod', [status(thm)], ['20', '21'])).
% 0.46/0.63  thf('158', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('159', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('160', plain,
% 0.46/0.63      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.63        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.46/0.63            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))))),
% 0.46/0.63      inference('demod', [status(thm)], ['156', '157', '158', '159'])).
% 0.46/0.63  thf('161', plain,
% 0.46/0.63      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.63        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.63        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.63        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.46/0.63            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['137', '160'])).
% 0.46/0.63  thf('162', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.63      inference('demod', [status(thm)], ['20', '21'])).
% 0.46/0.63  thf('163', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('164', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('165', plain,
% 0.46/0.63      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.46/0.63         = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.46/0.63      inference('demod', [status(thm)], ['161', '162', '163', '164'])).
% 0.46/0.63  thf('166', plain,
% 0.46/0.63      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.46/0.63          = (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 0.46/0.63        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.63        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.63        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.63      inference('sup+', [status(thm)], ['122', '165'])).
% 0.46/0.63  thf('167', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C @ 
% 0.46/0.63        (k1_zfmisc_1 @ 
% 0.46/0.63         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf(redefinition_k2_relset_1, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i]:
% 0.46/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.63       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.46/0.63  thf('168', plain,
% 0.46/0.63      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.46/0.63         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 0.46/0.63          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.46/0.63      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.46/0.63  thf('169', plain,
% 0.46/0.63      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.63         = (k2_relat_1 @ sk_C))),
% 0.46/0.63      inference('sup-', [status(thm)], ['167', '168'])).
% 0.46/0.63  thf('170', plain,
% 0.46/0.63      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.63         = (k2_struct_0 @ sk_B))),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('171', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.63      inference('sup+', [status(thm)], ['169', '170'])).
% 0.46/0.63  thf('172', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.63      inference('demod', [status(thm)], ['20', '21'])).
% 0.46/0.63  thf('173', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('174', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('175', plain,
% 0.46/0.63      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.46/0.63         = (k6_relat_1 @ (k2_struct_0 @ sk_B)))),
% 0.46/0.63      inference('demod', [status(thm)], ['166', '171', '172', '173', '174'])).
% 0.46/0.63  thf('176', plain,
% 0.46/0.63      (![X7 : $i, X8 : $i]:
% 0.46/0.63         (~ (v1_relat_1 @ X7)
% 0.46/0.63          | ~ (v1_funct_1 @ X7)
% 0.46/0.63          | (v2_funct_1 @ X7)
% 0.46/0.63          | ((k2_relat_1 @ X7) != (k1_relat_1 @ X8))
% 0.46/0.63          | ~ (v2_funct_1 @ (k5_relat_1 @ X7 @ X8))
% 0.46/0.63          | ~ (v1_funct_1 @ X8)
% 0.46/0.63          | ~ (v1_relat_1 @ X8))),
% 0.46/0.63      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.46/0.63  thf('177', plain,
% 0.46/0.63      ((~ (v2_funct_1 @ (k6_relat_1 @ (k2_struct_0 @ sk_B)))
% 0.46/0.63        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.63        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.63        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 0.46/0.63        | (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.63        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.63        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['175', '176'])).
% 0.46/0.63  thf('178', plain, (![X6 : $i]: (v2_funct_1 @ (k6_relat_1 @ X6))),
% 0.46/0.63      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.46/0.63  thf('179', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.63      inference('demod', [status(thm)], ['20', '21'])).
% 0.46/0.63  thf('180', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('181', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.63      inference('clc', [status(thm)], ['51', '52'])).
% 0.46/0.63  thf('182', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.63      inference('simplify', [status(thm)], ['109'])).
% 0.46/0.63  thf('183', plain,
% 0.46/0.63      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 0.46/0.63        | (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.63        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.63      inference('demod', [status(thm)],
% 0.46/0.63                ['177', '178', '179', '180', '181', '182'])).
% 0.46/0.63  thf('184', plain,
% 0.46/0.63      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.63        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.63        | (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.63        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['121', '183'])).
% 0.46/0.63  thf('185', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.63      inference('demod', [status(thm)], ['20', '21'])).
% 0.46/0.63  thf('186', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('187', plain,
% 0.46/0.63      (((v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.63        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.46/0.63      inference('demod', [status(thm)], ['184', '185', '186'])).
% 0.46/0.63  thf('188', plain,
% 0.46/0.63      ((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))
% 0.46/0.63        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.63        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.63        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.63        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['120', '187'])).
% 0.46/0.63  thf('189', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.63      inference('clc', [status(thm)], ['51', '52'])).
% 0.46/0.63  thf('190', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.63      inference('demod', [status(thm)], ['20', '21'])).
% 0.46/0.63  thf('191', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('192', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('193', plain,
% 0.46/0.63      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.46/0.63        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.63      inference('demod', [status(thm)], ['188', '189', '190', '191', '192'])).
% 0.46/0.63  thf('194', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.63      inference('simplify', [status(thm)], ['193'])).
% 0.46/0.63  thf('195', plain,
% 0.46/0.63      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.63        (k1_zfmisc_1 @ 
% 0.46/0.63         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.46/0.63      inference('simplify', [status(thm)], ['98'])).
% 0.46/0.63  thf('196', plain,
% 0.46/0.63      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.46/0.63         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 0.46/0.63          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.46/0.63      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.46/0.63  thf('197', plain,
% 0.46/0.63      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.63         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['195', '196'])).
% 0.46/0.63  thf('198', plain,
% 0.46/0.63      ((((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.63          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.63        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.46/0.63      inference('demod', [status(thm)], ['101', '110', '119', '194', '197'])).
% 0.46/0.63  thf('199', plain,
% 0.46/0.63      ((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))
% 0.46/0.63        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.63        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.63        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.63        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.63            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.46/0.63      inference('sup-', [status(thm)], ['90', '198'])).
% 0.46/0.63  thf('200', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.63      inference('clc', [status(thm)], ['51', '52'])).
% 0.46/0.63  thf('201', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.63      inference('demod', [status(thm)], ['20', '21'])).
% 0.46/0.63  thf('202', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('203', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('204', plain,
% 0.46/0.63      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.46/0.63        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.63            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.46/0.63      inference('demod', [status(thm)], ['199', '200', '201', '202', '203'])).
% 0.46/0.63  thf('205', plain,
% 0.46/0.63      (((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.63         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.63      inference('simplify', [status(thm)], ['204'])).
% 0.46/0.63  thf('206', plain,
% 0.46/0.63      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.63          (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)),
% 0.46/0.63      inference('demod', [status(thm)], ['89', '205'])).
% 0.46/0.63  thf('207', plain,
% 0.46/0.63      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.63           sk_C)
% 0.46/0.63        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.63        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.63        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.63      inference('sup-', [status(thm)], ['0', '206'])).
% 0.46/0.63  thf('208', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.63      inference('demod', [status(thm)], ['20', '21'])).
% 0.46/0.63  thf('209', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('210', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('211', plain,
% 0.46/0.63      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.63          sk_C)),
% 0.46/0.63      inference('demod', [status(thm)], ['207', '208', '209', '210'])).
% 0.46/0.63  thf('212', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C @ 
% 0.46/0.63        (k1_zfmisc_1 @ 
% 0.46/0.63         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.63      inference('demod', [status(thm)], ['29', '30'])).
% 0.46/0.63  thf('213', plain,
% 0.46/0.63      ((m1_subset_1 @ sk_C @ 
% 0.46/0.63        (k1_zfmisc_1 @ 
% 0.46/0.63         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.63      inference('demod', [status(thm)], ['29', '30'])).
% 0.46/0.63  thf(reflexivity_r2_funct_2, axiom,
% 0.46/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.63     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.63         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.46/0.63         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.46/0.63         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.63       ( r2_funct_2 @ A @ B @ C @ C ) ))).
% 0.46/0.63  thf('214', plain,
% 0.46/0.63      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.46/0.63         ((r2_funct_2 @ X23 @ X24 @ X25 @ X25)
% 0.46/0.63          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.46/0.63          | ~ (v1_funct_2 @ X25 @ X23 @ X24)
% 0.46/0.63          | ~ (v1_funct_1 @ X25)
% 0.46/0.63          | ~ (v1_funct_1 @ X26)
% 0.46/0.63          | ~ (v1_funct_2 @ X26 @ X23 @ X24)
% 0.46/0.63          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.46/0.63      inference('cnf', [status(esa)], [reflexivity_r2_funct_2])).
% 0.46/0.63  thf('215', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X0 @ 
% 0.46/0.63             (k1_zfmisc_1 @ 
% 0.46/0.63              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.46/0.63          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.63          | ~ (v1_funct_1 @ X0)
% 0.46/0.63          | ~ (v1_funct_1 @ sk_C)
% 0.46/0.63          | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.63          | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.63             sk_C))),
% 0.46/0.63      inference('sup-', [status(thm)], ['213', '214'])).
% 0.46/0.63  thf('216', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('217', plain,
% 0.46/0.63      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.63      inference('demod', [status(thm)], ['37', '38'])).
% 0.46/0.63  thf('218', plain,
% 0.46/0.63      (![X0 : $i]:
% 0.46/0.63         (~ (m1_subset_1 @ X0 @ 
% 0.46/0.63             (k1_zfmisc_1 @ 
% 0.46/0.63              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.46/0.63          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.63          | ~ (v1_funct_1 @ X0)
% 0.46/0.63          | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.63             sk_C))),
% 0.46/0.63      inference('demod', [status(thm)], ['215', '216', '217'])).
% 0.46/0.63  thf('219', plain,
% 0.46/0.63      (((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)
% 0.46/0.63        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.63        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.46/0.63      inference('sup-', [status(thm)], ['212', '218'])).
% 0.46/0.63  thf('220', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.63  thf('221', plain,
% 0.46/0.63      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.63      inference('demod', [status(thm)], ['37', '38'])).
% 0.46/0.63  thf('222', plain,
% 0.46/0.63      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.46/0.63      inference('demod', [status(thm)], ['219', '220', '221'])).
% 0.46/0.63  thf('223', plain, ($false), inference('demod', [status(thm)], ['211', '222'])).
% 0.46/0.63  
% 0.46/0.63  % SZS output end Refutation
% 0.46/0.63  
% 0.46/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
