%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EyAbCrgNPi

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:06 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  317 (3436 expanded)
%              Number of leaves         :   42 (1014 expanded)
%              Depth                    :   52
%              Number of atoms          : 3197 (76058 expanded)
%              Number of equality atoms :  174 (2405 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( v1_partfun1 @ X15 @ X16 )
      | ~ ( v1_funct_2 @ X15 @ X16 @ X17 )
      | ~ ( v1_funct_1 @ X15 )
      | ( v1_xboole_0 @ X17 ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_partfun1 @ X19 @ X18 )
      | ( ( k1_relat_1 @ X19 )
        = X18 )
      | ~ ( v4_relat_1 @ X19 @ X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
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

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('18',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('19',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('21',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v4_relat_1 @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('22',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','19','22'])).

thf('24',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( v1_partfun1 @ X15 @ X16 )
      | ~ ( v1_funct_2 @ X15 @ X16 @ X17 )
      | ~ ( v1_funct_1 @ X15 )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('33',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31','36'])).

thf('38',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_partfun1 @ X19 @ X18 )
      | ( ( k1_relat_1 @ X19 )
        = X18 )
      | ~ ( v4_relat_1 @ X19 @ X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('42',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v4_relat_1 @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('43',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40','43'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('45',plain,(
    ! [X28: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('46',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','50'])).

thf('52',plain,(
    ! [X28: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('53',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('59',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('60',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['8','57','58','59'])).

thf('61',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('62',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('63',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

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

thf('66',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k2_relset_1 @ X30 @ X29 @ X31 )
       != X29 )
      | ~ ( v2_funct_1 @ X31 )
      | ( ( k2_tops_2 @ X30 @ X29 @ X31 )
        = ( k2_funct_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X31 @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('67',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('70',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('71',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('76',plain,(
    ! [X27: $i] :
      ( ( ( k2_struct_0 @ X27 )
        = ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('77',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['75','80'])).

thf('82',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['67','68','73','74','83'])).

thf('85',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['60','85'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('87',plain,(
    ! [X1: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X1 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('88',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

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

thf('89',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relset_1 @ X26 @ X25 @ X24 )
       != X25 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('90',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('93',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('94',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['90','91','92','93','94'])).

thf('96',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k2_relset_1 @ X30 @ X29 @ X31 )
       != X29 )
      | ~ ( v2_funct_1 @ X31 )
      | ( ( k2_tops_2 @ X30 @ X29 @ X31 )
        = ( k2_funct_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X31 @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('98',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('100',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relset_1 @ X26 @ X25 @ X24 )
       != X25 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('101',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('104',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('105',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['101','102','103','104','105'])).

thf('107',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('109',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relset_1 @ X26 @ X25 @ X24 )
       != X25 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X24 ) @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('110',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('113',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('114',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['110','111','112','113','114'])).

thf('116',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('118',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('119',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['98','107','116','119'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('121',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k1_relat_1 @ X2 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('122',plain,(
    ! [X1: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X1 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('123',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k1_relat_1 @ X2 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('124',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('126',plain,(
    ! [X1: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X1 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('127',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k2_relat_1 @ X2 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('128',plain,(
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X3 ) @ X3 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X3 ) ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(t63_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k2_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ( ( k5_relat_1 @ A @ B )
                = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) )
           => ( B
              = ( k2_funct_1 @ A ) ) ) ) ) )).

thf('129',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ( X4
        = ( k2_funct_1 @ X5 ) )
      | ( ( k5_relat_1 @ X5 @ X4 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X5 ) ) )
      | ( ( k2_relat_1 @ X5 )
       != ( k1_relat_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t63_funct_1])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ ( k2_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_relat_1 @ ( k2_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ ( k2_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['127','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['126','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['125','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['124','137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['123','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,(
    ! [X1: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X1 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('143',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('144',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('145',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['140'])).

thf('147',plain,(
    ! [X1: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X1 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['140'])).

thf('151',plain,(
    ! [X1: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X1 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['140'])).

thf('155',plain,(
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k5_relat_1 @ X3 @ ( k2_funct_1 @ X3 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X3 ) ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['154','155'])).

thf('157',plain,(
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
    inference('sup-',[status(thm)],['153','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['152','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['151','160'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['150','162'])).

thf('164',plain,(
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
    inference('sup-',[status(thm)],['149','163'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['164'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['148','165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['147','167'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['146','169'])).

thf('171',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['145','170'])).

thf('172',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['106'])).

thf('173',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('176',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['171','172','173','174','175'])).

thf('177',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['142','176'])).

thf('178',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('179',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ),
    inference(demod,[status(thm)],['177','178','179','180'])).

thf('182',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['141','181'])).

thf('183',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k2_relat_1 @ X2 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('184',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('186',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['186','187'])).

thf('189',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k2_relat_1 @ X2 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('190',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k1_relat_1 @ X19 )
       != X18 )
      | ( v1_partfun1 @ X19 @ X18 )
      | ~ ( v4_relat_1 @ X19 @ X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('191',plain,(
    ! [X19: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v4_relat_1 @ X19 @ ( k1_relat_1 @ X19 ) )
      | ( v1_partfun1 @ X19 @ ( k1_relat_1 @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['190'])).

thf('192',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['189','191'])).

thf('193',plain,
    ( ~ ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['188','192'])).

thf('194',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('197',plain,
    ( ~ ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['193','194','195','196'])).

thf('198',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('199',plain,
    ( ~ ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['197','198'])).

thf('200',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('201',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v4_relat_1 @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('202',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['200','201'])).

thf('203',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['199','202'])).

thf('204',plain,
    ( ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['183','203'])).

thf('205',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['186','187'])).

thf('206',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('207',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['204','205','206','207','208'])).

thf('210',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_partfun1 @ X19 @ X18 )
      | ( ( k1_relat_1 @ X19 )
        = X18 )
      | ~ ( v4_relat_1 @ X19 @ X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('211',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['209','210'])).

thf('212',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('213',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['200','201'])).

thf('214',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['211','212','213'])).

thf('215',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('216',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_relat_1 @ ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['182','214','215','216','217'])).

thf('219',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ( X4
        = ( k2_funct_1 @ X5 ) )
      | ( ( k5_relat_1 @ X5 @ X4 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X5 ) ) )
      | ( ( k2_relat_1 @ X5 )
       != ( k1_relat_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t63_funct_1])).

thf('220',plain,
    ( ( ( k6_relat_1 @ ( k2_struct_0 @ sk_B ) )
     != ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['218','219'])).

thf('221',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['211','212','213'])).

thf('222',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('223',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['106'])).

thf('224',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('225',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('227',plain,
    ( ( ( k6_relat_1 @ ( k2_struct_0 @ sk_B ) )
     != ( k6_relat_1 @ ( k2_struct_0 @ sk_B ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['220','221','222','223','224','225','226'])).

thf('228',plain,
    ( ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['227'])).

thf('229',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['122','228'])).

thf('230',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('231',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['229','230','231','232'])).

thf('234',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['121','233'])).

thf('235',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('236',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('237',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( sk_C
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['234','235','236','237','238'])).

thf('240',plain,
    ( sk_C
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['239'])).

thf('241',plain,(
    ! [X1: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X1 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('242',plain,
    ( sk_C
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['239'])).

thf('243',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k2_relat_1 @ X2 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('244',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['242','243'])).

thf('245',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('246',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('247',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['106'])).

thf('248',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['244','245','246','247'])).

thf('249',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['241','248'])).

thf('250',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('251',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('253',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['249','250','251','252'])).

thf('254',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['120','240','253'])).

thf('255',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C ) ),
    inference(simplify,[status(thm)],['254'])).

thf('256',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['87','255'])).

thf('257',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf('258',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('259',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('260',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['256','257','258','259'])).

thf('261',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['86','260'])).

thf('262',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('263',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(reflexivity_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_funct_2 @ A @ B @ C @ C ) ) )).

thf('264',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( r2_funct_2 @ X20 @ X21 @ X22 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( v1_funct_2 @ X22 @ X20 @ X21 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_2 @ X23 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_funct_2])).

thf('265',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['263','264'])).

thf('266',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('267',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('268',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['265','266','267'])).

thf('269',plain,
    ( ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['262','268'])).

thf('270',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('271',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('272',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['269','270','271'])).

thf('273',plain,(
    $false ),
    inference(demod,[status(thm)],['261','272'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EyAbCrgNPi
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:13:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.60  % Solved by: fo/fo7.sh
% 0.38/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.60  % done 456 iterations in 0.144s
% 0.38/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.60  % SZS output start Refutation
% 0.38/0.60  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.38/0.60  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.38/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.60  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.38/0.60  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.60  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.38/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.60  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.38/0.60  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.38/0.60  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.38/0.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.60  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.38/0.60  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.38/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.60  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.38/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.60  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.38/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.60  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.38/0.60  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.38/0.60  thf(d3_struct_0, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.38/0.60  thf('0', plain,
% 0.38/0.60      (![X27 : $i]:
% 0.38/0.60         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 0.38/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.60  thf('1', plain,
% 0.38/0.60      (![X27 : $i]:
% 0.38/0.60         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 0.38/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.60  thf(t64_tops_2, conjecture,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( l1_struct_0 @ A ) =>
% 0.38/0.60       ( ![B:$i]:
% 0.38/0.60         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.38/0.60           ( ![C:$i]:
% 0.38/0.60             ( ( ( v1_funct_1 @ C ) & 
% 0.38/0.60                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.60                 ( m1_subset_1 @
% 0.38/0.60                   C @ 
% 0.38/0.60                   ( k1_zfmisc_1 @
% 0.38/0.60                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.38/0.60               ( ( ( ( k2_relset_1 @
% 0.38/0.60                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.38/0.60                     ( k2_struct_0 @ B ) ) & 
% 0.38/0.60                   ( v2_funct_1 @ C ) ) =>
% 0.38/0.60                 ( r2_funct_2 @
% 0.38/0.60                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.38/0.60                   ( k2_tops_2 @
% 0.38/0.60                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.38/0.60                     ( k2_tops_2 @
% 0.38/0.60                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.38/0.60                   C ) ) ) ) ) ) ))).
% 0.38/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.60    (~( ![A:$i]:
% 0.38/0.60        ( ( l1_struct_0 @ A ) =>
% 0.38/0.60          ( ![B:$i]:
% 0.38/0.60            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.38/0.60              ( ![C:$i]:
% 0.38/0.60                ( ( ( v1_funct_1 @ C ) & 
% 0.38/0.60                    ( v1_funct_2 @
% 0.38/0.60                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.60                    ( m1_subset_1 @
% 0.38/0.60                      C @ 
% 0.38/0.60                      ( k1_zfmisc_1 @
% 0.38/0.60                        ( k2_zfmisc_1 @
% 0.38/0.60                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.38/0.60                  ( ( ( ( k2_relset_1 @
% 0.38/0.60                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.38/0.60                        ( k2_struct_0 @ B ) ) & 
% 0.38/0.60                      ( v2_funct_1 @ C ) ) =>
% 0.38/0.60                    ( r2_funct_2 @
% 0.38/0.60                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.38/0.60                      ( k2_tops_2 @
% 0.38/0.60                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.38/0.60                        ( k2_tops_2 @
% 0.38/0.60                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.38/0.60                      C ) ) ) ) ) ) ) )),
% 0.38/0.60    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.38/0.60  thf('2', plain,
% 0.38/0.60      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.60          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.60           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.38/0.60          sk_C)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('3', plain,
% 0.38/0.60      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.60           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.60            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.38/0.60           sk_C)
% 0.38/0.60        | ~ (l1_struct_0 @ sk_B))),
% 0.38/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.60  thf('4', plain, ((l1_struct_0 @ sk_B)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('5', plain,
% 0.38/0.60      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.60          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.60           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.38/0.60          sk_C)),
% 0.38/0.60      inference('demod', [status(thm)], ['3', '4'])).
% 0.38/0.60  thf('6', plain,
% 0.38/0.60      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.60           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.60            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.38/0.60           sk_C)
% 0.38/0.60        | ~ (l1_struct_0 @ sk_B))),
% 0.38/0.60      inference('sup-', [status(thm)], ['0', '5'])).
% 0.38/0.60  thf('7', plain, ((l1_struct_0 @ sk_B)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('8', plain,
% 0.38/0.60      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.60          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.60           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.38/0.60          sk_C)),
% 0.38/0.60      inference('demod', [status(thm)], ['6', '7'])).
% 0.38/0.60  thf('9', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_C @ 
% 0.38/0.60        (k1_zfmisc_1 @ 
% 0.38/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(cc5_funct_2, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.38/0.60       ( ![C:$i]:
% 0.38/0.60         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.60           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.38/0.60             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.38/0.60  thf('10', plain,
% 0.38/0.60      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.38/0.60         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.38/0.60          | (v1_partfun1 @ X15 @ X16)
% 0.38/0.60          | ~ (v1_funct_2 @ X15 @ X16 @ X17)
% 0.38/0.60          | ~ (v1_funct_1 @ X15)
% 0.38/0.60          | (v1_xboole_0 @ X17))),
% 0.38/0.60      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.38/0.60  thf('11', plain,
% 0.38/0.60      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.38/0.60        | ~ (v1_funct_1 @ sk_C)
% 0.38/0.60        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.38/0.60        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['9', '10'])).
% 0.38/0.60  thf('12', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('13', plain,
% 0.38/0.60      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('14', plain,
% 0.38/0.60      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.38/0.60        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.38/0.60      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.38/0.60  thf(d4_partfun1, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.38/0.60       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.38/0.60  thf('15', plain,
% 0.38/0.60      (![X18 : $i, X19 : $i]:
% 0.38/0.60         (~ (v1_partfun1 @ X19 @ X18)
% 0.38/0.60          | ((k1_relat_1 @ X19) = (X18))
% 0.38/0.60          | ~ (v4_relat_1 @ X19 @ X18)
% 0.38/0.60          | ~ (v1_relat_1 @ X19))),
% 0.38/0.60      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.38/0.60  thf('16', plain,
% 0.38/0.60      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.38/0.60        | ~ (v1_relat_1 @ sk_C)
% 0.38/0.60        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.38/0.60        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['14', '15'])).
% 0.38/0.60  thf('17', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_C @ 
% 0.38/0.60        (k1_zfmisc_1 @ 
% 0.38/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(cc1_relset_1, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.60       ( v1_relat_1 @ C ) ))).
% 0.38/0.60  thf('18', plain,
% 0.38/0.60      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.38/0.60         ((v1_relat_1 @ X6)
% 0.38/0.60          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.38/0.60      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.38/0.60  thf('19', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.60      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.60  thf('20', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_C @ 
% 0.38/0.60        (k1_zfmisc_1 @ 
% 0.38/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf(cc2_relset_1, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.60       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.38/0.60  thf('21', plain,
% 0.38/0.60      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.38/0.60         ((v4_relat_1 @ X9 @ X10)
% 0.38/0.60          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.38/0.60      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.38/0.60  thf('22', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.38/0.60      inference('sup-', [status(thm)], ['20', '21'])).
% 0.38/0.60  thf('23', plain,
% 0.38/0.60      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.38/0.60        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.38/0.60      inference('demod', [status(thm)], ['16', '19', '22'])).
% 0.38/0.60  thf('24', plain,
% 0.38/0.60      (![X27 : $i]:
% 0.38/0.60         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 0.38/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.60  thf('25', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_C @ 
% 0.38/0.60        (k1_zfmisc_1 @ 
% 0.38/0.60         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('26', plain,
% 0.38/0.60      (((m1_subset_1 @ sk_C @ 
% 0.38/0.60         (k1_zfmisc_1 @ 
% 0.38/0.60          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.38/0.60        | ~ (l1_struct_0 @ sk_A))),
% 0.38/0.60      inference('sup+', [status(thm)], ['24', '25'])).
% 0.38/0.60  thf('27', plain, ((l1_struct_0 @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('28', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_C @ 
% 0.38/0.60        (k1_zfmisc_1 @ 
% 0.38/0.60         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.60      inference('demod', [status(thm)], ['26', '27'])).
% 0.38/0.60  thf('29', plain,
% 0.38/0.60      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.38/0.60         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.38/0.60          | (v1_partfun1 @ X15 @ X16)
% 0.38/0.60          | ~ (v1_funct_2 @ X15 @ X16 @ X17)
% 0.38/0.60          | ~ (v1_funct_1 @ X15)
% 0.38/0.60          | (v1_xboole_0 @ X17))),
% 0.38/0.60      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.38/0.60  thf('30', plain,
% 0.38/0.60      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.38/0.60        | ~ (v1_funct_1 @ sk_C)
% 0.38/0.60        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.38/0.60        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['28', '29'])).
% 0.38/0.60  thf('31', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('32', plain,
% 0.38/0.60      (![X27 : $i]:
% 0.38/0.60         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 0.38/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.60  thf('33', plain,
% 0.38/0.60      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('34', plain,
% 0.38/0.60      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.38/0.60        | ~ (l1_struct_0 @ sk_A))),
% 0.38/0.60      inference('sup+', [status(thm)], ['32', '33'])).
% 0.38/0.60  thf('35', plain, ((l1_struct_0 @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('36', plain,
% 0.38/0.60      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.38/0.60      inference('demod', [status(thm)], ['34', '35'])).
% 0.38/0.60  thf('37', plain,
% 0.38/0.60      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.38/0.60        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.38/0.60      inference('demod', [status(thm)], ['30', '31', '36'])).
% 0.38/0.60  thf('38', plain,
% 0.38/0.60      (![X18 : $i, X19 : $i]:
% 0.38/0.60         (~ (v1_partfun1 @ X19 @ X18)
% 0.38/0.60          | ((k1_relat_1 @ X19) = (X18))
% 0.38/0.60          | ~ (v4_relat_1 @ X19 @ X18)
% 0.38/0.60          | ~ (v1_relat_1 @ X19))),
% 0.38/0.60      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.38/0.60  thf('39', plain,
% 0.38/0.60      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.38/0.60        | ~ (v1_relat_1 @ sk_C)
% 0.38/0.60        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.38/0.60        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['37', '38'])).
% 0.38/0.60  thf('40', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.60      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.60  thf('41', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_C @ 
% 0.38/0.60        (k1_zfmisc_1 @ 
% 0.38/0.60         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.60      inference('demod', [status(thm)], ['26', '27'])).
% 0.38/0.60  thf('42', plain,
% 0.38/0.60      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.38/0.60         ((v4_relat_1 @ X9 @ X10)
% 0.38/0.60          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.38/0.60      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.38/0.60  thf('43', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.38/0.60      inference('sup-', [status(thm)], ['41', '42'])).
% 0.38/0.60  thf('44', plain,
% 0.38/0.60      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.38/0.60        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.38/0.60      inference('demod', [status(thm)], ['39', '40', '43'])).
% 0.38/0.60  thf(fc2_struct_0, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.38/0.60       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.38/0.60  thf('45', plain,
% 0.38/0.60      (![X28 : $i]:
% 0.38/0.60         (~ (v1_xboole_0 @ (u1_struct_0 @ X28))
% 0.38/0.60          | ~ (l1_struct_0 @ X28)
% 0.38/0.60          | (v2_struct_0 @ X28))),
% 0.38/0.60      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.38/0.60  thf('46', plain,
% 0.38/0.60      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))
% 0.38/0.60        | (v2_struct_0 @ sk_B)
% 0.38/0.60        | ~ (l1_struct_0 @ sk_B))),
% 0.38/0.60      inference('sup-', [status(thm)], ['44', '45'])).
% 0.38/0.60  thf('47', plain, ((l1_struct_0 @ sk_B)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('48', plain,
% 0.38/0.60      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 0.38/0.60      inference('demod', [status(thm)], ['46', '47'])).
% 0.38/0.60  thf('49', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('50', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.38/0.60      inference('clc', [status(thm)], ['48', '49'])).
% 0.38/0.60  thf('51', plain,
% 0.38/0.60      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.38/0.60        | ((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)))),
% 0.38/0.60      inference('demod', [status(thm)], ['23', '50'])).
% 0.38/0.60  thf('52', plain,
% 0.38/0.60      (![X28 : $i]:
% 0.38/0.60         (~ (v1_xboole_0 @ (u1_struct_0 @ X28))
% 0.38/0.60          | ~ (l1_struct_0 @ X28)
% 0.38/0.60          | (v2_struct_0 @ X28))),
% 0.38/0.60      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.38/0.60  thf('53', plain,
% 0.38/0.60      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))
% 0.38/0.60        | (v2_struct_0 @ sk_B)
% 0.38/0.60        | ~ (l1_struct_0 @ sk_B))),
% 0.38/0.60      inference('sup-', [status(thm)], ['51', '52'])).
% 0.38/0.60  thf('54', plain, ((l1_struct_0 @ sk_B)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('55', plain,
% 0.38/0.60      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 0.38/0.60      inference('demod', [status(thm)], ['53', '54'])).
% 0.38/0.60  thf('56', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('57', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.38/0.60      inference('clc', [status(thm)], ['55', '56'])).
% 0.38/0.60  thf('58', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.38/0.60      inference('clc', [status(thm)], ['55', '56'])).
% 0.38/0.60  thf('59', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.38/0.60      inference('clc', [status(thm)], ['55', '56'])).
% 0.38/0.60  thf('60', plain,
% 0.38/0.60      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.60          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.60           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.38/0.60          sk_C)),
% 0.38/0.60      inference('demod', [status(thm)], ['8', '57', '58', '59'])).
% 0.38/0.60  thf('61', plain,
% 0.38/0.60      (![X27 : $i]:
% 0.38/0.60         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 0.38/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.60  thf('62', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_C @ 
% 0.38/0.60        (k1_zfmisc_1 @ 
% 0.38/0.60         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.60      inference('demod', [status(thm)], ['26', '27'])).
% 0.38/0.60  thf('63', plain,
% 0.38/0.60      (((m1_subset_1 @ sk_C @ 
% 0.38/0.60         (k1_zfmisc_1 @ 
% 0.38/0.60          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.38/0.60        | ~ (l1_struct_0 @ sk_B))),
% 0.38/0.60      inference('sup+', [status(thm)], ['61', '62'])).
% 0.38/0.60  thf('64', plain, ((l1_struct_0 @ sk_B)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('65', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_C @ 
% 0.38/0.60        (k1_zfmisc_1 @ 
% 0.38/0.60         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.38/0.60      inference('demod', [status(thm)], ['63', '64'])).
% 0.38/0.60  thf(d4_tops_2, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.38/0.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.60       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.38/0.60         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.38/0.60  thf('66', plain,
% 0.38/0.60      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.38/0.60         (((k2_relset_1 @ X30 @ X29 @ X31) != (X29))
% 0.38/0.60          | ~ (v2_funct_1 @ X31)
% 0.38/0.60          | ((k2_tops_2 @ X30 @ X29 @ X31) = (k2_funct_1 @ X31))
% 0.38/0.60          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 0.38/0.60          | ~ (v1_funct_2 @ X31 @ X30 @ X29)
% 0.38/0.60          | ~ (v1_funct_1 @ X31))),
% 0.38/0.60      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.38/0.60  thf('67', plain,
% 0.38/0.60      ((~ (v1_funct_1 @ sk_C)
% 0.38/0.60        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.38/0.60        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.38/0.60            = (k2_funct_1 @ sk_C))
% 0.38/0.60        | ~ (v2_funct_1 @ sk_C)
% 0.38/0.60        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.38/0.60            != (k2_struct_0 @ sk_B)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['65', '66'])).
% 0.38/0.60  thf('68', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('69', plain,
% 0.38/0.60      (![X27 : $i]:
% 0.38/0.60         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 0.38/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.60  thf('70', plain,
% 0.38/0.60      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.38/0.60      inference('demod', [status(thm)], ['34', '35'])).
% 0.38/0.60  thf('71', plain,
% 0.38/0.60      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.38/0.60        | ~ (l1_struct_0 @ sk_B))),
% 0.38/0.60      inference('sup+', [status(thm)], ['69', '70'])).
% 0.38/0.60  thf('72', plain, ((l1_struct_0 @ sk_B)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('73', plain,
% 0.38/0.60      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.38/0.60      inference('demod', [status(thm)], ['71', '72'])).
% 0.38/0.60  thf('74', plain, ((v2_funct_1 @ sk_C)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('75', plain,
% 0.38/0.60      (![X27 : $i]:
% 0.38/0.60         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 0.38/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.60  thf('76', plain,
% 0.38/0.60      (![X27 : $i]:
% 0.38/0.60         (((k2_struct_0 @ X27) = (u1_struct_0 @ X27)) | ~ (l1_struct_0 @ X27))),
% 0.38/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.60  thf('77', plain,
% 0.38/0.60      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.38/0.60         = (k2_struct_0 @ sk_B))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('78', plain,
% 0.38/0.60      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.38/0.60          = (k2_struct_0 @ sk_B))
% 0.38/0.60        | ~ (l1_struct_0 @ sk_A))),
% 0.38/0.60      inference('sup+', [status(thm)], ['76', '77'])).
% 0.38/0.60  thf('79', plain, ((l1_struct_0 @ sk_A)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('80', plain,
% 0.38/0.60      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.38/0.60         = (k2_struct_0 @ sk_B))),
% 0.38/0.60      inference('demod', [status(thm)], ['78', '79'])).
% 0.38/0.60  thf('81', plain,
% 0.38/0.60      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.38/0.60          = (k2_struct_0 @ sk_B))
% 0.38/0.60        | ~ (l1_struct_0 @ sk_B))),
% 0.38/0.60      inference('sup+', [status(thm)], ['75', '80'])).
% 0.38/0.60  thf('82', plain, ((l1_struct_0 @ sk_B)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('83', plain,
% 0.38/0.60      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.38/0.60         = (k2_struct_0 @ sk_B))),
% 0.38/0.60      inference('demod', [status(thm)], ['81', '82'])).
% 0.38/0.60  thf('84', plain,
% 0.38/0.60      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.38/0.60          = (k2_funct_1 @ sk_C))
% 0.38/0.60        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.38/0.60      inference('demod', [status(thm)], ['67', '68', '73', '74', '83'])).
% 0.38/0.60  thf('85', plain,
% 0.38/0.60      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.38/0.60         = (k2_funct_1 @ sk_C))),
% 0.38/0.60      inference('simplify', [status(thm)], ['84'])).
% 0.38/0.60  thf('86', plain,
% 0.38/0.60      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.38/0.60          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.60           (k2_funct_1 @ sk_C)) @ 
% 0.38/0.60          sk_C)),
% 0.38/0.60      inference('demod', [status(thm)], ['60', '85'])).
% 0.38/0.60  thf(fc6_funct_1, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.38/0.60       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.38/0.60         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 0.38/0.60         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.38/0.60  thf('87', plain,
% 0.38/0.60      (![X1 : $i]:
% 0.38/0.60         ((v2_funct_1 @ (k2_funct_1 @ X1))
% 0.38/0.60          | ~ (v2_funct_1 @ X1)
% 0.38/0.60          | ~ (v1_funct_1 @ X1)
% 0.38/0.60          | ~ (v1_relat_1 @ X1))),
% 0.38/0.60      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.38/0.60  thf('88', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_C @ 
% 0.38/0.60        (k1_zfmisc_1 @ 
% 0.38/0.60         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.38/0.60      inference('demod', [status(thm)], ['63', '64'])).
% 0.38/0.60  thf(t31_funct_2, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.38/0.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.60       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.38/0.60         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.38/0.60           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.38/0.60           ( m1_subset_1 @
% 0.38/0.60             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.38/0.60  thf('89', plain,
% 0.38/0.60      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.38/0.60         (~ (v2_funct_1 @ X24)
% 0.38/0.60          | ((k2_relset_1 @ X26 @ X25 @ X24) != (X25))
% 0.38/0.60          | (m1_subset_1 @ (k2_funct_1 @ X24) @ 
% 0.38/0.60             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.38/0.60          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 0.38/0.60          | ~ (v1_funct_2 @ X24 @ X26 @ X25)
% 0.38/0.60          | ~ (v1_funct_1 @ X24))),
% 0.38/0.60      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.38/0.60  thf('90', plain,
% 0.38/0.60      ((~ (v1_funct_1 @ sk_C)
% 0.38/0.60        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.38/0.60        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.38/0.60           (k1_zfmisc_1 @ 
% 0.38/0.60            (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.38/0.60        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.38/0.60            != (k2_struct_0 @ sk_B))
% 0.38/0.60        | ~ (v2_funct_1 @ sk_C))),
% 0.38/0.60      inference('sup-', [status(thm)], ['88', '89'])).
% 0.38/0.60  thf('91', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('92', plain,
% 0.38/0.60      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.38/0.60      inference('demod', [status(thm)], ['71', '72'])).
% 0.38/0.60  thf('93', plain,
% 0.38/0.60      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.38/0.60         = (k2_struct_0 @ sk_B))),
% 0.38/0.60      inference('demod', [status(thm)], ['81', '82'])).
% 0.38/0.60  thf('94', plain, ((v2_funct_1 @ sk_C)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('95', plain,
% 0.38/0.60      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.38/0.60         (k1_zfmisc_1 @ 
% 0.38/0.60          (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.38/0.60        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.38/0.60      inference('demod', [status(thm)], ['90', '91', '92', '93', '94'])).
% 0.38/0.60  thf('96', plain,
% 0.38/0.60      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.38/0.60        (k1_zfmisc_1 @ 
% 0.38/0.60         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.38/0.60      inference('simplify', [status(thm)], ['95'])).
% 0.38/0.60  thf('97', plain,
% 0.38/0.60      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.38/0.60         (((k2_relset_1 @ X30 @ X29 @ X31) != (X29))
% 0.38/0.60          | ~ (v2_funct_1 @ X31)
% 0.38/0.60          | ((k2_tops_2 @ X30 @ X29 @ X31) = (k2_funct_1 @ X31))
% 0.38/0.60          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 0.38/0.60          | ~ (v1_funct_2 @ X31 @ X30 @ X29)
% 0.38/0.60          | ~ (v1_funct_1 @ X31))),
% 0.38/0.60      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.38/0.60  thf('98', plain,
% 0.38/0.60      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.38/0.60        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.38/0.60             (k2_struct_0 @ sk_A))
% 0.38/0.60        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.60            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.38/0.60        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.38/0.60        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.60            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['96', '97'])).
% 0.38/0.60  thf('99', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_C @ 
% 0.38/0.60        (k1_zfmisc_1 @ 
% 0.38/0.60         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.38/0.60      inference('demod', [status(thm)], ['63', '64'])).
% 0.38/0.60  thf('100', plain,
% 0.38/0.60      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.38/0.60         (~ (v2_funct_1 @ X24)
% 0.38/0.60          | ((k2_relset_1 @ X26 @ X25 @ X24) != (X25))
% 0.38/0.60          | (v1_funct_1 @ (k2_funct_1 @ X24))
% 0.38/0.60          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 0.38/0.60          | ~ (v1_funct_2 @ X24 @ X26 @ X25)
% 0.38/0.60          | ~ (v1_funct_1 @ X24))),
% 0.38/0.60      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.38/0.60  thf('101', plain,
% 0.38/0.60      ((~ (v1_funct_1 @ sk_C)
% 0.38/0.60        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.38/0.60        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.38/0.60        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.38/0.60            != (k2_struct_0 @ sk_B))
% 0.38/0.60        | ~ (v2_funct_1 @ sk_C))),
% 0.38/0.60      inference('sup-', [status(thm)], ['99', '100'])).
% 0.38/0.60  thf('102', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('103', plain,
% 0.38/0.60      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.38/0.60      inference('demod', [status(thm)], ['71', '72'])).
% 0.38/0.60  thf('104', plain,
% 0.38/0.60      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.38/0.60         = (k2_struct_0 @ sk_B))),
% 0.38/0.60      inference('demod', [status(thm)], ['81', '82'])).
% 0.38/0.60  thf('105', plain, ((v2_funct_1 @ sk_C)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('106', plain,
% 0.38/0.60      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.38/0.60        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.38/0.60      inference('demod', [status(thm)], ['101', '102', '103', '104', '105'])).
% 0.38/0.60  thf('107', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.38/0.60      inference('simplify', [status(thm)], ['106'])).
% 0.38/0.60  thf('108', plain,
% 0.38/0.60      ((m1_subset_1 @ sk_C @ 
% 0.38/0.60        (k1_zfmisc_1 @ 
% 0.38/0.60         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.38/0.60      inference('demod', [status(thm)], ['63', '64'])).
% 0.38/0.60  thf('109', plain,
% 0.38/0.60      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.38/0.60         (~ (v2_funct_1 @ X24)
% 0.38/0.60          | ((k2_relset_1 @ X26 @ X25 @ X24) != (X25))
% 0.38/0.60          | (v1_funct_2 @ (k2_funct_1 @ X24) @ X25 @ X26)
% 0.38/0.60          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 0.38/0.60          | ~ (v1_funct_2 @ X24 @ X26 @ X25)
% 0.38/0.60          | ~ (v1_funct_1 @ X24))),
% 0.38/0.60      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.38/0.60  thf('110', plain,
% 0.38/0.60      ((~ (v1_funct_1 @ sk_C)
% 0.38/0.60        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.38/0.60        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.38/0.60           (k2_struct_0 @ sk_A))
% 0.38/0.60        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.38/0.60            != (k2_struct_0 @ sk_B))
% 0.38/0.60        | ~ (v2_funct_1 @ sk_C))),
% 0.38/0.60      inference('sup-', [status(thm)], ['108', '109'])).
% 0.38/0.60  thf('111', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('112', plain,
% 0.38/0.60      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.38/0.60      inference('demod', [status(thm)], ['71', '72'])).
% 0.38/0.60  thf('113', plain,
% 0.38/0.60      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.38/0.60         = (k2_struct_0 @ sk_B))),
% 0.38/0.60      inference('demod', [status(thm)], ['81', '82'])).
% 0.38/0.60  thf('114', plain, ((v2_funct_1 @ sk_C)),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('115', plain,
% 0.38/0.60      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.38/0.60         (k2_struct_0 @ sk_A))
% 0.38/0.60        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.38/0.60      inference('demod', [status(thm)], ['110', '111', '112', '113', '114'])).
% 0.38/0.60  thf('116', plain,
% 0.38/0.60      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.38/0.60        (k2_struct_0 @ sk_A))),
% 0.38/0.60      inference('simplify', [status(thm)], ['115'])).
% 0.38/0.60  thf('117', plain,
% 0.38/0.60      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.38/0.60        (k1_zfmisc_1 @ 
% 0.38/0.60         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.38/0.60      inference('simplify', [status(thm)], ['95'])).
% 0.38/0.60  thf(redefinition_k2_relset_1, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.60       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.38/0.60  thf('118', plain,
% 0.38/0.60      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.38/0.60         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 0.38/0.60          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.38/0.60      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.38/0.60  thf('119', plain,
% 0.38/0.60      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.60         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['117', '118'])).
% 0.38/0.60  thf('120', plain,
% 0.38/0.60      ((((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.60          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.38/0.60        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.38/0.60        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.38/0.60      inference('demod', [status(thm)], ['98', '107', '116', '119'])).
% 0.38/0.60  thf(t55_funct_1, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.60       ( ( v2_funct_1 @ A ) =>
% 0.38/0.60         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.38/0.60           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.38/0.60  thf('121', plain,
% 0.38/0.60      (![X2 : $i]:
% 0.38/0.60         (~ (v2_funct_1 @ X2)
% 0.38/0.60          | ((k1_relat_1 @ X2) = (k2_relat_1 @ (k2_funct_1 @ X2)))
% 0.38/0.60          | ~ (v1_funct_1 @ X2)
% 0.38/0.60          | ~ (v1_relat_1 @ X2))),
% 0.38/0.60      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.38/0.60  thf('122', plain,
% 0.38/0.60      (![X1 : $i]:
% 0.38/0.60         ((v2_funct_1 @ (k2_funct_1 @ X1))
% 0.38/0.60          | ~ (v2_funct_1 @ X1)
% 0.38/0.60          | ~ (v1_funct_1 @ X1)
% 0.38/0.60          | ~ (v1_relat_1 @ X1))),
% 0.38/0.60      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.38/0.60  thf('123', plain,
% 0.38/0.60      (![X2 : $i]:
% 0.38/0.60         (~ (v2_funct_1 @ X2)
% 0.38/0.60          | ((k1_relat_1 @ X2) = (k2_relat_1 @ (k2_funct_1 @ X2)))
% 0.38/0.60          | ~ (v1_funct_1 @ X2)
% 0.38/0.60          | ~ (v1_relat_1 @ X2))),
% 0.38/0.60      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.38/0.60  thf(dt_k2_funct_1, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.60       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.38/0.60         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.38/0.60  thf('124', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.38/0.60          | ~ (v1_funct_1 @ X0)
% 0.38/0.60          | ~ (v1_relat_1 @ X0))),
% 0.38/0.60      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.38/0.60  thf('125', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.60          | ~ (v1_funct_1 @ X0)
% 0.38/0.60          | ~ (v1_relat_1 @ X0))),
% 0.38/0.60      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.38/0.60  thf('126', plain,
% 0.38/0.60      (![X1 : $i]:
% 0.38/0.60         ((v2_funct_1 @ (k2_funct_1 @ X1))
% 0.38/0.60          | ~ (v2_funct_1 @ X1)
% 0.38/0.60          | ~ (v1_funct_1 @ X1)
% 0.38/0.60          | ~ (v1_relat_1 @ X1))),
% 0.38/0.60      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.38/0.60  thf('127', plain,
% 0.38/0.60      (![X2 : $i]:
% 0.38/0.60         (~ (v2_funct_1 @ X2)
% 0.38/0.60          | ((k2_relat_1 @ X2) = (k1_relat_1 @ (k2_funct_1 @ X2)))
% 0.38/0.60          | ~ (v1_funct_1 @ X2)
% 0.38/0.60          | ~ (v1_relat_1 @ X2))),
% 0.38/0.60      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.38/0.60  thf(t61_funct_1, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.60       ( ( v2_funct_1 @ A ) =>
% 0.38/0.60         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.38/0.60             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.38/0.60           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.38/0.60             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.38/0.60  thf('128', plain,
% 0.38/0.60      (![X3 : $i]:
% 0.38/0.60         (~ (v2_funct_1 @ X3)
% 0.38/0.60          | ((k5_relat_1 @ (k2_funct_1 @ X3) @ X3)
% 0.38/0.60              = (k6_relat_1 @ (k2_relat_1 @ X3)))
% 0.38/0.60          | ~ (v1_funct_1 @ X3)
% 0.38/0.60          | ~ (v1_relat_1 @ X3))),
% 0.38/0.60      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.38/0.60  thf(t63_funct_1, axiom,
% 0.38/0.60    (![A:$i]:
% 0.38/0.60     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.60       ( ![B:$i]:
% 0.38/0.60         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.38/0.60           ( ( ( v2_funct_1 @ A ) & 
% 0.38/0.60               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.38/0.60               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.38/0.60             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.38/0.60  thf('129', plain,
% 0.38/0.60      (![X4 : $i, X5 : $i]:
% 0.38/0.60         (~ (v1_relat_1 @ X4)
% 0.38/0.60          | ~ (v1_funct_1 @ X4)
% 0.38/0.60          | ((X4) = (k2_funct_1 @ X5))
% 0.38/0.60          | ((k5_relat_1 @ X5 @ X4) != (k6_relat_1 @ (k1_relat_1 @ X5)))
% 0.38/0.60          | ((k2_relat_1 @ X5) != (k1_relat_1 @ X4))
% 0.38/0.60          | ~ (v2_funct_1 @ X5)
% 0.38/0.60          | ~ (v1_funct_1 @ X5)
% 0.38/0.60          | ~ (v1_relat_1 @ X5))),
% 0.38/0.60      inference('cnf', [status(esa)], [t63_funct_1])).
% 0.38/0.60  thf('130', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (((k6_relat_1 @ (k2_relat_1 @ X0))
% 0.38/0.60            != (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.38/0.60          | ~ (v1_relat_1 @ X0)
% 0.38/0.60          | ~ (v1_funct_1 @ X0)
% 0.38/0.60          | ~ (v2_funct_1 @ X0)
% 0.38/0.60          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.38/0.60          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.60          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.60          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.38/0.60          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.38/0.60          | ~ (v1_funct_1 @ X0)
% 0.38/0.60          | ~ (v1_relat_1 @ X0))),
% 0.38/0.60      inference('sup-', [status(thm)], ['128', '129'])).
% 0.38/0.60  thf('131', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.38/0.60          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.38/0.60          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.60          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.60          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.38/0.60          | ~ (v2_funct_1 @ X0)
% 0.38/0.60          | ~ (v1_funct_1 @ X0)
% 0.38/0.60          | ~ (v1_relat_1 @ X0)
% 0.38/0.60          | ((k6_relat_1 @ (k2_relat_1 @ X0))
% 0.38/0.60              != (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.38/0.60      inference('simplify', [status(thm)], ['130'])).
% 0.38/0.60  thf('132', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (((k6_relat_1 @ (k2_relat_1 @ X0)) != (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.38/0.60          | ~ (v1_relat_1 @ X0)
% 0.38/0.60          | ~ (v1_funct_1 @ X0)
% 0.38/0.60          | ~ (v2_funct_1 @ X0)
% 0.38/0.60          | ~ (v1_relat_1 @ X0)
% 0.38/0.60          | ~ (v1_funct_1 @ X0)
% 0.38/0.60          | ~ (v2_funct_1 @ X0)
% 0.38/0.60          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.38/0.60          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.60          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.60          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.38/0.60          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['127', '131'])).
% 0.38/0.60  thf('133', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.38/0.60          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.38/0.60          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.60          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.60          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.38/0.60          | ~ (v2_funct_1 @ X0)
% 0.38/0.60          | ~ (v1_funct_1 @ X0)
% 0.38/0.60          | ~ (v1_relat_1 @ X0))),
% 0.38/0.60      inference('simplify', [status(thm)], ['132'])).
% 0.38/0.60  thf('134', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (~ (v1_relat_1 @ X0)
% 0.38/0.60          | ~ (v1_funct_1 @ X0)
% 0.38/0.60          | ~ (v2_funct_1 @ X0)
% 0.38/0.60          | ~ (v1_relat_1 @ X0)
% 0.38/0.60          | ~ (v1_funct_1 @ X0)
% 0.38/0.60          | ~ (v2_funct_1 @ X0)
% 0.38/0.60          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.38/0.60          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.60          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.38/0.60          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['126', '133'])).
% 0.38/0.60  thf('135', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.38/0.60          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.38/0.60          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.60          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.38/0.60          | ~ (v2_funct_1 @ X0)
% 0.38/0.60          | ~ (v1_funct_1 @ X0)
% 0.38/0.60          | ~ (v1_relat_1 @ X0))),
% 0.38/0.60      inference('simplify', [status(thm)], ['134'])).
% 0.38/0.60  thf('136', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (~ (v1_relat_1 @ X0)
% 0.38/0.60          | ~ (v1_funct_1 @ X0)
% 0.38/0.60          | ~ (v1_relat_1 @ X0)
% 0.38/0.60          | ~ (v1_funct_1 @ X0)
% 0.38/0.60          | ~ (v2_funct_1 @ X0)
% 0.38/0.60          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.38/0.60          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.38/0.60          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['125', '135'])).
% 0.38/0.60  thf('137', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.38/0.60          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.38/0.60          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.38/0.60          | ~ (v2_funct_1 @ X0)
% 0.38/0.60          | ~ (v1_funct_1 @ X0)
% 0.38/0.60          | ~ (v1_relat_1 @ X0))),
% 0.38/0.60      inference('simplify', [status(thm)], ['136'])).
% 0.38/0.60  thf('138', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (~ (v1_relat_1 @ X0)
% 0.38/0.60          | ~ (v1_funct_1 @ X0)
% 0.38/0.60          | ~ (v1_relat_1 @ X0)
% 0.38/0.60          | ~ (v1_funct_1 @ X0)
% 0.38/0.60          | ~ (v2_funct_1 @ X0)
% 0.38/0.60          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.38/0.60          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['124', '137'])).
% 0.38/0.60  thf('139', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.38/0.60          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.38/0.60          | ~ (v2_funct_1 @ X0)
% 0.38/0.60          | ~ (v1_funct_1 @ X0)
% 0.38/0.60          | ~ (v1_relat_1 @ X0))),
% 0.38/0.60      inference('simplify', [status(thm)], ['138'])).
% 0.38/0.60  thf('140', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 0.38/0.60          | ~ (v1_relat_1 @ X0)
% 0.38/0.60          | ~ (v1_funct_1 @ X0)
% 0.38/0.60          | ~ (v2_funct_1 @ X0)
% 0.38/0.60          | ~ (v1_relat_1 @ X0)
% 0.38/0.60          | ~ (v1_funct_1 @ X0)
% 0.38/0.60          | ~ (v2_funct_1 @ X0)
% 0.38/0.60          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.38/0.60      inference('sup-', [status(thm)], ['123', '139'])).
% 0.38/0.60  thf('141', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.38/0.60          | ~ (v2_funct_1 @ X0)
% 0.38/0.60          | ~ (v1_funct_1 @ X0)
% 0.38/0.60          | ~ (v1_relat_1 @ X0))),
% 0.38/0.60      inference('simplify', [status(thm)], ['140'])).
% 0.38/0.60  thf('142', plain,
% 0.38/0.60      (![X1 : $i]:
% 0.38/0.60         ((v2_funct_1 @ (k2_funct_1 @ X1))
% 0.38/0.60          | ~ (v2_funct_1 @ X1)
% 0.38/0.60          | ~ (v1_funct_1 @ X1)
% 0.38/0.60          | ~ (v1_relat_1 @ X1))),
% 0.38/0.60      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.38/0.60  thf('143', plain,
% 0.38/0.60      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.38/0.60        (k1_zfmisc_1 @ 
% 0.38/0.60         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.38/0.60      inference('simplify', [status(thm)], ['95'])).
% 0.38/0.60  thf('144', plain,
% 0.38/0.60      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.38/0.60         ((v1_relat_1 @ X6)
% 0.38/0.60          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.38/0.60      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.38/0.60  thf('145', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.38/0.60      inference('sup-', [status(thm)], ['143', '144'])).
% 0.38/0.60  thf('146', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.38/0.60          | ~ (v2_funct_1 @ X0)
% 0.38/0.60          | ~ (v1_funct_1 @ X0)
% 0.38/0.60          | ~ (v1_relat_1 @ X0))),
% 0.38/0.60      inference('simplify', [status(thm)], ['140'])).
% 0.38/0.60  thf('147', plain,
% 0.38/0.60      (![X1 : $i]:
% 0.38/0.60         ((v2_funct_1 @ (k2_funct_1 @ X1))
% 0.38/0.60          | ~ (v2_funct_1 @ X1)
% 0.38/0.60          | ~ (v1_funct_1 @ X1)
% 0.38/0.60          | ~ (v1_relat_1 @ X1))),
% 0.38/0.60      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.38/0.60  thf('148', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.60          | ~ (v1_funct_1 @ X0)
% 0.38/0.60          | ~ (v1_relat_1 @ X0))),
% 0.38/0.60      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.38/0.60  thf('149', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.38/0.60          | ~ (v1_funct_1 @ X0)
% 0.38/0.60          | ~ (v1_relat_1 @ X0))),
% 0.38/0.60      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.38/0.60  thf('150', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.38/0.60          | ~ (v2_funct_1 @ X0)
% 0.38/0.60          | ~ (v1_funct_1 @ X0)
% 0.38/0.60          | ~ (v1_relat_1 @ X0))),
% 0.38/0.60      inference('simplify', [status(thm)], ['140'])).
% 0.38/0.60  thf('151', plain,
% 0.38/0.60      (![X1 : $i]:
% 0.38/0.60         ((v2_funct_1 @ (k2_funct_1 @ X1))
% 0.38/0.60          | ~ (v2_funct_1 @ X1)
% 0.38/0.60          | ~ (v1_funct_1 @ X1)
% 0.38/0.60          | ~ (v1_relat_1 @ X1))),
% 0.38/0.60      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.38/0.60  thf('152', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.60          | ~ (v1_funct_1 @ X0)
% 0.38/0.60          | ~ (v1_relat_1 @ X0))),
% 0.38/0.60      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.38/0.60  thf('153', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.38/0.60          | ~ (v1_funct_1 @ X0)
% 0.38/0.60          | ~ (v1_relat_1 @ X0))),
% 0.38/0.60      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.38/0.60  thf('154', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.38/0.60          | ~ (v2_funct_1 @ X0)
% 0.38/0.60          | ~ (v1_funct_1 @ X0)
% 0.38/0.60          | ~ (v1_relat_1 @ X0))),
% 0.38/0.60      inference('simplify', [status(thm)], ['140'])).
% 0.38/0.60  thf('155', plain,
% 0.38/0.60      (![X3 : $i]:
% 0.38/0.60         (~ (v2_funct_1 @ X3)
% 0.38/0.60          | ((k5_relat_1 @ X3 @ (k2_funct_1 @ X3))
% 0.38/0.60              = (k6_relat_1 @ (k1_relat_1 @ X3)))
% 0.38/0.60          | ~ (v1_funct_1 @ X3)
% 0.38/0.60          | ~ (v1_relat_1 @ X3))),
% 0.38/0.60      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.38/0.60  thf('156', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.38/0.60            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.38/0.60          | ~ (v1_relat_1 @ X0)
% 0.38/0.60          | ~ (v1_funct_1 @ X0)
% 0.38/0.60          | ~ (v2_funct_1 @ X0)
% 0.38/0.60          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.38/0.60          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.60          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.38/0.60      inference('sup+', [status(thm)], ['154', '155'])).
% 0.38/0.60  thf('157', plain,
% 0.38/0.60      (![X0 : $i]:
% 0.38/0.60         (~ (v1_relat_1 @ X0)
% 0.38/0.60          | ~ (v1_funct_1 @ X0)
% 0.38/0.60          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.60          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.60          | ~ (v2_funct_1 @ X0)
% 0.38/0.60          | ~ (v1_funct_1 @ X0)
% 0.38/0.60          | ~ (v1_relat_1 @ X0)
% 0.38/0.60          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.38/0.60              = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.38/0.61      inference('sup-', [status(thm)], ['153', '156'])).
% 0.38/0.61  thf('158', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.38/0.61            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.38/0.61          | ~ (v2_funct_1 @ X0)
% 0.38/0.61          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.61          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.61          | ~ (v1_funct_1 @ X0)
% 0.38/0.61          | ~ (v1_relat_1 @ X0))),
% 0.38/0.61      inference('simplify', [status(thm)], ['157'])).
% 0.38/0.61  thf('159', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (~ (v1_relat_1 @ X0)
% 0.38/0.61          | ~ (v1_funct_1 @ X0)
% 0.38/0.61          | ~ (v1_relat_1 @ X0)
% 0.38/0.61          | ~ (v1_funct_1 @ X0)
% 0.38/0.61          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.61          | ~ (v2_funct_1 @ X0)
% 0.38/0.61          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.38/0.61              = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.38/0.61      inference('sup-', [status(thm)], ['152', '158'])).
% 0.38/0.61  thf('160', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.38/0.61            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.38/0.61          | ~ (v2_funct_1 @ X0)
% 0.38/0.61          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.61          | ~ (v1_funct_1 @ X0)
% 0.38/0.61          | ~ (v1_relat_1 @ X0))),
% 0.38/0.61      inference('simplify', [status(thm)], ['159'])).
% 0.38/0.61  thf('161', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (~ (v1_relat_1 @ X0)
% 0.38/0.61          | ~ (v1_funct_1 @ X0)
% 0.38/0.61          | ~ (v2_funct_1 @ X0)
% 0.38/0.61          | ~ (v1_relat_1 @ X0)
% 0.38/0.61          | ~ (v1_funct_1 @ X0)
% 0.38/0.61          | ~ (v2_funct_1 @ X0)
% 0.38/0.61          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.38/0.61              = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.38/0.61      inference('sup-', [status(thm)], ['151', '160'])).
% 0.38/0.61  thf('162', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.38/0.61            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.38/0.61          | ~ (v2_funct_1 @ X0)
% 0.38/0.61          | ~ (v1_funct_1 @ X0)
% 0.38/0.61          | ~ (v1_relat_1 @ X0))),
% 0.38/0.61      inference('simplify', [status(thm)], ['161'])).
% 0.38/0.61  thf('163', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.38/0.61            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 0.38/0.61          | ~ (v1_relat_1 @ X0)
% 0.38/0.61          | ~ (v1_funct_1 @ X0)
% 0.38/0.61          | ~ (v2_funct_1 @ X0)
% 0.38/0.61          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.38/0.61          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.61          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.38/0.61      inference('sup+', [status(thm)], ['150', '162'])).
% 0.38/0.61  thf('164', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (~ (v1_relat_1 @ X0)
% 0.38/0.61          | ~ (v1_funct_1 @ X0)
% 0.38/0.61          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.61          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.61          | ~ (v2_funct_1 @ X0)
% 0.38/0.61          | ~ (v1_funct_1 @ X0)
% 0.38/0.61          | ~ (v1_relat_1 @ X0)
% 0.38/0.61          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.38/0.61              = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))))),
% 0.38/0.61      inference('sup-', [status(thm)], ['149', '163'])).
% 0.38/0.61  thf('165', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.38/0.61            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 0.38/0.61          | ~ (v2_funct_1 @ X0)
% 0.38/0.61          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.61          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.61          | ~ (v1_funct_1 @ X0)
% 0.38/0.61          | ~ (v1_relat_1 @ X0))),
% 0.38/0.61      inference('simplify', [status(thm)], ['164'])).
% 0.38/0.61  thf('166', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (~ (v1_relat_1 @ X0)
% 0.38/0.61          | ~ (v1_funct_1 @ X0)
% 0.38/0.61          | ~ (v1_relat_1 @ X0)
% 0.38/0.61          | ~ (v1_funct_1 @ X0)
% 0.38/0.61          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.61          | ~ (v2_funct_1 @ X0)
% 0.38/0.61          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.38/0.61              = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))))),
% 0.38/0.61      inference('sup-', [status(thm)], ['148', '165'])).
% 0.38/0.61  thf('167', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.38/0.61            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 0.38/0.61          | ~ (v2_funct_1 @ X0)
% 0.38/0.61          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.61          | ~ (v1_funct_1 @ X0)
% 0.38/0.61          | ~ (v1_relat_1 @ X0))),
% 0.38/0.61      inference('simplify', [status(thm)], ['166'])).
% 0.38/0.61  thf('168', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (~ (v1_relat_1 @ X0)
% 0.38/0.61          | ~ (v1_funct_1 @ X0)
% 0.38/0.61          | ~ (v2_funct_1 @ X0)
% 0.38/0.61          | ~ (v1_relat_1 @ X0)
% 0.38/0.61          | ~ (v1_funct_1 @ X0)
% 0.38/0.61          | ~ (v2_funct_1 @ X0)
% 0.38/0.61          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.38/0.61              = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))))),
% 0.38/0.61      inference('sup-', [status(thm)], ['147', '167'])).
% 0.38/0.61  thf('169', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.38/0.61            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 0.38/0.61          | ~ (v2_funct_1 @ X0)
% 0.38/0.61          | ~ (v1_funct_1 @ X0)
% 0.38/0.61          | ~ (v1_relat_1 @ X0))),
% 0.38/0.61      inference('simplify', [status(thm)], ['168'])).
% 0.38/0.61  thf('170', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.38/0.61            = (k6_relat_1 @ 
% 0.38/0.61               (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))))
% 0.38/0.61          | ~ (v1_relat_1 @ X0)
% 0.38/0.61          | ~ (v1_funct_1 @ X0)
% 0.38/0.61          | ~ (v2_funct_1 @ X0)
% 0.38/0.61          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.38/0.61          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.38/0.61          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.38/0.61      inference('sup+', [status(thm)], ['146', '169'])).
% 0.38/0.61  thf('171', plain,
% 0.38/0.61      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.38/0.61        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.38/0.61        | ~ (v2_funct_1 @ sk_C)
% 0.38/0.61        | ~ (v1_funct_1 @ sk_C)
% 0.38/0.61        | ~ (v1_relat_1 @ sk_C)
% 0.38/0.61        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.38/0.61            = (k6_relat_1 @ 
% 0.38/0.61               (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))))),
% 0.38/0.61      inference('sup-', [status(thm)], ['145', '170'])).
% 0.38/0.61  thf('172', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.38/0.61      inference('simplify', [status(thm)], ['106'])).
% 0.38/0.61  thf('173', plain, ((v2_funct_1 @ sk_C)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('174', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('175', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.61      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.61  thf('176', plain,
% 0.38/0.61      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.38/0.61        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.38/0.61            = (k6_relat_1 @ 
% 0.38/0.61               (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))))),
% 0.38/0.61      inference('demod', [status(thm)], ['171', '172', '173', '174', '175'])).
% 0.38/0.61  thf('177', plain,
% 0.38/0.61      ((~ (v1_relat_1 @ sk_C)
% 0.38/0.61        | ~ (v1_funct_1 @ sk_C)
% 0.38/0.61        | ~ (v2_funct_1 @ sk_C)
% 0.38/0.61        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.38/0.61            = (k6_relat_1 @ 
% 0.38/0.61               (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))))),
% 0.38/0.61      inference('sup-', [status(thm)], ['142', '176'])).
% 0.38/0.61  thf('178', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.61      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.61  thf('179', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('180', plain, ((v2_funct_1 @ sk_C)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('181', plain,
% 0.38/0.61      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.38/0.61         = (k6_relat_1 @ 
% 0.38/0.61            (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))))),
% 0.38/0.61      inference('demod', [status(thm)], ['177', '178', '179', '180'])).
% 0.38/0.61  thf('182', plain,
% 0.38/0.61      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.38/0.61          = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))
% 0.38/0.61        | ~ (v1_relat_1 @ sk_C)
% 0.38/0.61        | ~ (v1_funct_1 @ sk_C)
% 0.38/0.61        | ~ (v2_funct_1 @ sk_C))),
% 0.38/0.61      inference('sup+', [status(thm)], ['141', '181'])).
% 0.38/0.61  thf('183', plain,
% 0.38/0.61      (![X2 : $i]:
% 0.38/0.61         (~ (v2_funct_1 @ X2)
% 0.38/0.61          | ((k2_relat_1 @ X2) = (k1_relat_1 @ (k2_funct_1 @ X2)))
% 0.38/0.61          | ~ (v1_funct_1 @ X2)
% 0.38/0.61          | ~ (v1_relat_1 @ X2))),
% 0.38/0.61      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.38/0.61  thf('184', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_C @ 
% 0.38/0.61        (k1_zfmisc_1 @ 
% 0.38/0.61         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('185', plain,
% 0.38/0.61      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.38/0.61         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 0.38/0.61          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.38/0.61      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.38/0.61  thf('186', plain,
% 0.38/0.61      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.38/0.61         = (k2_relat_1 @ sk_C))),
% 0.38/0.61      inference('sup-', [status(thm)], ['184', '185'])).
% 0.38/0.61  thf('187', plain,
% 0.38/0.61      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.38/0.61         = (k2_struct_0 @ sk_B))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('188', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.38/0.61      inference('sup+', [status(thm)], ['186', '187'])).
% 0.38/0.61  thf('189', plain,
% 0.38/0.61      (![X2 : $i]:
% 0.38/0.61         (~ (v2_funct_1 @ X2)
% 0.38/0.61          | ((k2_relat_1 @ X2) = (k1_relat_1 @ (k2_funct_1 @ X2)))
% 0.38/0.61          | ~ (v1_funct_1 @ X2)
% 0.38/0.61          | ~ (v1_relat_1 @ X2))),
% 0.38/0.61      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.38/0.61  thf('190', plain,
% 0.38/0.61      (![X18 : $i, X19 : $i]:
% 0.38/0.61         (((k1_relat_1 @ X19) != (X18))
% 0.38/0.61          | (v1_partfun1 @ X19 @ X18)
% 0.38/0.61          | ~ (v4_relat_1 @ X19 @ X18)
% 0.38/0.61          | ~ (v1_relat_1 @ X19))),
% 0.38/0.61      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.38/0.61  thf('191', plain,
% 0.38/0.61      (![X19 : $i]:
% 0.38/0.61         (~ (v1_relat_1 @ X19)
% 0.38/0.61          | ~ (v4_relat_1 @ X19 @ (k1_relat_1 @ X19))
% 0.38/0.61          | (v1_partfun1 @ X19 @ (k1_relat_1 @ X19)))),
% 0.38/0.61      inference('simplify', [status(thm)], ['190'])).
% 0.38/0.61  thf('192', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (~ (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.38/0.61          | ~ (v1_relat_1 @ X0)
% 0.38/0.61          | ~ (v1_funct_1 @ X0)
% 0.38/0.61          | ~ (v2_funct_1 @ X0)
% 0.38/0.61          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.38/0.61          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['189', '191'])).
% 0.38/0.61  thf('193', plain,
% 0.38/0.61      ((~ (v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 0.38/0.61        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.38/0.61        | (v1_partfun1 @ (k2_funct_1 @ sk_C) @ 
% 0.38/0.61           (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.38/0.61        | ~ (v2_funct_1 @ sk_C)
% 0.38/0.61        | ~ (v1_funct_1 @ sk_C)
% 0.38/0.61        | ~ (v1_relat_1 @ sk_C))),
% 0.38/0.61      inference('sup-', [status(thm)], ['188', '192'])).
% 0.38/0.61  thf('194', plain, ((v2_funct_1 @ sk_C)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('195', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('196', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.61      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.61  thf('197', plain,
% 0.38/0.61      ((~ (v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 0.38/0.61        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.38/0.61        | (v1_partfun1 @ (k2_funct_1 @ sk_C) @ 
% 0.38/0.61           (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.38/0.61      inference('demod', [status(thm)], ['193', '194', '195', '196'])).
% 0.38/0.61  thf('198', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.38/0.61      inference('sup-', [status(thm)], ['143', '144'])).
% 0.38/0.61  thf('199', plain,
% 0.38/0.61      ((~ (v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 0.38/0.61        | (v1_partfun1 @ (k2_funct_1 @ sk_C) @ 
% 0.38/0.61           (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.38/0.61      inference('demod', [status(thm)], ['197', '198'])).
% 0.38/0.61  thf('200', plain,
% 0.38/0.61      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.38/0.61        (k1_zfmisc_1 @ 
% 0.38/0.61         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.38/0.61      inference('simplify', [status(thm)], ['95'])).
% 0.38/0.61  thf('201', plain,
% 0.38/0.61      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.38/0.61         ((v4_relat_1 @ X9 @ X10)
% 0.38/0.61          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.38/0.61      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.38/0.61  thf('202', plain,
% 0.38/0.61      ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))),
% 0.38/0.61      inference('sup-', [status(thm)], ['200', '201'])).
% 0.38/0.61  thf('203', plain,
% 0.38/0.61      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.38/0.61      inference('demod', [status(thm)], ['199', '202'])).
% 0.38/0.61  thf('204', plain,
% 0.38/0.61      (((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.38/0.61        | ~ (v1_relat_1 @ sk_C)
% 0.38/0.61        | ~ (v1_funct_1 @ sk_C)
% 0.38/0.61        | ~ (v2_funct_1 @ sk_C))),
% 0.38/0.61      inference('sup+', [status(thm)], ['183', '203'])).
% 0.38/0.61  thf('205', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.38/0.61      inference('sup+', [status(thm)], ['186', '187'])).
% 0.38/0.61  thf('206', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.61      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.61  thf('207', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('208', plain, ((v2_funct_1 @ sk_C)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('209', plain,
% 0.38/0.61      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))),
% 0.38/0.61      inference('demod', [status(thm)], ['204', '205', '206', '207', '208'])).
% 0.38/0.61  thf('210', plain,
% 0.38/0.61      (![X18 : $i, X19 : $i]:
% 0.38/0.61         (~ (v1_partfun1 @ X19 @ X18)
% 0.38/0.61          | ((k1_relat_1 @ X19) = (X18))
% 0.38/0.61          | ~ (v4_relat_1 @ X19 @ X18)
% 0.38/0.61          | ~ (v1_relat_1 @ X19))),
% 0.38/0.61      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.38/0.61  thf('211', plain,
% 0.38/0.61      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.38/0.61        | ~ (v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 0.38/0.61        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['209', '210'])).
% 0.38/0.61  thf('212', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.38/0.61      inference('sup-', [status(thm)], ['143', '144'])).
% 0.38/0.61  thf('213', plain,
% 0.38/0.61      ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))),
% 0.38/0.61      inference('sup-', [status(thm)], ['200', '201'])).
% 0.38/0.61  thf('214', plain,
% 0.38/0.61      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B))),
% 0.38/0.61      inference('demod', [status(thm)], ['211', '212', '213'])).
% 0.38/0.61  thf('215', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.61      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.61  thf('216', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('217', plain, ((v2_funct_1 @ sk_C)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('218', plain,
% 0.38/0.61      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.38/0.61         = (k6_relat_1 @ (k2_struct_0 @ sk_B)))),
% 0.38/0.61      inference('demod', [status(thm)], ['182', '214', '215', '216', '217'])).
% 0.38/0.61  thf('219', plain,
% 0.38/0.61      (![X4 : $i, X5 : $i]:
% 0.38/0.61         (~ (v1_relat_1 @ X4)
% 0.38/0.61          | ~ (v1_funct_1 @ X4)
% 0.38/0.61          | ((X4) = (k2_funct_1 @ X5))
% 0.38/0.61          | ((k5_relat_1 @ X5 @ X4) != (k6_relat_1 @ (k1_relat_1 @ X5)))
% 0.38/0.61          | ((k2_relat_1 @ X5) != (k1_relat_1 @ X4))
% 0.38/0.61          | ~ (v2_funct_1 @ X5)
% 0.38/0.61          | ~ (v1_funct_1 @ X5)
% 0.38/0.61          | ~ (v1_relat_1 @ X5))),
% 0.38/0.61      inference('cnf', [status(esa)], [t63_funct_1])).
% 0.38/0.61  thf('220', plain,
% 0.38/0.61      ((((k6_relat_1 @ (k2_struct_0 @ sk_B))
% 0.38/0.61          != (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))
% 0.38/0.61        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.38/0.61        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.38/0.61        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.38/0.61        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 0.38/0.61        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.38/0.61        | ~ (v1_funct_1 @ sk_C)
% 0.38/0.61        | ~ (v1_relat_1 @ sk_C))),
% 0.38/0.61      inference('sup-', [status(thm)], ['218', '219'])).
% 0.38/0.61  thf('221', plain,
% 0.38/0.61      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B))),
% 0.38/0.61      inference('demod', [status(thm)], ['211', '212', '213'])).
% 0.38/0.61  thf('222', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.38/0.61      inference('sup-', [status(thm)], ['143', '144'])).
% 0.38/0.61  thf('223', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.38/0.61      inference('simplify', [status(thm)], ['106'])).
% 0.38/0.61  thf('224', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.38/0.61      inference('clc', [status(thm)], ['48', '49'])).
% 0.38/0.61  thf('225', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('226', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.61      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.61  thf('227', plain,
% 0.38/0.61      ((((k6_relat_1 @ (k2_struct_0 @ sk_B))
% 0.38/0.61          != (k6_relat_1 @ (k2_struct_0 @ sk_B)))
% 0.38/0.61        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.38/0.61        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 0.38/0.61        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.38/0.61      inference('demod', [status(thm)],
% 0.38/0.61                ['220', '221', '222', '223', '224', '225', '226'])).
% 0.38/0.61  thf('228', plain,
% 0.38/0.61      ((((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.38/0.61        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 0.38/0.61        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.38/0.61      inference('simplify', [status(thm)], ['227'])).
% 0.38/0.61  thf('229', plain,
% 0.38/0.61      ((~ (v1_relat_1 @ sk_C)
% 0.38/0.61        | ~ (v1_funct_1 @ sk_C)
% 0.38/0.61        | ~ (v2_funct_1 @ sk_C)
% 0.38/0.61        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 0.38/0.61        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.38/0.61      inference('sup-', [status(thm)], ['122', '228'])).
% 0.38/0.61  thf('230', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.61      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.61  thf('231', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('232', plain, ((v2_funct_1 @ sk_C)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('233', plain,
% 0.38/0.61      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 0.38/0.61        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.38/0.61      inference('demod', [status(thm)], ['229', '230', '231', '232'])).
% 0.38/0.61  thf('234', plain,
% 0.38/0.61      ((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))
% 0.38/0.61        | ~ (v1_relat_1 @ sk_C)
% 0.38/0.61        | ~ (v1_funct_1 @ sk_C)
% 0.38/0.61        | ~ (v2_funct_1 @ sk_C)
% 0.38/0.61        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.38/0.61      inference('sup-', [status(thm)], ['121', '233'])).
% 0.38/0.61  thf('235', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.38/0.61      inference('clc', [status(thm)], ['48', '49'])).
% 0.38/0.61  thf('236', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.61      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.61  thf('237', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('238', plain, ((v2_funct_1 @ sk_C)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('239', plain,
% 0.38/0.61      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.38/0.61        | ((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.38/0.61      inference('demod', [status(thm)], ['234', '235', '236', '237', '238'])).
% 0.38/0.61  thf('240', plain, (((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.38/0.61      inference('simplify', [status(thm)], ['239'])).
% 0.38/0.61  thf('241', plain,
% 0.38/0.61      (![X1 : $i]:
% 0.38/0.61         ((v2_funct_1 @ (k2_funct_1 @ X1))
% 0.38/0.61          | ~ (v2_funct_1 @ X1)
% 0.38/0.61          | ~ (v1_funct_1 @ X1)
% 0.38/0.61          | ~ (v1_relat_1 @ X1))),
% 0.38/0.61      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.38/0.61  thf('242', plain, (((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.38/0.61      inference('simplify', [status(thm)], ['239'])).
% 0.38/0.61  thf('243', plain,
% 0.38/0.61      (![X2 : $i]:
% 0.38/0.61         (~ (v2_funct_1 @ X2)
% 0.38/0.61          | ((k2_relat_1 @ X2) = (k1_relat_1 @ (k2_funct_1 @ X2)))
% 0.38/0.61          | ~ (v1_funct_1 @ X2)
% 0.38/0.61          | ~ (v1_relat_1 @ X2))),
% 0.38/0.61      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.38/0.61  thf('244', plain,
% 0.38/0.61      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))
% 0.38/0.61        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.38/0.61        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.38/0.61        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.38/0.61      inference('sup+', [status(thm)], ['242', '243'])).
% 0.38/0.61  thf('245', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.38/0.61      inference('clc', [status(thm)], ['48', '49'])).
% 0.38/0.61  thf('246', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.38/0.61      inference('sup-', [status(thm)], ['143', '144'])).
% 0.38/0.61  thf('247', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.38/0.61      inference('simplify', [status(thm)], ['106'])).
% 0.38/0.61  thf('248', plain,
% 0.38/0.61      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))
% 0.38/0.61        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.38/0.61      inference('demod', [status(thm)], ['244', '245', '246', '247'])).
% 0.38/0.61  thf('249', plain,
% 0.38/0.61      ((~ (v1_relat_1 @ sk_C)
% 0.38/0.61        | ~ (v1_funct_1 @ sk_C)
% 0.38/0.61        | ~ (v2_funct_1 @ sk_C)
% 0.38/0.61        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['241', '248'])).
% 0.38/0.61  thf('250', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.61      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.61  thf('251', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('252', plain, ((v2_funct_1 @ sk_C)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('253', plain,
% 0.38/0.61      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.38/0.61      inference('demod', [status(thm)], ['249', '250', '251', '252'])).
% 0.38/0.61  thf('254', plain,
% 0.38/0.61      ((((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.61          (k2_funct_1 @ sk_C)) = (sk_C))
% 0.38/0.61        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.38/0.61        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)))),
% 0.38/0.61      inference('demod', [status(thm)], ['120', '240', '253'])).
% 0.38/0.61  thf('255', plain,
% 0.38/0.61      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.38/0.61        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.61            (k2_funct_1 @ sk_C)) = (sk_C)))),
% 0.38/0.61      inference('simplify', [status(thm)], ['254'])).
% 0.38/0.61  thf('256', plain,
% 0.38/0.61      ((~ (v1_relat_1 @ sk_C)
% 0.38/0.61        | ~ (v1_funct_1 @ sk_C)
% 0.38/0.61        | ~ (v2_funct_1 @ sk_C)
% 0.38/0.61        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.61            (k2_funct_1 @ sk_C)) = (sk_C)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['87', '255'])).
% 0.38/0.61  thf('257', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.61      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.61  thf('258', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('259', plain, ((v2_funct_1 @ sk_C)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('260', plain,
% 0.38/0.61      (((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.38/0.61         (k2_funct_1 @ sk_C)) = (sk_C))),
% 0.38/0.61      inference('demod', [status(thm)], ['256', '257', '258', '259'])).
% 0.38/0.61  thf('261', plain,
% 0.38/0.61      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.38/0.61          sk_C)),
% 0.38/0.61      inference('demod', [status(thm)], ['86', '260'])).
% 0.38/0.61  thf('262', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_C @ 
% 0.38/0.61        (k1_zfmisc_1 @ 
% 0.38/0.61         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.61      inference('demod', [status(thm)], ['26', '27'])).
% 0.38/0.61  thf('263', plain,
% 0.38/0.61      ((m1_subset_1 @ sk_C @ 
% 0.38/0.61        (k1_zfmisc_1 @ 
% 0.38/0.61         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.61      inference('demod', [status(thm)], ['26', '27'])).
% 0.38/0.61  thf(reflexivity_r2_funct_2, axiom,
% 0.38/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.61     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.38/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.38/0.61         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.38/0.61         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.61       ( r2_funct_2 @ A @ B @ C @ C ) ))).
% 0.38/0.61  thf('264', plain,
% 0.38/0.61      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.38/0.61         ((r2_funct_2 @ X20 @ X21 @ X22 @ X22)
% 0.38/0.61          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.38/0.61          | ~ (v1_funct_2 @ X22 @ X20 @ X21)
% 0.38/0.61          | ~ (v1_funct_1 @ X22)
% 0.38/0.61          | ~ (v1_funct_1 @ X23)
% 0.38/0.61          | ~ (v1_funct_2 @ X23 @ X20 @ X21)
% 0.38/0.61          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.38/0.61      inference('cnf', [status(esa)], [reflexivity_r2_funct_2])).
% 0.38/0.61  thf('265', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X0 @ 
% 0.38/0.61             (k1_zfmisc_1 @ 
% 0.38/0.61              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.38/0.61          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.38/0.61          | ~ (v1_funct_1 @ X0)
% 0.38/0.61          | ~ (v1_funct_1 @ sk_C)
% 0.38/0.61          | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.38/0.61          | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.38/0.61             sk_C))),
% 0.38/0.61      inference('sup-', [status(thm)], ['263', '264'])).
% 0.38/0.61  thf('266', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('267', plain,
% 0.38/0.61      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.38/0.61      inference('demod', [status(thm)], ['34', '35'])).
% 0.38/0.61  thf('268', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (~ (m1_subset_1 @ X0 @ 
% 0.38/0.61             (k1_zfmisc_1 @ 
% 0.38/0.61              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.38/0.61          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.38/0.61          | ~ (v1_funct_1 @ X0)
% 0.38/0.61          | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.38/0.61             sk_C))),
% 0.38/0.61      inference('demod', [status(thm)], ['265', '266', '267'])).
% 0.38/0.61  thf('269', plain,
% 0.38/0.61      (((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)
% 0.38/0.61        | ~ (v1_funct_1 @ sk_C)
% 0.38/0.61        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['262', '268'])).
% 0.38/0.61  thf('270', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.61  thf('271', plain,
% 0.38/0.61      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.38/0.61      inference('demod', [status(thm)], ['34', '35'])).
% 0.38/0.61  thf('272', plain,
% 0.38/0.61      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.38/0.61      inference('demod', [status(thm)], ['269', '270', '271'])).
% 0.38/0.61  thf('273', plain, ($false), inference('demod', [status(thm)], ['261', '272'])).
% 0.38/0.61  
% 0.38/0.61  % SZS output end Refutation
% 0.38/0.61  
% 0.38/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
