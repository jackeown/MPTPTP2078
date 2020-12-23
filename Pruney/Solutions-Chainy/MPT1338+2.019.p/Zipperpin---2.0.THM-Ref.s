%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.L5D7XCzVS7

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:49 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :  334 (8983 expanded)
%              Number of leaves         :   51 (2566 expanded)
%              Depth                    :   35
%              Number of atoms          : 3403 (221503 expanded)
%              Number of equality atoms :  214 (11289 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t62_tops_2,conjecture,(
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
               => ( ( ( k1_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                    = ( k2_struct_0 @ B ) )
                  & ( ( k2_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                    = ( k2_struct_0 @ A ) ) ) ) ) ) ) )).

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
                 => ( ( ( k1_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                      = ( k2_struct_0 @ B ) )
                    & ( ( k2_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                      = ( k2_struct_0 @ A ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_tops_2])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['0','5'])).

thf('7',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('10',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('11',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('16',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('23',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( v1_partfun1 @ X27 @ X28 )
      | ~ ( v1_funct_2 @ X27 @ X28 @ X29 )
      | ~ ( v1_funct_1 @ X27 )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('24',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('27',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('32',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25','32'])).

thf('34',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('35',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('36',plain,(
    ! [X36: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['34','38'])).

thf('40',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['33','43'])).

thf('45',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['15','44'])).

thf('46',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['45','46'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('48',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v1_partfun1 @ X31 @ X30 )
      | ( ( k1_relat_1 @ X31 )
        = X30 )
      | ~ ( v4_relat_1 @ X31 @ X30 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('51',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('52',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('54',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v4_relat_1 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('55',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['49','52','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['14','56'])).

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

thf('58',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v2_funct_1 @ X32 )
      | ( ( k2_relset_1 @ X34 @ X33 @ X32 )
       != X33 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X34 @ X33 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('59',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('62',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('63',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['61','66'])).

thf('68',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('71',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['49','52','55'])).

thf('73',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('75',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('76',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['74','79'])).

thf('81',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('84',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('85',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['49','52','55'])).

thf('87',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['59','60','73','87','88'])).

thf('90',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('91',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k8_relset_1 @ X24 @ X25 @ X26 @ X25 )
        = ( k1_relset_1 @ X24 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('92',plain,
    ( ( k8_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    = ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('94',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( ( k8_relset_1 @ X21 @ X22 @ X20 @ X23 )
        = ( k10_relat_1 @ X20 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k8_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) @ X0 )
      = ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    = ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['92','95'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('97',plain,(
    ! [X5: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v2_funct_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('98',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('99',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('100',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X10 ) )
        = X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('101',plain,(
    ! [X5: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v2_funct_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('102',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('103',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('104',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X10 ) )
        = X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('105',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X9 ) @ X9 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
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
    inference('sup-',[status(thm)],['103','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['102','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['101','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf(t58_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('113',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X8 @ ( k2_funct_1 @ X8 ) ) )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('115',plain,(
    ! [X3: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X3 ) )
      = X3 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['100','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['99','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['98','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['97','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t155_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ B @ A )
          = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('126',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k10_relat_1 @ X6 @ X7 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X6 ) @ X7 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('127',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['125','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['124','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('134',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('135',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v4_relat_1 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('136',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('138',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k1_relat_1 @ X31 )
       != X30 )
      | ( v1_partfun1 @ X31 @ X30 )
      | ~ ( v4_relat_1 @ X31 @ X30 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('139',plain,(
    ! [X31: $i] :
      ( ~ ( v1_relat_1 @ X31 )
      | ~ ( v4_relat_1 @ X31 @ ( k1_relat_1 @ X31 ) )
      | ( v1_partfun1 @ X31 @ ( k1_relat_1 @ X31 ) ) ) ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['137','139'])).

thf('141',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['136','140'])).

thf('142',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('143',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('144',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['50','51'])).

thf('148',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['141','144','145','146','147'])).

thf('149',plain,
    ( ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['133','148'])).

thf('150',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['50','51'])).

thf('151',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['149','150','151','152'])).

thf('154',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v1_partfun1 @ X31 @ X30 )
      | ( ( k1_relat_1 @ X31 )
        = X30 )
      | ~ ( v4_relat_1 @ X31 @ X30 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('155',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('157',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('158',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['155','156','157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('160',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('161',plain,(
    ! [X5: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v2_funct_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('162',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('163',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('164',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X10 ) )
        = X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('165',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k10_relat_1 @ X6 @ X7 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X6 ) @ X7 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
        = ( k9_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['163','166'])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['167'])).

thf('169',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
        = ( k9_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['162','168'])).

thf('170',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['169'])).

thf('171',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
        = ( k9_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['161','170'])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 )
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['171'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('173',plain,(
    ! [X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ ( k2_relat_1 @ X1 ) )
        = ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('174',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['172','173'])).

thf('175',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['160','174'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['175'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['159','176'])).

thf('178',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['177'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['177'])).

thf('181',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['129'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['180','181'])).

thf('183',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['182'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['179','183'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['184'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['178','185'])).

thf('187',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['186'])).

thf('188',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['158','187'])).

thf('189',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['50','51'])).

thf('190',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['188','189','190','191'])).

thf('193',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['132','192'])).

thf('194',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['50','51'])).

thf('195',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['193','194','195','196'])).

thf('198',plain,(
    ! [X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ ( k2_relat_1 @ X1 ) )
        = ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('199',plain,
    ( ( ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['197','198'])).

thf('200',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['155','156','157'])).

thf('201',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('202',plain,
    ( ( k10_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['199','200','201'])).

thf('203',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['96','202'])).

thf('204',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('205',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['205'])).

thf('207',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['204','206'])).

thf('208',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['207','208'])).

thf('210',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('211',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['33','43'])).

thf('212',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v1_partfun1 @ X31 @ X30 )
      | ( ( k1_relat_1 @ X31 )
        = X30 )
      | ~ ( v4_relat_1 @ X31 @ X30 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('213',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['50','51'])).

thf('215',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v4_relat_1 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('217',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['215','216'])).

thf('218',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['213','214','217'])).

thf('219',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['213','214','217'])).

thf('220',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('221',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('222',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['49','52','55'])).

thf('223',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['221','222'])).

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

thf('224',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k2_relset_1 @ X38 @ X37 @ X39 )
       != X37 )
      | ~ ( v2_funct_1 @ X39 )
      | ( ( k2_tops_2 @ X38 @ X37 @ X39 )
        = ( k2_funct_1 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X39 @ X38 @ X37 )
      | ~ ( v1_funct_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('225',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['223','224'])).

thf('226',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('228',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['49','52','55'])).

thf('229',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['227','228'])).

thf('230',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('232',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('233',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['231','232'])).

thf('234',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['49','52','55'])).

thf('235',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['233','234'])).

thf('236',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['225','226','229','230','235'])).

thf('237',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['220','236'])).

thf('238',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('239',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['237','238','239'])).

thf('241',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['240'])).

thf('242',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('243',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['209','210','218','219','241','242'])).

thf('244',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('245',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('246',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['244','245'])).

thf('247',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['193','194','195','196'])).

thf('248',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['246','247'])).

thf('249',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['14','56'])).

thf('250',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k2_relset_1 @ X38 @ X37 @ X39 )
       != X37 )
      | ~ ( v2_funct_1 @ X39 )
      | ( ( k2_tops_2 @ X38 @ X37 @ X39 )
        = ( k2_funct_1 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X39 @ X38 @ X37 )
      | ~ ( v1_funct_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('251',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['249','250'])).

thf('252',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('253',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('254',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('255',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('256',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['251','252','253','254','255'])).

thf('257',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['256'])).

thf('258',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('259',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('260',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('261',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['205'])).

thf('262',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['260','261'])).

thf('263',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['262','263'])).

thf('265',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['259','264'])).

thf('266',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('267',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['265','266'])).

thf('268',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['258','267'])).

thf('269',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('270',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['268','269'])).

thf('271',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['213','214','217'])).

thf('272',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['213','214','217'])).

thf('273',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['49','52','55'])).

thf('274',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['270','271','272','273'])).

thf('275',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['257','274'])).

thf('276',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['248','275'])).

thf('277',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['276'])).

thf('278',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['205'])).

thf('279',plain,(
    ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['277','278'])).

thf('280',plain,(
    ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
 != ( k2_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['243','279'])).

thf('281',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['203','280'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.L5D7XCzVS7
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:58:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.47/0.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.71  % Solved by: fo/fo7.sh
% 0.47/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.71  % done 635 iterations in 0.241s
% 0.47/0.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.71  % SZS output start Refutation
% 0.47/0.71  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.47/0.71  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.47/0.71  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.47/0.71  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.47/0.71  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.47/0.71  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.47/0.71  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.47/0.71  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.47/0.71  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.47/0.71  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.71  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.47/0.71  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.47/0.71  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.71  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.47/0.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.71  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.47/0.71  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.47/0.71  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.47/0.71  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.71  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.47/0.71  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.71  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.47/0.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.71  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.47/0.71  thf(sk_C_type, type, sk_C: $i).
% 0.47/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.71  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.47/0.71  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.47/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.71  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.47/0.71  thf(d3_struct_0, axiom,
% 0.47/0.71    (![A:$i]:
% 0.47/0.71     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.47/0.71  thf('0', plain,
% 0.47/0.71      (![X35 : $i]:
% 0.47/0.71         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.47/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.71  thf('1', plain,
% 0.47/0.71      (![X35 : $i]:
% 0.47/0.71         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.47/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.71  thf(t62_tops_2, conjecture,
% 0.47/0.71    (![A:$i]:
% 0.47/0.71     ( ( l1_struct_0 @ A ) =>
% 0.47/0.71       ( ![B:$i]:
% 0.47/0.71         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.47/0.71           ( ![C:$i]:
% 0.47/0.71             ( ( ( v1_funct_1 @ C ) & 
% 0.47/0.71                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.47/0.71                 ( m1_subset_1 @
% 0.47/0.71                   C @ 
% 0.47/0.71                   ( k1_zfmisc_1 @
% 0.47/0.71                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.47/0.71               ( ( ( ( k2_relset_1 @
% 0.47/0.71                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.47/0.71                     ( k2_struct_0 @ B ) ) & 
% 0.47/0.71                   ( v2_funct_1 @ C ) ) =>
% 0.47/0.71                 ( ( ( k1_relset_1 @
% 0.47/0.71                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.47/0.71                       ( k2_tops_2 @
% 0.47/0.71                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.47/0.71                     ( k2_struct_0 @ B ) ) & 
% 0.47/0.71                   ( ( k2_relset_1 @
% 0.47/0.71                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.47/0.71                       ( k2_tops_2 @
% 0.47/0.71                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.47/0.71                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.47/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.71    (~( ![A:$i]:
% 0.47/0.71        ( ( l1_struct_0 @ A ) =>
% 0.47/0.71          ( ![B:$i]:
% 0.47/0.71            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.47/0.71              ( ![C:$i]:
% 0.47/0.71                ( ( ( v1_funct_1 @ C ) & 
% 0.47/0.71                    ( v1_funct_2 @
% 0.47/0.71                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.47/0.71                    ( m1_subset_1 @
% 0.47/0.71                      C @ 
% 0.47/0.71                      ( k1_zfmisc_1 @
% 0.47/0.71                        ( k2_zfmisc_1 @
% 0.47/0.71                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.47/0.71                  ( ( ( ( k2_relset_1 @
% 0.47/0.71                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.47/0.71                        ( k2_struct_0 @ B ) ) & 
% 0.47/0.71                      ( v2_funct_1 @ C ) ) =>
% 0.47/0.71                    ( ( ( k1_relset_1 @
% 0.47/0.71                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.47/0.71                          ( k2_tops_2 @
% 0.47/0.71                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.47/0.71                        ( k2_struct_0 @ B ) ) & 
% 0.47/0.71                      ( ( k2_relset_1 @
% 0.47/0.71                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.47/0.71                          ( k2_tops_2 @
% 0.47/0.71                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.47/0.71                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.47/0.71    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 0.47/0.71  thf('2', plain,
% 0.47/0.71      ((m1_subset_1 @ sk_C @ 
% 0.47/0.71        (k1_zfmisc_1 @ 
% 0.47/0.71         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('3', plain,
% 0.47/0.71      (((m1_subset_1 @ sk_C @ 
% 0.47/0.71         (k1_zfmisc_1 @ 
% 0.47/0.71          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.47/0.71        | ~ (l1_struct_0 @ sk_A))),
% 0.47/0.71      inference('sup+', [status(thm)], ['1', '2'])).
% 0.47/0.71  thf('4', plain, ((l1_struct_0 @ sk_A)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('5', plain,
% 0.47/0.71      ((m1_subset_1 @ sk_C @ 
% 0.47/0.71        (k1_zfmisc_1 @ 
% 0.47/0.71         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.71      inference('demod', [status(thm)], ['3', '4'])).
% 0.47/0.71  thf('6', plain,
% 0.47/0.71      (((m1_subset_1 @ sk_C @ 
% 0.47/0.71         (k1_zfmisc_1 @ 
% 0.47/0.71          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.47/0.71        | ~ (l1_struct_0 @ sk_B))),
% 0.47/0.71      inference('sup+', [status(thm)], ['0', '5'])).
% 0.47/0.71  thf('7', plain, ((l1_struct_0 @ sk_B)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('8', plain,
% 0.47/0.71      ((m1_subset_1 @ sk_C @ 
% 0.47/0.71        (k1_zfmisc_1 @ 
% 0.47/0.71         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.47/0.71      inference('demod', [status(thm)], ['6', '7'])).
% 0.47/0.71  thf('9', plain,
% 0.47/0.71      ((m1_subset_1 @ sk_C @ 
% 0.47/0.71        (k1_zfmisc_1 @ 
% 0.47/0.71         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf(redefinition_k2_relset_1, axiom,
% 0.47/0.71    (![A:$i,B:$i,C:$i]:
% 0.47/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.71       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.47/0.71  thf('10', plain,
% 0.47/0.71      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.47/0.71         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 0.47/0.71          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.47/0.71      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.47/0.71  thf('11', plain,
% 0.47/0.71      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.47/0.71         = (k2_relat_1 @ sk_C))),
% 0.47/0.71      inference('sup-', [status(thm)], ['9', '10'])).
% 0.47/0.71  thf('12', plain,
% 0.47/0.71      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.47/0.71         = (k2_struct_0 @ sk_B))),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('13', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.47/0.71      inference('sup+', [status(thm)], ['11', '12'])).
% 0.47/0.71  thf('14', plain,
% 0.47/0.71      ((m1_subset_1 @ sk_C @ 
% 0.47/0.71        (k1_zfmisc_1 @ 
% 0.47/0.71         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.47/0.71      inference('demod', [status(thm)], ['8', '13'])).
% 0.47/0.71  thf('15', plain,
% 0.47/0.71      (![X35 : $i]:
% 0.47/0.71         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.47/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.71  thf('16', plain,
% 0.47/0.71      (![X35 : $i]:
% 0.47/0.71         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.47/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.71  thf('17', plain,
% 0.47/0.71      ((m1_subset_1 @ sk_C @ 
% 0.47/0.71        (k1_zfmisc_1 @ 
% 0.47/0.71         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('18', plain,
% 0.47/0.71      (((m1_subset_1 @ sk_C @ 
% 0.47/0.71         (k1_zfmisc_1 @ 
% 0.47/0.71          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.47/0.71        | ~ (l1_struct_0 @ sk_B))),
% 0.47/0.71      inference('sup+', [status(thm)], ['16', '17'])).
% 0.47/0.71  thf('19', plain, ((l1_struct_0 @ sk_B)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('20', plain,
% 0.47/0.71      ((m1_subset_1 @ sk_C @ 
% 0.47/0.71        (k1_zfmisc_1 @ 
% 0.47/0.71         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.47/0.71      inference('demod', [status(thm)], ['18', '19'])).
% 0.47/0.71  thf('21', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.47/0.71      inference('sup+', [status(thm)], ['11', '12'])).
% 0.47/0.71  thf('22', plain,
% 0.47/0.71      ((m1_subset_1 @ sk_C @ 
% 0.47/0.71        (k1_zfmisc_1 @ 
% 0.47/0.71         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.47/0.71      inference('demod', [status(thm)], ['20', '21'])).
% 0.47/0.71  thf(cc5_funct_2, axiom,
% 0.47/0.71    (![A:$i,B:$i]:
% 0.47/0.71     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.47/0.71       ( ![C:$i]:
% 0.47/0.71         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.71           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.47/0.71             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.47/0.71  thf('23', plain,
% 0.47/0.71      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.47/0.71         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.47/0.71          | (v1_partfun1 @ X27 @ X28)
% 0.47/0.71          | ~ (v1_funct_2 @ X27 @ X28 @ X29)
% 0.47/0.71          | ~ (v1_funct_1 @ X27)
% 0.47/0.71          | (v1_xboole_0 @ X29))),
% 0.47/0.71      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.47/0.71  thf('24', plain,
% 0.47/0.71      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.47/0.71        | ~ (v1_funct_1 @ sk_C)
% 0.47/0.71        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.47/0.71        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.47/0.71      inference('sup-', [status(thm)], ['22', '23'])).
% 0.47/0.71  thf('25', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('26', plain,
% 0.47/0.71      (![X35 : $i]:
% 0.47/0.71         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.47/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.71  thf('27', plain,
% 0.47/0.71      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('28', plain,
% 0.47/0.71      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.47/0.71        | ~ (l1_struct_0 @ sk_B))),
% 0.47/0.71      inference('sup+', [status(thm)], ['26', '27'])).
% 0.47/0.71  thf('29', plain, ((l1_struct_0 @ sk_B)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('30', plain,
% 0.47/0.71      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.47/0.71      inference('demod', [status(thm)], ['28', '29'])).
% 0.47/0.71  thf('31', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.47/0.71      inference('sup+', [status(thm)], ['11', '12'])).
% 0.47/0.71  thf('32', plain,
% 0.47/0.71      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.47/0.71      inference('demod', [status(thm)], ['30', '31'])).
% 0.47/0.71  thf('33', plain,
% 0.47/0.71      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.47/0.71        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.47/0.71      inference('demod', [status(thm)], ['24', '25', '32'])).
% 0.47/0.71  thf('34', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.47/0.71      inference('sup+', [status(thm)], ['11', '12'])).
% 0.47/0.71  thf('35', plain,
% 0.47/0.71      (![X35 : $i]:
% 0.47/0.71         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.47/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.71  thf(fc2_struct_0, axiom,
% 0.47/0.71    (![A:$i]:
% 0.47/0.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.47/0.71       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.47/0.71  thf('36', plain,
% 0.47/0.71      (![X36 : $i]:
% 0.47/0.71         (~ (v1_xboole_0 @ (u1_struct_0 @ X36))
% 0.47/0.71          | ~ (l1_struct_0 @ X36)
% 0.47/0.71          | (v2_struct_0 @ X36))),
% 0.47/0.71      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.47/0.71  thf('37', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.47/0.71          | ~ (l1_struct_0 @ X0)
% 0.47/0.71          | (v2_struct_0 @ X0)
% 0.47/0.71          | ~ (l1_struct_0 @ X0))),
% 0.47/0.71      inference('sup-', [status(thm)], ['35', '36'])).
% 0.47/0.71  thf('38', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         ((v2_struct_0 @ X0)
% 0.47/0.71          | ~ (l1_struct_0 @ X0)
% 0.47/0.71          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.47/0.71      inference('simplify', [status(thm)], ['37'])).
% 0.47/0.71  thf('39', plain,
% 0.47/0.71      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.47/0.71        | ~ (l1_struct_0 @ sk_B)
% 0.47/0.71        | (v2_struct_0 @ sk_B))),
% 0.47/0.71      inference('sup-', [status(thm)], ['34', '38'])).
% 0.47/0.71  thf('40', plain, ((l1_struct_0 @ sk_B)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('41', plain,
% 0.47/0.71      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.47/0.71      inference('demod', [status(thm)], ['39', '40'])).
% 0.47/0.71  thf('42', plain, (~ (v2_struct_0 @ sk_B)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('43', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.47/0.71      inference('clc', [status(thm)], ['41', '42'])).
% 0.47/0.71  thf('44', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.47/0.71      inference('clc', [status(thm)], ['33', '43'])).
% 0.47/0.71  thf('45', plain,
% 0.47/0.71      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.47/0.71      inference('sup+', [status(thm)], ['15', '44'])).
% 0.47/0.71  thf('46', plain, ((l1_struct_0 @ sk_A)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('47', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.47/0.71      inference('demod', [status(thm)], ['45', '46'])).
% 0.47/0.71  thf(d4_partfun1, axiom,
% 0.47/0.71    (![A:$i,B:$i]:
% 0.47/0.71     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.47/0.71       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.47/0.71  thf('48', plain,
% 0.47/0.71      (![X30 : $i, X31 : $i]:
% 0.47/0.71         (~ (v1_partfun1 @ X31 @ X30)
% 0.47/0.71          | ((k1_relat_1 @ X31) = (X30))
% 0.47/0.71          | ~ (v4_relat_1 @ X31 @ X30)
% 0.47/0.71          | ~ (v1_relat_1 @ X31))),
% 0.47/0.71      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.47/0.71  thf('49', plain,
% 0.47/0.71      ((~ (v1_relat_1 @ sk_C)
% 0.47/0.71        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.47/0.71        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.47/0.71      inference('sup-', [status(thm)], ['47', '48'])).
% 0.47/0.71  thf('50', plain,
% 0.47/0.71      ((m1_subset_1 @ sk_C @ 
% 0.47/0.71        (k1_zfmisc_1 @ 
% 0.47/0.71         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf(cc1_relset_1, axiom,
% 0.47/0.71    (![A:$i,B:$i,C:$i]:
% 0.47/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.71       ( v1_relat_1 @ C ) ))).
% 0.47/0.71  thf('51', plain,
% 0.47/0.71      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.47/0.71         ((v1_relat_1 @ X11)
% 0.47/0.71          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.47/0.71      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.47/0.71  thf('52', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.71      inference('sup-', [status(thm)], ['50', '51'])).
% 0.47/0.71  thf('53', plain,
% 0.47/0.71      ((m1_subset_1 @ sk_C @ 
% 0.47/0.71        (k1_zfmisc_1 @ 
% 0.47/0.71         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.71      inference('demod', [status(thm)], ['3', '4'])).
% 0.47/0.71  thf(cc2_relset_1, axiom,
% 0.47/0.71    (![A:$i,B:$i,C:$i]:
% 0.47/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.71       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.47/0.71  thf('54', plain,
% 0.47/0.71      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.47/0.71         ((v4_relat_1 @ X14 @ X15)
% 0.47/0.71          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.47/0.71      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.47/0.71  thf('55', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.47/0.71      inference('sup-', [status(thm)], ['53', '54'])).
% 0.47/0.71  thf('56', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.47/0.71      inference('demod', [status(thm)], ['49', '52', '55'])).
% 0.47/0.71  thf('57', plain,
% 0.47/0.71      ((m1_subset_1 @ sk_C @ 
% 0.47/0.71        (k1_zfmisc_1 @ 
% 0.47/0.71         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.47/0.71      inference('demod', [status(thm)], ['14', '56'])).
% 0.47/0.71  thf(t31_funct_2, axiom,
% 0.47/0.71    (![A:$i,B:$i,C:$i]:
% 0.47/0.71     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.47/0.71         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.71       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.47/0.71         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.47/0.71           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.47/0.71           ( m1_subset_1 @
% 0.47/0.71             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.47/0.71  thf('58', plain,
% 0.47/0.71      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.47/0.71         (~ (v2_funct_1 @ X32)
% 0.47/0.71          | ((k2_relset_1 @ X34 @ X33 @ X32) != (X33))
% 0.47/0.71          | (m1_subset_1 @ (k2_funct_1 @ X32) @ 
% 0.47/0.71             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.47/0.71          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.47/0.71          | ~ (v1_funct_2 @ X32 @ X34 @ X33)
% 0.47/0.71          | ~ (v1_funct_1 @ X32))),
% 0.47/0.71      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.47/0.71  thf('59', plain,
% 0.47/0.71      ((~ (v1_funct_1 @ sk_C)
% 0.47/0.71        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.47/0.71        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.47/0.71           (k1_zfmisc_1 @ 
% 0.47/0.71            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 0.47/0.71        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.47/0.71            != (k2_relat_1 @ sk_C))
% 0.47/0.71        | ~ (v2_funct_1 @ sk_C))),
% 0.47/0.71      inference('sup-', [status(thm)], ['57', '58'])).
% 0.47/0.71  thf('60', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('61', plain,
% 0.47/0.71      (![X35 : $i]:
% 0.47/0.71         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.47/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.71  thf('62', plain,
% 0.47/0.71      (![X35 : $i]:
% 0.47/0.71         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.47/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.71  thf('63', plain,
% 0.47/0.71      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('64', plain,
% 0.47/0.71      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.47/0.71        | ~ (l1_struct_0 @ sk_A))),
% 0.47/0.71      inference('sup+', [status(thm)], ['62', '63'])).
% 0.47/0.71  thf('65', plain, ((l1_struct_0 @ sk_A)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('66', plain,
% 0.47/0.71      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.47/0.71      inference('demod', [status(thm)], ['64', '65'])).
% 0.47/0.71  thf('67', plain,
% 0.47/0.71      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.47/0.71        | ~ (l1_struct_0 @ sk_B))),
% 0.47/0.71      inference('sup+', [status(thm)], ['61', '66'])).
% 0.47/0.71  thf('68', plain, ((l1_struct_0 @ sk_B)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('69', plain,
% 0.47/0.71      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.47/0.71      inference('demod', [status(thm)], ['67', '68'])).
% 0.47/0.71  thf('70', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.47/0.71      inference('sup+', [status(thm)], ['11', '12'])).
% 0.47/0.71  thf('71', plain,
% 0.47/0.71      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.47/0.71      inference('demod', [status(thm)], ['69', '70'])).
% 0.47/0.71  thf('72', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.47/0.71      inference('demod', [status(thm)], ['49', '52', '55'])).
% 0.47/0.71  thf('73', plain,
% 0.47/0.71      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.47/0.71      inference('demod', [status(thm)], ['71', '72'])).
% 0.47/0.71  thf('74', plain,
% 0.47/0.71      (![X35 : $i]:
% 0.47/0.71         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.47/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.71  thf('75', plain,
% 0.47/0.71      (![X35 : $i]:
% 0.47/0.71         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.47/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.71  thf('76', plain,
% 0.47/0.71      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.47/0.71         = (k2_struct_0 @ sk_B))),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('77', plain,
% 0.47/0.71      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.47/0.71          = (k2_struct_0 @ sk_B))
% 0.47/0.71        | ~ (l1_struct_0 @ sk_A))),
% 0.47/0.71      inference('sup+', [status(thm)], ['75', '76'])).
% 0.47/0.71  thf('78', plain, ((l1_struct_0 @ sk_A)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('79', plain,
% 0.47/0.71      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.47/0.71         = (k2_struct_0 @ sk_B))),
% 0.47/0.71      inference('demod', [status(thm)], ['77', '78'])).
% 0.47/0.71  thf('80', plain,
% 0.47/0.71      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.47/0.71          = (k2_struct_0 @ sk_B))
% 0.47/0.71        | ~ (l1_struct_0 @ sk_B))),
% 0.47/0.71      inference('sup+', [status(thm)], ['74', '79'])).
% 0.47/0.71  thf('81', plain, ((l1_struct_0 @ sk_B)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('82', plain,
% 0.47/0.71      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.47/0.71         = (k2_struct_0 @ sk_B))),
% 0.47/0.71      inference('demod', [status(thm)], ['80', '81'])).
% 0.47/0.71  thf('83', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.47/0.71      inference('sup+', [status(thm)], ['11', '12'])).
% 0.47/0.71  thf('84', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.47/0.71      inference('sup+', [status(thm)], ['11', '12'])).
% 0.47/0.71  thf('85', plain,
% 0.47/0.71      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.47/0.71         = (k2_relat_1 @ sk_C))),
% 0.47/0.71      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.47/0.71  thf('86', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.47/0.71      inference('demod', [status(thm)], ['49', '52', '55'])).
% 0.47/0.71  thf('87', plain,
% 0.47/0.71      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.47/0.71         = (k2_relat_1 @ sk_C))),
% 0.47/0.71      inference('demod', [status(thm)], ['85', '86'])).
% 0.47/0.71  thf('88', plain, ((v2_funct_1 @ sk_C)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('89', plain,
% 0.47/0.71      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.47/0.71         (k1_zfmisc_1 @ 
% 0.47/0.71          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 0.47/0.71        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.47/0.71      inference('demod', [status(thm)], ['59', '60', '73', '87', '88'])).
% 0.47/0.71  thf('90', plain,
% 0.47/0.71      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.47/0.71        (k1_zfmisc_1 @ 
% 0.47/0.71         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.47/0.71      inference('simplify', [status(thm)], ['89'])).
% 0.47/0.71  thf(t38_relset_1, axiom,
% 0.47/0.71    (![A:$i,B:$i,C:$i]:
% 0.47/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.71       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.47/0.71         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.47/0.71  thf('91', plain,
% 0.47/0.71      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.47/0.71         (((k8_relset_1 @ X24 @ X25 @ X26 @ X25)
% 0.47/0.71            = (k1_relset_1 @ X24 @ X25 @ X26))
% 0.47/0.71          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.47/0.71      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.47/0.71  thf('92', plain,
% 0.47/0.71      (((k8_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.47/0.71         (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C))
% 0.47/0.71         = (k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.47/0.71            (k2_funct_1 @ sk_C)))),
% 0.47/0.71      inference('sup-', [status(thm)], ['90', '91'])).
% 0.47/0.71  thf('93', plain,
% 0.47/0.71      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.47/0.71        (k1_zfmisc_1 @ 
% 0.47/0.71         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.47/0.71      inference('simplify', [status(thm)], ['89'])).
% 0.47/0.71  thf(redefinition_k8_relset_1, axiom,
% 0.47/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.71       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.47/0.71  thf('94', plain,
% 0.47/0.71      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.47/0.71         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.47/0.71          | ((k8_relset_1 @ X21 @ X22 @ X20 @ X23) = (k10_relat_1 @ X20 @ X23)))),
% 0.47/0.71      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.47/0.71  thf('95', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         ((k8_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.47/0.71           (k2_funct_1 @ sk_C) @ X0) = (k10_relat_1 @ (k2_funct_1 @ sk_C) @ X0))),
% 0.47/0.71      inference('sup-', [status(thm)], ['93', '94'])).
% 0.47/0.71  thf('96', plain,
% 0.47/0.71      (((k10_relat_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C))
% 0.47/0.71         = (k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.47/0.71            (k2_funct_1 @ sk_C)))),
% 0.47/0.71      inference('demod', [status(thm)], ['92', '95'])).
% 0.47/0.71  thf(fc6_funct_1, axiom,
% 0.47/0.71    (![A:$i]:
% 0.47/0.71     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.47/0.71       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.47/0.71         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 0.47/0.71         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.47/0.71  thf('97', plain,
% 0.47/0.71      (![X5 : $i]:
% 0.47/0.71         ((v2_funct_1 @ (k2_funct_1 @ X5))
% 0.47/0.71          | ~ (v2_funct_1 @ X5)
% 0.47/0.71          | ~ (v1_funct_1 @ X5)
% 0.47/0.71          | ~ (v1_relat_1 @ X5))),
% 0.47/0.71      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.47/0.71  thf(dt_k2_funct_1, axiom,
% 0.47/0.71    (![A:$i]:
% 0.47/0.71     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.47/0.71       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.47/0.71         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.47/0.71  thf('98', plain,
% 0.47/0.71      (![X4 : $i]:
% 0.47/0.71         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 0.47/0.71          | ~ (v1_funct_1 @ X4)
% 0.47/0.71          | ~ (v1_relat_1 @ X4))),
% 0.47/0.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.47/0.71  thf('99', plain,
% 0.47/0.71      (![X4 : $i]:
% 0.47/0.71         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.47/0.71          | ~ (v1_funct_1 @ X4)
% 0.47/0.71          | ~ (v1_relat_1 @ X4))),
% 0.47/0.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.47/0.71  thf(t65_funct_1, axiom,
% 0.47/0.71    (![A:$i]:
% 0.47/0.71     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.47/0.71       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.47/0.71  thf('100', plain,
% 0.47/0.71      (![X10 : $i]:
% 0.47/0.71         (~ (v2_funct_1 @ X10)
% 0.47/0.71          | ((k2_funct_1 @ (k2_funct_1 @ X10)) = (X10))
% 0.47/0.71          | ~ (v1_funct_1 @ X10)
% 0.47/0.71          | ~ (v1_relat_1 @ X10))),
% 0.47/0.71      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.47/0.71  thf('101', plain,
% 0.47/0.71      (![X5 : $i]:
% 0.47/0.71         ((v2_funct_1 @ (k2_funct_1 @ X5))
% 0.47/0.71          | ~ (v2_funct_1 @ X5)
% 0.47/0.71          | ~ (v1_funct_1 @ X5)
% 0.47/0.71          | ~ (v1_relat_1 @ X5))),
% 0.47/0.71      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.47/0.71  thf('102', plain,
% 0.47/0.71      (![X4 : $i]:
% 0.47/0.71         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 0.47/0.71          | ~ (v1_funct_1 @ X4)
% 0.47/0.71          | ~ (v1_relat_1 @ X4))),
% 0.47/0.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.47/0.71  thf('103', plain,
% 0.47/0.71      (![X4 : $i]:
% 0.47/0.71         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.47/0.71          | ~ (v1_funct_1 @ X4)
% 0.47/0.71          | ~ (v1_relat_1 @ X4))),
% 0.47/0.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.47/0.71  thf('104', plain,
% 0.47/0.71      (![X10 : $i]:
% 0.47/0.71         (~ (v2_funct_1 @ X10)
% 0.47/0.71          | ((k2_funct_1 @ (k2_funct_1 @ X10)) = (X10))
% 0.47/0.71          | ~ (v1_funct_1 @ X10)
% 0.47/0.71          | ~ (v1_relat_1 @ X10))),
% 0.47/0.71      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.47/0.71  thf(t61_funct_1, axiom,
% 0.47/0.71    (![A:$i]:
% 0.47/0.71     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.47/0.71       ( ( v2_funct_1 @ A ) =>
% 0.47/0.71         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.47/0.71             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.47/0.71           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.47/0.71             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.47/0.71  thf('105', plain,
% 0.47/0.71      (![X9 : $i]:
% 0.47/0.71         (~ (v2_funct_1 @ X9)
% 0.47/0.71          | ((k5_relat_1 @ (k2_funct_1 @ X9) @ X9)
% 0.47/0.71              = (k6_relat_1 @ (k2_relat_1 @ X9)))
% 0.47/0.71          | ~ (v1_funct_1 @ X9)
% 0.47/0.71          | ~ (v1_relat_1 @ X9))),
% 0.47/0.71      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.47/0.71  thf('106', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.47/0.71            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.47/0.71          | ~ (v1_relat_1 @ X0)
% 0.47/0.71          | ~ (v1_funct_1 @ X0)
% 0.47/0.71          | ~ (v2_funct_1 @ X0)
% 0.47/0.71          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.47/0.71          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.47/0.71          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.47/0.71      inference('sup+', [status(thm)], ['104', '105'])).
% 0.47/0.71  thf('107', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         (~ (v1_relat_1 @ X0)
% 0.47/0.71          | ~ (v1_funct_1 @ X0)
% 0.47/0.71          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.47/0.71          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.47/0.71          | ~ (v2_funct_1 @ X0)
% 0.47/0.71          | ~ (v1_funct_1 @ X0)
% 0.47/0.71          | ~ (v1_relat_1 @ X0)
% 0.47/0.71          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.47/0.71              = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.47/0.71      inference('sup-', [status(thm)], ['103', '106'])).
% 0.47/0.71  thf('108', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.47/0.71            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.47/0.71          | ~ (v2_funct_1 @ X0)
% 0.47/0.71          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.47/0.71          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.47/0.71          | ~ (v1_funct_1 @ X0)
% 0.47/0.71          | ~ (v1_relat_1 @ X0))),
% 0.47/0.71      inference('simplify', [status(thm)], ['107'])).
% 0.47/0.71  thf('109', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         (~ (v1_relat_1 @ X0)
% 0.47/0.71          | ~ (v1_funct_1 @ X0)
% 0.47/0.71          | ~ (v1_relat_1 @ X0)
% 0.47/0.71          | ~ (v1_funct_1 @ X0)
% 0.47/0.71          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.47/0.71          | ~ (v2_funct_1 @ X0)
% 0.47/0.71          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.47/0.71              = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.47/0.71      inference('sup-', [status(thm)], ['102', '108'])).
% 0.47/0.71  thf('110', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.47/0.71            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.47/0.71          | ~ (v2_funct_1 @ X0)
% 0.47/0.71          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.47/0.71          | ~ (v1_funct_1 @ X0)
% 0.47/0.71          | ~ (v1_relat_1 @ X0))),
% 0.47/0.71      inference('simplify', [status(thm)], ['109'])).
% 0.47/0.71  thf('111', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         (~ (v1_relat_1 @ X0)
% 0.47/0.71          | ~ (v1_funct_1 @ X0)
% 0.47/0.71          | ~ (v2_funct_1 @ X0)
% 0.47/0.71          | ~ (v1_relat_1 @ X0)
% 0.47/0.71          | ~ (v1_funct_1 @ X0)
% 0.47/0.71          | ~ (v2_funct_1 @ X0)
% 0.47/0.71          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.47/0.71              = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.47/0.71      inference('sup-', [status(thm)], ['101', '110'])).
% 0.47/0.71  thf('112', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.47/0.71            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.47/0.71          | ~ (v2_funct_1 @ X0)
% 0.47/0.71          | ~ (v1_funct_1 @ X0)
% 0.47/0.71          | ~ (v1_relat_1 @ X0))),
% 0.47/0.71      inference('simplify', [status(thm)], ['111'])).
% 0.47/0.71  thf(t58_funct_1, axiom,
% 0.47/0.71    (![A:$i]:
% 0.47/0.71     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.47/0.71       ( ( v2_funct_1 @ A ) =>
% 0.47/0.71         ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.47/0.71             ( k1_relat_1 @ A ) ) & 
% 0.47/0.71           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.47/0.71             ( k1_relat_1 @ A ) ) ) ) ))).
% 0.47/0.71  thf('113', plain,
% 0.47/0.71      (![X8 : $i]:
% 0.47/0.71         (~ (v2_funct_1 @ X8)
% 0.47/0.71          | ((k2_relat_1 @ (k5_relat_1 @ X8 @ (k2_funct_1 @ X8)))
% 0.47/0.71              = (k1_relat_1 @ X8))
% 0.47/0.71          | ~ (v1_funct_1 @ X8)
% 0.47/0.71          | ~ (v1_relat_1 @ X8))),
% 0.47/0.71      inference('cnf', [status(esa)], [t58_funct_1])).
% 0.47/0.71  thf('114', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         (((k2_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.47/0.71            = (k1_relat_1 @ X0))
% 0.47/0.71          | ~ (v1_relat_1 @ X0)
% 0.47/0.71          | ~ (v1_funct_1 @ X0)
% 0.47/0.71          | ~ (v2_funct_1 @ X0)
% 0.47/0.71          | ~ (v1_relat_1 @ X0)
% 0.47/0.71          | ~ (v1_funct_1 @ X0)
% 0.47/0.71          | ~ (v2_funct_1 @ X0))),
% 0.47/0.71      inference('sup+', [status(thm)], ['112', '113'])).
% 0.47/0.71  thf(t71_relat_1, axiom,
% 0.47/0.71    (![A:$i]:
% 0.47/0.71     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.47/0.71       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.47/0.71  thf('115', plain, (![X3 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X3)) = (X3))),
% 0.47/0.71      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.47/0.71  thf('116', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         (((k2_relat_1 @ (k2_funct_1 @ X0)) = (k1_relat_1 @ X0))
% 0.47/0.71          | ~ (v1_relat_1 @ X0)
% 0.47/0.71          | ~ (v1_funct_1 @ X0)
% 0.47/0.71          | ~ (v2_funct_1 @ X0)
% 0.47/0.71          | ~ (v1_relat_1 @ X0)
% 0.47/0.71          | ~ (v1_funct_1 @ X0)
% 0.47/0.71          | ~ (v2_funct_1 @ X0))),
% 0.47/0.71      inference('demod', [status(thm)], ['114', '115'])).
% 0.47/0.71  thf('117', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         (~ (v2_funct_1 @ X0)
% 0.47/0.71          | ~ (v1_funct_1 @ X0)
% 0.47/0.71          | ~ (v1_relat_1 @ X0)
% 0.47/0.71          | ((k2_relat_1 @ (k2_funct_1 @ X0)) = (k1_relat_1 @ X0)))),
% 0.47/0.71      inference('simplify', [status(thm)], ['116'])).
% 0.47/0.71  thf('118', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         (((k2_relat_1 @ X0) = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.47/0.71          | ~ (v1_relat_1 @ X0)
% 0.47/0.71          | ~ (v1_funct_1 @ X0)
% 0.47/0.71          | ~ (v2_funct_1 @ X0)
% 0.47/0.71          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.47/0.71          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.47/0.71          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.47/0.71      inference('sup+', [status(thm)], ['100', '117'])).
% 0.47/0.71  thf('119', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         (~ (v1_relat_1 @ X0)
% 0.47/0.71          | ~ (v1_funct_1 @ X0)
% 0.47/0.71          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.47/0.71          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.47/0.71          | ~ (v2_funct_1 @ X0)
% 0.47/0.71          | ~ (v1_funct_1 @ X0)
% 0.47/0.71          | ~ (v1_relat_1 @ X0)
% 0.47/0.71          | ((k2_relat_1 @ X0) = (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 0.47/0.71      inference('sup-', [status(thm)], ['99', '118'])).
% 0.47/0.71  thf('120', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         (((k2_relat_1 @ X0) = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.47/0.71          | ~ (v2_funct_1 @ X0)
% 0.47/0.71          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.47/0.71          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.47/0.71          | ~ (v1_funct_1 @ X0)
% 0.47/0.71          | ~ (v1_relat_1 @ X0))),
% 0.47/0.71      inference('simplify', [status(thm)], ['119'])).
% 0.47/0.71  thf('121', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         (~ (v1_relat_1 @ X0)
% 0.47/0.71          | ~ (v1_funct_1 @ X0)
% 0.47/0.71          | ~ (v1_relat_1 @ X0)
% 0.47/0.71          | ~ (v1_funct_1 @ X0)
% 0.47/0.71          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.47/0.71          | ~ (v2_funct_1 @ X0)
% 0.47/0.71          | ((k2_relat_1 @ X0) = (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 0.47/0.71      inference('sup-', [status(thm)], ['98', '120'])).
% 0.47/0.71  thf('122', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         (((k2_relat_1 @ X0) = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.47/0.71          | ~ (v2_funct_1 @ X0)
% 0.47/0.71          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.47/0.71          | ~ (v1_funct_1 @ X0)
% 0.47/0.71          | ~ (v1_relat_1 @ X0))),
% 0.47/0.71      inference('simplify', [status(thm)], ['121'])).
% 0.47/0.71  thf('123', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         (~ (v1_relat_1 @ X0)
% 0.47/0.71          | ~ (v1_funct_1 @ X0)
% 0.47/0.71          | ~ (v2_funct_1 @ X0)
% 0.47/0.71          | ~ (v1_relat_1 @ X0)
% 0.47/0.71          | ~ (v1_funct_1 @ X0)
% 0.47/0.71          | ~ (v2_funct_1 @ X0)
% 0.47/0.71          | ((k2_relat_1 @ X0) = (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 0.47/0.71      inference('sup-', [status(thm)], ['97', '122'])).
% 0.47/0.71  thf('124', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         (((k2_relat_1 @ X0) = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.47/0.71          | ~ (v2_funct_1 @ X0)
% 0.47/0.71          | ~ (v1_funct_1 @ X0)
% 0.47/0.71          | ~ (v1_relat_1 @ X0))),
% 0.47/0.71      inference('simplify', [status(thm)], ['123'])).
% 0.47/0.71  thf('125', plain,
% 0.47/0.71      (![X4 : $i]:
% 0.47/0.71         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.47/0.71          | ~ (v1_funct_1 @ X4)
% 0.47/0.71          | ~ (v1_relat_1 @ X4))),
% 0.47/0.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.47/0.71  thf(t155_funct_1, axiom,
% 0.47/0.71    (![A:$i,B:$i]:
% 0.47/0.71     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.47/0.71       ( ( v2_funct_1 @ B ) =>
% 0.47/0.71         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 0.47/0.71  thf('126', plain,
% 0.47/0.71      (![X6 : $i, X7 : $i]:
% 0.47/0.71         (~ (v2_funct_1 @ X6)
% 0.47/0.71          | ((k10_relat_1 @ X6 @ X7) = (k9_relat_1 @ (k2_funct_1 @ X6) @ X7))
% 0.47/0.71          | ~ (v1_funct_1 @ X6)
% 0.47/0.71          | ~ (v1_relat_1 @ X6))),
% 0.47/0.71      inference('cnf', [status(esa)], [t155_funct_1])).
% 0.47/0.71  thf(t146_relat_1, axiom,
% 0.47/0.71    (![A:$i]:
% 0.47/0.71     ( ( v1_relat_1 @ A ) =>
% 0.47/0.71       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.47/0.71  thf('127', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         (((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (k2_relat_1 @ X0))
% 0.47/0.71          | ~ (v1_relat_1 @ X0))),
% 0.47/0.71      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.47/0.71  thf('128', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         (((k10_relat_1 @ X0 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.47/0.71            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.47/0.71          | ~ (v1_relat_1 @ X0)
% 0.47/0.71          | ~ (v1_funct_1 @ X0)
% 0.47/0.71          | ~ (v2_funct_1 @ X0)
% 0.47/0.71          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.47/0.71      inference('sup+', [status(thm)], ['126', '127'])).
% 0.47/0.71  thf('129', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         (~ (v1_relat_1 @ X0)
% 0.47/0.71          | ~ (v1_funct_1 @ X0)
% 0.47/0.71          | ~ (v2_funct_1 @ X0)
% 0.47/0.71          | ~ (v1_funct_1 @ X0)
% 0.47/0.71          | ~ (v1_relat_1 @ X0)
% 0.47/0.71          | ((k10_relat_1 @ X0 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.47/0.71              = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 0.47/0.71      inference('sup-', [status(thm)], ['125', '128'])).
% 0.47/0.71  thf('130', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         (((k10_relat_1 @ X0 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.47/0.71            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.47/0.71          | ~ (v2_funct_1 @ X0)
% 0.47/0.71          | ~ (v1_funct_1 @ X0)
% 0.47/0.71          | ~ (v1_relat_1 @ X0))),
% 0.47/0.71      inference('simplify', [status(thm)], ['129'])).
% 0.47/0.71  thf('131', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         (((k10_relat_1 @ X0 @ (k2_relat_1 @ X0))
% 0.47/0.71            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.47/0.71          | ~ (v1_relat_1 @ X0)
% 0.47/0.71          | ~ (v1_funct_1 @ X0)
% 0.47/0.71          | ~ (v2_funct_1 @ X0)
% 0.47/0.71          | ~ (v1_relat_1 @ X0)
% 0.47/0.71          | ~ (v1_funct_1 @ X0)
% 0.47/0.71          | ~ (v2_funct_1 @ X0))),
% 0.47/0.71      inference('sup+', [status(thm)], ['124', '130'])).
% 0.47/0.71  thf('132', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         (~ (v2_funct_1 @ X0)
% 0.47/0.71          | ~ (v1_funct_1 @ X0)
% 0.47/0.71          | ~ (v1_relat_1 @ X0)
% 0.47/0.71          | ((k10_relat_1 @ X0 @ (k2_relat_1 @ X0))
% 0.47/0.71              = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 0.47/0.71      inference('simplify', [status(thm)], ['131'])).
% 0.47/0.71  thf('133', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         (((k2_relat_1 @ X0) = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.47/0.71          | ~ (v2_funct_1 @ X0)
% 0.47/0.71          | ~ (v1_funct_1 @ X0)
% 0.47/0.71          | ~ (v1_relat_1 @ X0))),
% 0.47/0.71      inference('simplify', [status(thm)], ['123'])).
% 0.47/0.71  thf('134', plain,
% 0.47/0.71      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.47/0.71        (k1_zfmisc_1 @ 
% 0.47/0.71         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.47/0.71      inference('simplify', [status(thm)], ['89'])).
% 0.47/0.71  thf('135', plain,
% 0.47/0.71      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.47/0.71         ((v4_relat_1 @ X14 @ X15)
% 0.47/0.71          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.47/0.71      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.47/0.71  thf('136', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.47/0.71      inference('sup-', [status(thm)], ['134', '135'])).
% 0.47/0.71  thf('137', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         (((k2_relat_1 @ X0) = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.47/0.71          | ~ (v2_funct_1 @ X0)
% 0.47/0.71          | ~ (v1_funct_1 @ X0)
% 0.47/0.71          | ~ (v1_relat_1 @ X0))),
% 0.47/0.71      inference('simplify', [status(thm)], ['123'])).
% 0.47/0.71  thf('138', plain,
% 0.47/0.71      (![X30 : $i, X31 : $i]:
% 0.47/0.71         (((k1_relat_1 @ X31) != (X30))
% 0.47/0.71          | (v1_partfun1 @ X31 @ X30)
% 0.47/0.71          | ~ (v4_relat_1 @ X31 @ X30)
% 0.47/0.71          | ~ (v1_relat_1 @ X31))),
% 0.47/0.71      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.47/0.71  thf('139', plain,
% 0.47/0.71      (![X31 : $i]:
% 0.47/0.71         (~ (v1_relat_1 @ X31)
% 0.47/0.71          | ~ (v4_relat_1 @ X31 @ (k1_relat_1 @ X31))
% 0.47/0.71          | (v1_partfun1 @ X31 @ (k1_relat_1 @ X31)))),
% 0.47/0.71      inference('simplify', [status(thm)], ['138'])).
% 0.47/0.71  thf('140', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         (~ (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.47/0.71          | ~ (v1_relat_1 @ X0)
% 0.47/0.71          | ~ (v1_funct_1 @ X0)
% 0.47/0.71          | ~ (v2_funct_1 @ X0)
% 0.47/0.71          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.47/0.71          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.47/0.71      inference('sup-', [status(thm)], ['137', '139'])).
% 0.47/0.71  thf('141', plain,
% 0.47/0.71      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.47/0.71        | (v1_partfun1 @ (k2_funct_1 @ sk_C) @ 
% 0.47/0.71           (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.47/0.71        | ~ (v2_funct_1 @ sk_C)
% 0.47/0.71        | ~ (v1_funct_1 @ sk_C)
% 0.47/0.71        | ~ (v1_relat_1 @ sk_C))),
% 0.47/0.71      inference('sup-', [status(thm)], ['136', '140'])).
% 0.47/0.71  thf('142', plain,
% 0.47/0.71      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.47/0.71        (k1_zfmisc_1 @ 
% 0.47/0.71         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.47/0.71      inference('simplify', [status(thm)], ['89'])).
% 0.47/0.71  thf('143', plain,
% 0.47/0.71      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.47/0.71         ((v1_relat_1 @ X11)
% 0.47/0.71          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.47/0.71      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.47/0.71  thf('144', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.47/0.71      inference('sup-', [status(thm)], ['142', '143'])).
% 0.47/0.71  thf('145', plain, ((v2_funct_1 @ sk_C)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('146', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('147', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.71      inference('sup-', [status(thm)], ['50', '51'])).
% 0.47/0.71  thf('148', plain,
% 0.47/0.71      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.47/0.71      inference('demod', [status(thm)], ['141', '144', '145', '146', '147'])).
% 0.47/0.71  thf('149', plain,
% 0.47/0.71      (((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.47/0.71        | ~ (v1_relat_1 @ sk_C)
% 0.47/0.71        | ~ (v1_funct_1 @ sk_C)
% 0.47/0.71        | ~ (v2_funct_1 @ sk_C))),
% 0.47/0.71      inference('sup+', [status(thm)], ['133', '148'])).
% 0.47/0.71  thf('150', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.71      inference('sup-', [status(thm)], ['50', '51'])).
% 0.47/0.71  thf('151', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('152', plain, ((v2_funct_1 @ sk_C)),
% 0.47/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.71  thf('153', plain,
% 0.47/0.71      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.47/0.71      inference('demod', [status(thm)], ['149', '150', '151', '152'])).
% 0.47/0.71  thf('154', plain,
% 0.47/0.71      (![X30 : $i, X31 : $i]:
% 0.47/0.71         (~ (v1_partfun1 @ X31 @ X30)
% 0.47/0.71          | ((k1_relat_1 @ X31) = (X30))
% 0.47/0.71          | ~ (v4_relat_1 @ X31 @ X30)
% 0.47/0.71          | ~ (v1_relat_1 @ X31))),
% 0.47/0.71      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.47/0.71  thf('155', plain,
% 0.47/0.71      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.47/0.71        | ~ (v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.47/0.71        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C)))),
% 0.47/0.71      inference('sup-', [status(thm)], ['153', '154'])).
% 0.47/0.71  thf('156', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.47/0.71      inference('sup-', [status(thm)], ['142', '143'])).
% 0.47/0.71  thf('157', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.47/0.71      inference('sup-', [status(thm)], ['134', '135'])).
% 0.47/0.71  thf('158', plain,
% 0.47/0.71      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 0.47/0.71      inference('demod', [status(thm)], ['155', '156', '157'])).
% 0.47/0.71  thf('159', plain,
% 0.47/0.71      (![X0 : $i]:
% 0.47/0.71         (~ (v2_funct_1 @ X0)
% 0.47/0.71          | ~ (v1_funct_1 @ X0)
% 0.47/0.71          | ~ (v1_relat_1 @ X0)
% 0.47/0.71          | ((k2_relat_1 @ (k2_funct_1 @ X0)) = (k1_relat_1 @ X0)))),
% 0.47/0.71      inference('simplify', [status(thm)], ['116'])).
% 0.47/0.71  thf('160', plain,
% 0.47/0.71      (![X4 : $i]:
% 0.47/0.71         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.47/0.71          | ~ (v1_funct_1 @ X4)
% 0.47/0.71          | ~ (v1_relat_1 @ X4))),
% 0.47/0.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.47/0.71  thf('161', plain,
% 0.47/0.71      (![X5 : $i]:
% 0.47/0.71         ((v2_funct_1 @ (k2_funct_1 @ X5))
% 0.47/0.71          | ~ (v2_funct_1 @ X5)
% 0.47/0.71          | ~ (v1_funct_1 @ X5)
% 0.47/0.71          | ~ (v1_relat_1 @ X5))),
% 0.47/0.71      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.47/0.71  thf('162', plain,
% 0.47/0.71      (![X4 : $i]:
% 0.47/0.71         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 0.47/0.71          | ~ (v1_funct_1 @ X4)
% 0.47/0.71          | ~ (v1_relat_1 @ X4))),
% 0.47/0.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.47/0.71  thf('163', plain,
% 0.47/0.71      (![X4 : $i]:
% 0.47/0.71         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.47/0.71          | ~ (v1_funct_1 @ X4)
% 0.47/0.71          | ~ (v1_relat_1 @ X4))),
% 0.47/0.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.47/0.71  thf('164', plain,
% 0.47/0.71      (![X10 : $i]:
% 0.47/0.71         (~ (v2_funct_1 @ X10)
% 0.47/0.71          | ((k2_funct_1 @ (k2_funct_1 @ X10)) = (X10))
% 0.47/0.71          | ~ (v1_funct_1 @ X10)
% 0.47/0.71          | ~ (v1_relat_1 @ X10))),
% 0.47/0.71      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.47/0.71  thf('165', plain,
% 0.47/0.71      (![X6 : $i, X7 : $i]:
% 0.47/0.71         (~ (v2_funct_1 @ X6)
% 0.47/0.71          | ((k10_relat_1 @ X6 @ X7) = (k9_relat_1 @ (k2_funct_1 @ X6) @ X7))
% 0.47/0.71          | ~ (v1_funct_1 @ X6)
% 0.47/0.71          | ~ (v1_relat_1 @ X6))),
% 0.47/0.71      inference('cnf', [status(esa)], [t155_funct_1])).
% 0.47/0.71  thf('166', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i]:
% 0.47/0.71         (((k10_relat_1 @ (k2_funct_1 @ X0) @ X1) = (k9_relat_1 @ X0 @ X1))
% 0.47/0.71          | ~ (v1_relat_1 @ X0)
% 0.47/0.71          | ~ (v1_funct_1 @ X0)
% 0.47/0.71          | ~ (v2_funct_1 @ X0)
% 0.47/0.71          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.47/0.71          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.47/0.71          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.47/0.71      inference('sup+', [status(thm)], ['164', '165'])).
% 0.47/0.71  thf('167', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i]:
% 0.47/0.71         (~ (v1_relat_1 @ X0)
% 0.47/0.71          | ~ (v1_funct_1 @ X0)
% 0.47/0.71          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.47/0.71          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.47/0.71          | ~ (v2_funct_1 @ X0)
% 0.47/0.71          | ~ (v1_funct_1 @ X0)
% 0.47/0.71          | ~ (v1_relat_1 @ X0)
% 0.47/0.71          | ((k10_relat_1 @ (k2_funct_1 @ X0) @ X1) = (k9_relat_1 @ X0 @ X1)))),
% 0.47/0.71      inference('sup-', [status(thm)], ['163', '166'])).
% 0.47/0.71  thf('168', plain,
% 0.47/0.71      (![X0 : $i, X1 : $i]:
% 0.47/0.71         (((k10_relat_1 @ (k2_funct_1 @ X0) @ X1) = (k9_relat_1 @ X0 @ X1))
% 0.47/0.71          | ~ (v2_funct_1 @ X0)
% 0.47/0.71          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.47/0.71          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.47/0.71          | ~ (v1_funct_1 @ X0)
% 0.47/0.71          | ~ (v1_relat_1 @ X0))),
% 0.47/0.72      inference('simplify', [status(thm)], ['167'])).
% 0.47/0.72  thf('169', plain,
% 0.47/0.72      (![X0 : $i, X1 : $i]:
% 0.47/0.72         (~ (v1_relat_1 @ X0)
% 0.47/0.72          | ~ (v1_funct_1 @ X0)
% 0.47/0.72          | ~ (v1_relat_1 @ X0)
% 0.47/0.72          | ~ (v1_funct_1 @ X0)
% 0.47/0.72          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.47/0.72          | ~ (v2_funct_1 @ X0)
% 0.47/0.72          | ((k10_relat_1 @ (k2_funct_1 @ X0) @ X1) = (k9_relat_1 @ X0 @ X1)))),
% 0.47/0.72      inference('sup-', [status(thm)], ['162', '168'])).
% 0.47/0.72  thf('170', plain,
% 0.47/0.72      (![X0 : $i, X1 : $i]:
% 0.47/0.72         (((k10_relat_1 @ (k2_funct_1 @ X0) @ X1) = (k9_relat_1 @ X0 @ X1))
% 0.47/0.72          | ~ (v2_funct_1 @ X0)
% 0.47/0.72          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.47/0.72          | ~ (v1_funct_1 @ X0)
% 0.47/0.72          | ~ (v1_relat_1 @ X0))),
% 0.47/0.72      inference('simplify', [status(thm)], ['169'])).
% 0.47/0.72  thf('171', plain,
% 0.47/0.72      (![X0 : $i, X1 : $i]:
% 0.47/0.72         (~ (v1_relat_1 @ X0)
% 0.47/0.72          | ~ (v1_funct_1 @ X0)
% 0.47/0.72          | ~ (v2_funct_1 @ X0)
% 0.47/0.72          | ~ (v1_relat_1 @ X0)
% 0.47/0.72          | ~ (v1_funct_1 @ X0)
% 0.47/0.72          | ~ (v2_funct_1 @ X0)
% 0.47/0.72          | ((k10_relat_1 @ (k2_funct_1 @ X0) @ X1) = (k9_relat_1 @ X0 @ X1)))),
% 0.47/0.72      inference('sup-', [status(thm)], ['161', '170'])).
% 0.47/0.72  thf('172', plain,
% 0.47/0.72      (![X0 : $i, X1 : $i]:
% 0.47/0.72         (((k10_relat_1 @ (k2_funct_1 @ X0) @ X1) = (k9_relat_1 @ X0 @ X1))
% 0.47/0.72          | ~ (v2_funct_1 @ X0)
% 0.47/0.72          | ~ (v1_funct_1 @ X0)
% 0.47/0.72          | ~ (v1_relat_1 @ X0))),
% 0.47/0.72      inference('simplify', [status(thm)], ['171'])).
% 0.47/0.72  thf(t169_relat_1, axiom,
% 0.47/0.72    (![A:$i]:
% 0.47/0.72     ( ( v1_relat_1 @ A ) =>
% 0.47/0.72       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.47/0.72  thf('173', plain,
% 0.47/0.72      (![X1 : $i]:
% 0.47/0.72         (((k10_relat_1 @ X1 @ (k2_relat_1 @ X1)) = (k1_relat_1 @ X1))
% 0.47/0.72          | ~ (v1_relat_1 @ X1))),
% 0.47/0.72      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.47/0.72  thf('174', plain,
% 0.47/0.72      (![X0 : $i]:
% 0.47/0.72         (((k9_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.47/0.72            = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.47/0.72          | ~ (v1_relat_1 @ X0)
% 0.47/0.72          | ~ (v1_funct_1 @ X0)
% 0.47/0.72          | ~ (v2_funct_1 @ X0)
% 0.47/0.72          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.47/0.72      inference('sup+', [status(thm)], ['172', '173'])).
% 0.47/0.72  thf('175', plain,
% 0.47/0.72      (![X0 : $i]:
% 0.47/0.72         (~ (v1_relat_1 @ X0)
% 0.47/0.72          | ~ (v1_funct_1 @ X0)
% 0.47/0.72          | ~ (v2_funct_1 @ X0)
% 0.47/0.72          | ~ (v1_funct_1 @ X0)
% 0.47/0.72          | ~ (v1_relat_1 @ X0)
% 0.47/0.72          | ((k9_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.47/0.72              = (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 0.47/0.72      inference('sup-', [status(thm)], ['160', '174'])).
% 0.47/0.72  thf('176', plain,
% 0.47/0.72      (![X0 : $i]:
% 0.47/0.72         (((k9_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.47/0.72            = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.47/0.72          | ~ (v2_funct_1 @ X0)
% 0.47/0.72          | ~ (v1_funct_1 @ X0)
% 0.47/0.72          | ~ (v1_relat_1 @ X0))),
% 0.47/0.72      inference('simplify', [status(thm)], ['175'])).
% 0.47/0.72  thf('177', plain,
% 0.47/0.72      (![X0 : $i]:
% 0.47/0.72         (((k9_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.47/0.72            = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.47/0.72          | ~ (v1_relat_1 @ X0)
% 0.47/0.72          | ~ (v1_funct_1 @ X0)
% 0.47/0.72          | ~ (v2_funct_1 @ X0)
% 0.47/0.72          | ~ (v1_relat_1 @ X0)
% 0.47/0.72          | ~ (v1_funct_1 @ X0)
% 0.47/0.72          | ~ (v2_funct_1 @ X0))),
% 0.47/0.72      inference('sup+', [status(thm)], ['159', '176'])).
% 0.47/0.72  thf('178', plain,
% 0.47/0.72      (![X0 : $i]:
% 0.47/0.72         (~ (v2_funct_1 @ X0)
% 0.47/0.72          | ~ (v1_funct_1 @ X0)
% 0.47/0.72          | ~ (v1_relat_1 @ X0)
% 0.47/0.72          | ((k9_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.47/0.72              = (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 0.47/0.72      inference('simplify', [status(thm)], ['177'])).
% 0.47/0.72  thf('179', plain,
% 0.47/0.72      (![X0 : $i]:
% 0.47/0.72         (~ (v2_funct_1 @ X0)
% 0.47/0.72          | ~ (v1_funct_1 @ X0)
% 0.47/0.72          | ~ (v1_relat_1 @ X0)
% 0.47/0.72          | ((k2_relat_1 @ (k2_funct_1 @ X0)) = (k1_relat_1 @ X0)))),
% 0.47/0.72      inference('simplify', [status(thm)], ['116'])).
% 0.47/0.72  thf('180', plain,
% 0.47/0.72      (![X0 : $i]:
% 0.47/0.72         (~ (v2_funct_1 @ X0)
% 0.47/0.72          | ~ (v1_funct_1 @ X0)
% 0.47/0.72          | ~ (v1_relat_1 @ X0)
% 0.47/0.72          | ((k9_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.47/0.72              = (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 0.47/0.72      inference('simplify', [status(thm)], ['177'])).
% 0.47/0.72  thf('181', plain,
% 0.47/0.72      (![X0 : $i]:
% 0.47/0.72         (((k10_relat_1 @ X0 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.47/0.72            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.47/0.72          | ~ (v2_funct_1 @ X0)
% 0.47/0.72          | ~ (v1_funct_1 @ X0)
% 0.47/0.72          | ~ (v1_relat_1 @ X0))),
% 0.47/0.72      inference('simplify', [status(thm)], ['129'])).
% 0.47/0.72  thf('182', plain,
% 0.47/0.72      (![X0 : $i]:
% 0.47/0.72         (((k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.47/0.72            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.47/0.72          | ~ (v1_relat_1 @ X0)
% 0.47/0.72          | ~ (v1_funct_1 @ X0)
% 0.47/0.72          | ~ (v2_funct_1 @ X0)
% 0.47/0.72          | ~ (v1_relat_1 @ X0)
% 0.47/0.72          | ~ (v1_funct_1 @ X0)
% 0.47/0.72          | ~ (v2_funct_1 @ X0))),
% 0.47/0.72      inference('sup+', [status(thm)], ['180', '181'])).
% 0.47/0.72  thf('183', plain,
% 0.47/0.72      (![X0 : $i]:
% 0.47/0.72         (~ (v2_funct_1 @ X0)
% 0.47/0.72          | ~ (v1_funct_1 @ X0)
% 0.47/0.72          | ~ (v1_relat_1 @ X0)
% 0.47/0.72          | ((k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.47/0.72              = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 0.47/0.72      inference('simplify', [status(thm)], ['182'])).
% 0.47/0.72  thf('184', plain,
% 0.47/0.72      (![X0 : $i]:
% 0.47/0.72         (((k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.47/0.72            = (k1_relat_1 @ X0))
% 0.47/0.72          | ~ (v1_relat_1 @ X0)
% 0.47/0.72          | ~ (v1_funct_1 @ X0)
% 0.47/0.72          | ~ (v2_funct_1 @ X0)
% 0.47/0.72          | ~ (v1_relat_1 @ X0)
% 0.47/0.72          | ~ (v1_funct_1 @ X0)
% 0.47/0.72          | ~ (v2_funct_1 @ X0))),
% 0.47/0.72      inference('sup+', [status(thm)], ['179', '183'])).
% 0.47/0.72  thf('185', plain,
% 0.47/0.72      (![X0 : $i]:
% 0.47/0.72         (~ (v2_funct_1 @ X0)
% 0.47/0.72          | ~ (v1_funct_1 @ X0)
% 0.47/0.72          | ~ (v1_relat_1 @ X0)
% 0.47/0.72          | ((k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.47/0.72              = (k1_relat_1 @ X0)))),
% 0.47/0.72      inference('simplify', [status(thm)], ['184'])).
% 0.47/0.72  thf('186', plain,
% 0.47/0.72      (![X0 : $i]:
% 0.47/0.72         (((k10_relat_1 @ X0 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.47/0.72            = (k1_relat_1 @ X0))
% 0.47/0.72          | ~ (v1_relat_1 @ X0)
% 0.47/0.72          | ~ (v1_funct_1 @ X0)
% 0.47/0.72          | ~ (v2_funct_1 @ X0)
% 0.47/0.72          | ~ (v1_relat_1 @ X0)
% 0.47/0.72          | ~ (v1_funct_1 @ X0)
% 0.47/0.72          | ~ (v2_funct_1 @ X0))),
% 0.47/0.72      inference('sup+', [status(thm)], ['178', '185'])).
% 0.47/0.72  thf('187', plain,
% 0.47/0.72      (![X0 : $i]:
% 0.47/0.72         (~ (v2_funct_1 @ X0)
% 0.47/0.72          | ~ (v1_funct_1 @ X0)
% 0.47/0.72          | ~ (v1_relat_1 @ X0)
% 0.47/0.72          | ((k10_relat_1 @ X0 @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.47/0.72              = (k1_relat_1 @ X0)))),
% 0.47/0.72      inference('simplify', [status(thm)], ['186'])).
% 0.47/0.72  thf('188', plain,
% 0.47/0.72      ((((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))
% 0.47/0.72        | ~ (v1_relat_1 @ sk_C)
% 0.47/0.72        | ~ (v1_funct_1 @ sk_C)
% 0.47/0.72        | ~ (v2_funct_1 @ sk_C))),
% 0.47/0.72      inference('sup+', [status(thm)], ['158', '187'])).
% 0.47/0.72  thf('189', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.72      inference('sup-', [status(thm)], ['50', '51'])).
% 0.47/0.72  thf('190', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.72  thf('191', plain, ((v2_funct_1 @ sk_C)),
% 0.47/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.72  thf('192', plain,
% 0.47/0.72      (((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.47/0.72      inference('demod', [status(thm)], ['188', '189', '190', '191'])).
% 0.47/0.72  thf('193', plain,
% 0.47/0.72      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))
% 0.47/0.72        | ~ (v1_relat_1 @ sk_C)
% 0.47/0.72        | ~ (v1_funct_1 @ sk_C)
% 0.47/0.72        | ~ (v2_funct_1 @ sk_C))),
% 0.47/0.72      inference('sup+', [status(thm)], ['132', '192'])).
% 0.47/0.72  thf('194', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.72      inference('sup-', [status(thm)], ['50', '51'])).
% 0.47/0.72  thf('195', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.72  thf('196', plain, ((v2_funct_1 @ sk_C)),
% 0.47/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.72  thf('197', plain,
% 0.47/0.72      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.47/0.72      inference('demod', [status(thm)], ['193', '194', '195', '196'])).
% 0.47/0.72  thf('198', plain,
% 0.47/0.72      (![X1 : $i]:
% 0.47/0.72         (((k10_relat_1 @ X1 @ (k2_relat_1 @ X1)) = (k1_relat_1 @ X1))
% 0.47/0.72          | ~ (v1_relat_1 @ X1))),
% 0.47/0.72      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.47/0.72  thf('199', plain,
% 0.47/0.72      ((((k10_relat_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C))
% 0.47/0.72          = (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.47/0.72        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.47/0.72      inference('sup+', [status(thm)], ['197', '198'])).
% 0.47/0.72  thf('200', plain,
% 0.47/0.72      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 0.47/0.72      inference('demod', [status(thm)], ['155', '156', '157'])).
% 0.47/0.72  thf('201', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.47/0.72      inference('sup-', [status(thm)], ['142', '143'])).
% 0.47/0.72  thf('202', plain,
% 0.47/0.72      (((k10_relat_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C))
% 0.47/0.72         = (k2_relat_1 @ sk_C))),
% 0.47/0.72      inference('demod', [status(thm)], ['199', '200', '201'])).
% 0.47/0.72  thf('203', plain,
% 0.47/0.72      (((k2_relat_1 @ sk_C)
% 0.47/0.72         = (k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.47/0.72            (k2_funct_1 @ sk_C)))),
% 0.47/0.72      inference('demod', [status(thm)], ['96', '202'])).
% 0.47/0.72  thf('204', plain,
% 0.47/0.72      (![X35 : $i]:
% 0.47/0.72         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.47/0.72      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.72  thf('205', plain,
% 0.47/0.72      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.72          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.72          != (k2_struct_0 @ sk_B))
% 0.47/0.72        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.72            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.72            != (k2_struct_0 @ sk_A)))),
% 0.47/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.72  thf('206', plain,
% 0.47/0.72      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.72          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.72          != (k2_struct_0 @ sk_B)))
% 0.47/0.72         <= (~
% 0.47/0.72             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.72                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.72                = (k2_struct_0 @ sk_B))))),
% 0.47/0.72      inference('split', [status(esa)], ['205'])).
% 0.47/0.72  thf('207', plain,
% 0.47/0.72      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.72           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.72           != (k2_struct_0 @ sk_B))
% 0.47/0.72         | ~ (l1_struct_0 @ sk_B)))
% 0.47/0.72         <= (~
% 0.47/0.72             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.72                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.72                = (k2_struct_0 @ sk_B))))),
% 0.47/0.72      inference('sup-', [status(thm)], ['204', '206'])).
% 0.47/0.72  thf('208', plain, ((l1_struct_0 @ sk_B)),
% 0.47/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.72  thf('209', plain,
% 0.47/0.72      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.72          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.72          != (k2_struct_0 @ sk_B)))
% 0.47/0.72         <= (~
% 0.47/0.72             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.72                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.72                = (k2_struct_0 @ sk_B))))),
% 0.47/0.72      inference('demod', [status(thm)], ['207', '208'])).
% 0.47/0.72  thf('210', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.47/0.72      inference('sup+', [status(thm)], ['11', '12'])).
% 0.47/0.72  thf('211', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.47/0.72      inference('clc', [status(thm)], ['33', '43'])).
% 0.47/0.72  thf('212', plain,
% 0.47/0.72      (![X30 : $i, X31 : $i]:
% 0.47/0.72         (~ (v1_partfun1 @ X31 @ X30)
% 0.47/0.72          | ((k1_relat_1 @ X31) = (X30))
% 0.47/0.72          | ~ (v4_relat_1 @ X31 @ X30)
% 0.47/0.72          | ~ (v1_relat_1 @ X31))),
% 0.47/0.72      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.47/0.72  thf('213', plain,
% 0.47/0.72      ((~ (v1_relat_1 @ sk_C)
% 0.47/0.72        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.47/0.72        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.47/0.72      inference('sup-', [status(thm)], ['211', '212'])).
% 0.47/0.72  thf('214', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.72      inference('sup-', [status(thm)], ['50', '51'])).
% 0.47/0.72  thf('215', plain,
% 0.47/0.72      ((m1_subset_1 @ sk_C @ 
% 0.47/0.72        (k1_zfmisc_1 @ 
% 0.47/0.72         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.72  thf('216', plain,
% 0.47/0.72      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.47/0.72         ((v4_relat_1 @ X14 @ X15)
% 0.47/0.72          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.47/0.72      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.47/0.72  thf('217', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.47/0.72      inference('sup-', [status(thm)], ['215', '216'])).
% 0.47/0.72  thf('218', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.47/0.72      inference('demod', [status(thm)], ['213', '214', '217'])).
% 0.47/0.72  thf('219', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.47/0.72      inference('demod', [status(thm)], ['213', '214', '217'])).
% 0.47/0.72  thf('220', plain,
% 0.47/0.72      (![X35 : $i]:
% 0.47/0.72         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.47/0.72      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.72  thf('221', plain,
% 0.47/0.72      ((m1_subset_1 @ sk_C @ 
% 0.47/0.72        (k1_zfmisc_1 @ 
% 0.47/0.72         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.72      inference('demod', [status(thm)], ['3', '4'])).
% 0.47/0.72  thf('222', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.47/0.72      inference('demod', [status(thm)], ['49', '52', '55'])).
% 0.47/0.72  thf('223', plain,
% 0.47/0.72      ((m1_subset_1 @ sk_C @ 
% 0.47/0.72        (k1_zfmisc_1 @ 
% 0.47/0.72         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.72      inference('demod', [status(thm)], ['221', '222'])).
% 0.47/0.72  thf(d4_tops_2, axiom,
% 0.47/0.72    (![A:$i,B:$i,C:$i]:
% 0.47/0.72     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.47/0.72         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.72       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.47/0.72         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.47/0.72  thf('224', plain,
% 0.47/0.72      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.47/0.72         (((k2_relset_1 @ X38 @ X37 @ X39) != (X37))
% 0.47/0.72          | ~ (v2_funct_1 @ X39)
% 0.47/0.72          | ((k2_tops_2 @ X38 @ X37 @ X39) = (k2_funct_1 @ X39))
% 0.47/0.72          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 0.47/0.72          | ~ (v1_funct_2 @ X39 @ X38 @ X37)
% 0.47/0.72          | ~ (v1_funct_1 @ X39))),
% 0.47/0.72      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.47/0.72  thf('225', plain,
% 0.47/0.72      ((~ (v1_funct_1 @ sk_C)
% 0.47/0.72        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.47/0.72        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.47/0.72            = (k2_funct_1 @ sk_C))
% 0.47/0.72        | ~ (v2_funct_1 @ sk_C)
% 0.47/0.72        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.47/0.72            != (u1_struct_0 @ sk_B)))),
% 0.47/0.72      inference('sup-', [status(thm)], ['223', '224'])).
% 0.47/0.72  thf('226', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.72  thf('227', plain,
% 0.47/0.72      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.47/0.72      inference('demod', [status(thm)], ['64', '65'])).
% 0.47/0.72  thf('228', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.47/0.72      inference('demod', [status(thm)], ['49', '52', '55'])).
% 0.47/0.72  thf('229', plain,
% 0.47/0.72      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.47/0.72      inference('demod', [status(thm)], ['227', '228'])).
% 0.47/0.72  thf('230', plain, ((v2_funct_1 @ sk_C)),
% 0.47/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.72  thf('231', plain,
% 0.47/0.72      ((m1_subset_1 @ sk_C @ 
% 0.47/0.72        (k1_zfmisc_1 @ 
% 0.47/0.72         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.47/0.72      inference('demod', [status(thm)], ['3', '4'])).
% 0.47/0.72  thf('232', plain,
% 0.47/0.72      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.47/0.72         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 0.47/0.72          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.47/0.72      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.47/0.72  thf('233', plain,
% 0.47/0.72      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.47/0.72         = (k2_relat_1 @ sk_C))),
% 0.47/0.72      inference('sup-', [status(thm)], ['231', '232'])).
% 0.47/0.72  thf('234', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.47/0.72      inference('demod', [status(thm)], ['49', '52', '55'])).
% 0.47/0.72  thf('235', plain,
% 0.47/0.72      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.47/0.72         = (k2_relat_1 @ sk_C))),
% 0.47/0.72      inference('demod', [status(thm)], ['233', '234'])).
% 0.47/0.72  thf('236', plain,
% 0.47/0.72      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.47/0.72          = (k2_funct_1 @ sk_C))
% 0.47/0.72        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.47/0.72      inference('demod', [status(thm)], ['225', '226', '229', '230', '235'])).
% 0.47/0.72  thf('237', plain,
% 0.47/0.72      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.47/0.72        | ~ (l1_struct_0 @ sk_B)
% 0.47/0.72        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.47/0.72            = (k2_funct_1 @ sk_C)))),
% 0.47/0.72      inference('sup-', [status(thm)], ['220', '236'])).
% 0.47/0.72  thf('238', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.47/0.72      inference('sup+', [status(thm)], ['11', '12'])).
% 0.47/0.72  thf('239', plain, ((l1_struct_0 @ sk_B)),
% 0.47/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.72  thf('240', plain,
% 0.47/0.72      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.47/0.72        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.47/0.72            = (k2_funct_1 @ sk_C)))),
% 0.47/0.72      inference('demod', [status(thm)], ['237', '238', '239'])).
% 0.47/0.72  thf('241', plain,
% 0.47/0.72      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.47/0.72         = (k2_funct_1 @ sk_C))),
% 0.47/0.72      inference('simplify', [status(thm)], ['240'])).
% 0.47/0.72  thf('242', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.47/0.72      inference('sup+', [status(thm)], ['11', '12'])).
% 0.47/0.72  thf('243', plain,
% 0.47/0.72      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.47/0.72          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.47/0.72         <= (~
% 0.47/0.72             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.72                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.72                = (k2_struct_0 @ sk_B))))),
% 0.47/0.72      inference('demod', [status(thm)],
% 0.47/0.72                ['209', '210', '218', '219', '241', '242'])).
% 0.47/0.72  thf('244', plain,
% 0.47/0.72      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.47/0.72        (k1_zfmisc_1 @ 
% 0.47/0.72         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.47/0.72      inference('simplify', [status(thm)], ['89'])).
% 0.47/0.72  thf('245', plain,
% 0.47/0.72      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.47/0.72         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 0.47/0.72          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.47/0.72      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.47/0.72  thf('246', plain,
% 0.47/0.72      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.47/0.72         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.47/0.72      inference('sup-', [status(thm)], ['244', '245'])).
% 0.47/0.72  thf('247', plain,
% 0.47/0.72      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.47/0.72      inference('demod', [status(thm)], ['193', '194', '195', '196'])).
% 0.47/0.72  thf('248', plain,
% 0.47/0.72      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.47/0.72         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.47/0.72      inference('demod', [status(thm)], ['246', '247'])).
% 0.47/0.72  thf('249', plain,
% 0.47/0.72      ((m1_subset_1 @ sk_C @ 
% 0.47/0.72        (k1_zfmisc_1 @ 
% 0.47/0.72         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.47/0.72      inference('demod', [status(thm)], ['14', '56'])).
% 0.47/0.72  thf('250', plain,
% 0.47/0.72      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.47/0.72         (((k2_relset_1 @ X38 @ X37 @ X39) != (X37))
% 0.47/0.72          | ~ (v2_funct_1 @ X39)
% 0.47/0.72          | ((k2_tops_2 @ X38 @ X37 @ X39) = (k2_funct_1 @ X39))
% 0.47/0.72          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 0.47/0.72          | ~ (v1_funct_2 @ X39 @ X38 @ X37)
% 0.47/0.72          | ~ (v1_funct_1 @ X39))),
% 0.47/0.72      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.47/0.72  thf('251', plain,
% 0.47/0.72      ((~ (v1_funct_1 @ sk_C)
% 0.47/0.72        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.47/0.72        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.47/0.72            = (k2_funct_1 @ sk_C))
% 0.47/0.72        | ~ (v2_funct_1 @ sk_C)
% 0.47/0.72        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.47/0.72            != (k2_relat_1 @ sk_C)))),
% 0.47/0.72      inference('sup-', [status(thm)], ['249', '250'])).
% 0.47/0.72  thf('252', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.72  thf('253', plain,
% 0.47/0.72      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.47/0.72      inference('demod', [status(thm)], ['71', '72'])).
% 0.47/0.72  thf('254', plain, ((v2_funct_1 @ sk_C)),
% 0.47/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.72  thf('255', plain,
% 0.47/0.72      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.47/0.72         = (k2_relat_1 @ sk_C))),
% 0.47/0.72      inference('demod', [status(thm)], ['85', '86'])).
% 0.47/0.72  thf('256', plain,
% 0.47/0.72      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.47/0.72          = (k2_funct_1 @ sk_C))
% 0.47/0.72        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.47/0.72      inference('demod', [status(thm)], ['251', '252', '253', '254', '255'])).
% 0.47/0.72  thf('257', plain,
% 0.47/0.72      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.47/0.72         = (k2_funct_1 @ sk_C))),
% 0.47/0.72      inference('simplify', [status(thm)], ['256'])).
% 0.47/0.72  thf('258', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.47/0.72      inference('sup+', [status(thm)], ['11', '12'])).
% 0.47/0.72  thf('259', plain,
% 0.47/0.72      (![X35 : $i]:
% 0.47/0.72         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.47/0.72      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.72  thf('260', plain,
% 0.47/0.72      (![X35 : $i]:
% 0.47/0.72         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.47/0.72      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.47/0.72  thf('261', plain,
% 0.47/0.72      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.72          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.72          != (k2_struct_0 @ sk_A)))
% 0.47/0.72         <= (~
% 0.47/0.72             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.72                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.72                = (k2_struct_0 @ sk_A))))),
% 0.47/0.72      inference('split', [status(esa)], ['205'])).
% 0.47/0.72  thf('262', plain,
% 0.47/0.72      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.72           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.72           != (k2_struct_0 @ sk_A))
% 0.47/0.72         | ~ (l1_struct_0 @ sk_B)))
% 0.47/0.72         <= (~
% 0.47/0.72             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.72                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.72                = (k2_struct_0 @ sk_A))))),
% 0.47/0.72      inference('sup-', [status(thm)], ['260', '261'])).
% 0.47/0.72  thf('263', plain, ((l1_struct_0 @ sk_B)),
% 0.47/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.72  thf('264', plain,
% 0.47/0.72      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.72          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.72          != (k2_struct_0 @ sk_A)))
% 0.47/0.72         <= (~
% 0.47/0.72             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.72                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.72                = (k2_struct_0 @ sk_A))))),
% 0.47/0.72      inference('demod', [status(thm)], ['262', '263'])).
% 0.47/0.72  thf('265', plain,
% 0.47/0.72      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.72           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.47/0.72           != (k2_struct_0 @ sk_A))
% 0.47/0.72         | ~ (l1_struct_0 @ sk_B)))
% 0.47/0.72         <= (~
% 0.47/0.72             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.72                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.72                = (k2_struct_0 @ sk_A))))),
% 0.47/0.72      inference('sup-', [status(thm)], ['259', '264'])).
% 0.47/0.72  thf('266', plain, ((l1_struct_0 @ sk_B)),
% 0.47/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.72  thf('267', plain,
% 0.47/0.72      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.72          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.47/0.72          != (k2_struct_0 @ sk_A)))
% 0.47/0.72         <= (~
% 0.47/0.72             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.72                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.72                = (k2_struct_0 @ sk_A))))),
% 0.47/0.72      inference('demod', [status(thm)], ['265', '266'])).
% 0.47/0.72  thf('268', plain,
% 0.47/0.72      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.72          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.47/0.72          != (k2_struct_0 @ sk_A)))
% 0.47/0.72         <= (~
% 0.47/0.72             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.72                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.72                = (k2_struct_0 @ sk_A))))),
% 0.47/0.72      inference('sup-', [status(thm)], ['258', '267'])).
% 0.47/0.72  thf('269', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.47/0.72      inference('sup+', [status(thm)], ['11', '12'])).
% 0.47/0.72  thf('270', plain,
% 0.47/0.72      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.72          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.47/0.72          != (k2_struct_0 @ sk_A)))
% 0.47/0.72         <= (~
% 0.47/0.72             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.72                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.72                = (k2_struct_0 @ sk_A))))),
% 0.47/0.72      inference('demod', [status(thm)], ['268', '269'])).
% 0.47/0.72  thf('271', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.47/0.72      inference('demod', [status(thm)], ['213', '214', '217'])).
% 0.47/0.72  thf('272', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.47/0.72      inference('demod', [status(thm)], ['213', '214', '217'])).
% 0.47/0.72  thf('273', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.47/0.72      inference('demod', [status(thm)], ['49', '52', '55'])).
% 0.47/0.72  thf('274', plain,
% 0.47/0.72      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.47/0.72          (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.47/0.72          != (k1_relat_1 @ sk_C)))
% 0.47/0.72         <= (~
% 0.47/0.72             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.72                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.72                = (k2_struct_0 @ sk_A))))),
% 0.47/0.72      inference('demod', [status(thm)], ['270', '271', '272', '273'])).
% 0.47/0.72  thf('275', plain,
% 0.47/0.72      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.47/0.72          (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 0.47/0.72         <= (~
% 0.47/0.72             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.72                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.72                = (k2_struct_0 @ sk_A))))),
% 0.47/0.72      inference('sup-', [status(thm)], ['257', '274'])).
% 0.47/0.72  thf('276', plain,
% 0.47/0.72      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))
% 0.47/0.72         <= (~
% 0.47/0.72             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.72                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.72                = (k2_struct_0 @ sk_A))))),
% 0.47/0.72      inference('sup-', [status(thm)], ['248', '275'])).
% 0.47/0.72  thf('277', plain,
% 0.47/0.72      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.72          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.72          = (k2_struct_0 @ sk_A)))),
% 0.47/0.72      inference('simplify', [status(thm)], ['276'])).
% 0.47/0.72  thf('278', plain,
% 0.47/0.72      (~
% 0.47/0.72       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.72          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.72          = (k2_struct_0 @ sk_B))) | 
% 0.47/0.72       ~
% 0.47/0.72       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.72          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.72          = (k2_struct_0 @ sk_A)))),
% 0.47/0.72      inference('split', [status(esa)], ['205'])).
% 0.47/0.72  thf('279', plain,
% 0.47/0.72      (~
% 0.47/0.72       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.47/0.72          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.47/0.72          = (k2_struct_0 @ sk_B)))),
% 0.47/0.72      inference('sat_resolution*', [status(thm)], ['277', '278'])).
% 0.47/0.72  thf('280', plain,
% 0.47/0.72      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.47/0.72         (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C))),
% 0.47/0.72      inference('simpl_trail', [status(thm)], ['243', '279'])).
% 0.47/0.72  thf('281', plain, ($false),
% 0.47/0.72      inference('simplify_reflect-', [status(thm)], ['203', '280'])).
% 0.47/0.72  
% 0.47/0.72  % SZS output end Refutation
% 0.47/0.72  
% 0.47/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
