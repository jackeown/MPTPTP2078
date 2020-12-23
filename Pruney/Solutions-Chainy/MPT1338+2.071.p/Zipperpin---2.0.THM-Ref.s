%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8oh7tawmLB

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:59 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :  292 (3126 expanded)
%              Number of leaves         :   51 ( 934 expanded)
%              Depth                    :   32
%              Number of atoms          : 2556 (78388 expanded)
%              Number of equality atoms :  186 (3971 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k3_relset_1_type,type,(
    k3_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('1',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('2',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('5',plain,(
    ! [X36: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('6',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X6: $i] :
      ( ( ( k10_relat_1 @ X6 @ ( k2_relat_1 @ X6 ) )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('12',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('20',plain,(
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

thf('21',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( v1_partfun1 @ X27 @ X28 )
      | ~ ( v1_funct_2 @ X27 @ X28 @ X29 )
      | ~ ( v1_funct_1 @ X27 )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('22',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('26',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v1_partfun1 @ X31 @ X30 )
      | ( ( k1_relat_1 @ X31 )
        = X30 )
      | ~ ( v4_relat_1 @ X31 @ X30 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('27',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('29',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('31',plain,(
    ! [X3: $i,X4: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('32',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','32','35'])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['19','36'])).

thf('38',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('39',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('42',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['18','42'])).

thf(dt_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k3_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) )).

thf('44',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( m1_subset_1 @ ( k3_relset_1 @ X15 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_relset_1])).

thf('45',plain,(
    m1_subset_1 @ ( k3_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k3_relset_1 @ A @ B @ C )
        = ( k4_relat_1 @ C ) ) ) )).

thf('48',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k3_relset_1 @ X25 @ X26 @ X24 )
        = ( k4_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_relset_1])).

thf('49',plain,
    ( ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['46','49'])).

thf('51',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('52',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('55',plain,
    ( ( k3_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['45','55'])).

thf('57',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( v1_partfun1 @ X27 @ X28 )
      | ~ ( v1_funct_2 @ X27 @ X28 @ X29 )
      | ~ ( v1_funct_1 @ X27 )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('58',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('60',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k2_funct_1 @ X8 )
        = ( k4_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('61',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['30','31'])).

thf('63',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('65',plain,(
    ! [X9: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('66',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['30','31'])).

thf('68',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['18','42'])).

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

thf('71',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v2_funct_1 @ X32 )
      | ( ( k2_relset_1 @ X34 @ X33 @ X32 )
       != X33 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X32 ) @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X34 @ X33 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('72',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('76',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['74','79'])).

thf('81',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('84',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('86',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('87',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( v1_partfun1 @ X27 @ X28 )
      | ~ ( v1_funct_2 @ X27 @ X28 @ X29 )
      | ~ ( v1_funct_1 @ X27 )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('92',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('95',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('96',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v1_partfun1 @ X31 @ X30 )
      | ( ( k1_relat_1 @ X31 )
        = X30 )
      | ~ ( v4_relat_1 @ X31 @ X30 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('97',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['30','31'])).

thf('99',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('100',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v4_relat_1 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('101',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['97','98','101'])).

thf('103',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['85','102'])).

thf('104',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('105',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('108',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['84','108'])).

thf('110',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('111',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('112',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('113',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('118',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('119',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('120',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['111','119'])).

thf('121',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('124',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['72','73','109','110','124','125'])).

thf('127',plain,(
    v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['58','69','127'])).

thf('129',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v1_partfun1 @ X31 @ X30 )
      | ( ( k1_relat_1 @ X31 )
        = X30 )
      | ~ ( v4_relat_1 @ X31 @ X30 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('130',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v4_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('132',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('133',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf('134',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['30','31'])).

thf('135',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['133','134','135'])).

thf('137',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('138',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( m1_subset_1 @ ( k3_relset_1 @ X15 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_relset_1])).

thf('140',plain,(
    m1_subset_1 @ ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,
    ( ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('142',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('144',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v4_relat_1 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('146',plain,(
    v4_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,
    ( ( v4_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['137','146'])).

thf('148',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('149',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v4_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['147','148','149'])).

thf('151',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['130','136','150'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('152',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('153',plain,
    ( ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('154',plain,(
    ! [X5: $i] :
      ( ( ( k9_relat_1 @ X5 @ ( k1_relat_1 @ X5 ) )
        = ( k2_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('155',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf(t155_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ B @ A )
          = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('156',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k10_relat_1 @ X10 @ X11 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X10 ) @ X11 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ sk_C @ X0 )
        = ( k9_relat_1 @ ( k4_relat_1 @ sk_C ) @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['155','156'])).

thf('158',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['30','31'])).

thf('159',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ sk_C @ X0 )
      = ( k9_relat_1 @ ( k4_relat_1 @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['157','158','159','160'])).

thf('162',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['154','161'])).

thf('163',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['133','134','135'])).

thf('164',plain,
    ( ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('165',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['153','164'])).

thf('166',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['11','165'])).

thf('167',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['30','31'])).

thf('168',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('170',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['170'])).

thf('172',plain,
    ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['169','171'])).

thf('173',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['172','173'])).

thf('175',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('176',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('177',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('178',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['18','42'])).

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

thf('179',plain,(
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

thf('180',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['84','108'])).

thf('183',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('184',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('186',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['180','181','182','183','184','185'])).

thf('187',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['186'])).

thf('188',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('189',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('190',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k4_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('192',plain,
    ( ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['174','175','176','177','187','190','191'])).

thf('193',plain,
    ( ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('194',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['186'])).

thf('195',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('196',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('197',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('198',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['170'])).

thf('199',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['197','198'])).

thf('200',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['199','200'])).

thf('202',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['196','201'])).

thf('203',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['202','203'])).

thf('205',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['195','204'])).

thf('206',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['205','206'])).

thf('208',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('209',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('210',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('211',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('212',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['207','208','209','210','211'])).

thf('213',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k4_relat_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['194','212'])).

thf('214',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['142','143'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('215',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('216',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k4_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['214','215'])).

thf('217',plain,
    ( ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['213','216'])).

thf('218',plain,
    ( ( ( ( k2_relat_1 @ sk_C )
       != ( k2_relat_1 @ sk_C ) )
      | ( ( k1_relat_1 @ sk_C )
        = k1_xboole_0 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['193','217'])).

thf('219',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['218'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('220',plain,(
    ! [X7: $i] :
      ( ( ( k1_relat_1 @ X7 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X7 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('221',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ( ( k2_relat_1 @ sk_C )
        = k1_xboole_0 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['219','220'])).

thf('222',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['30','31'])).

thf('223',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_C )
        = k1_xboole_0 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['221','222'])).

thf('224',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['223'])).

thf('225',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('226',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['224','225'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('227',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('228',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['226','227'])).

thf('229',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['170'])).

thf('230',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['228','229'])).

thf('231',plain,(
    ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['192','230'])).

thf('232',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['168','231'])).

thf('233',plain,(
    ! [X7: $i] :
      ( ( ( k1_relat_1 @ X7 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X7 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('234',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['232','233'])).

thf('235',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['30','31'])).

thf('236',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['234','235'])).

thf('237',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['236'])).

thf('238',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('239',plain,(
    $false ),
    inference(demod,[status(thm)],['10','237','238'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8oh7tawmLB
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:29:18 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.54/0.73  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.54/0.73  % Solved by: fo/fo7.sh
% 0.54/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.73  % done 501 iterations in 0.286s
% 0.54/0.73  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.54/0.73  % SZS output start Refutation
% 0.54/0.73  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.54/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.73  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.54/0.73  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.54/0.73  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.54/0.73  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.54/0.73  thf(sk_C_type, type, sk_C: $i).
% 0.54/0.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.54/0.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.54/0.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.54/0.73  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.54/0.73  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.54/0.73  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.54/0.73  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.54/0.73  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.54/0.73  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.54/0.73  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.54/0.73  thf(k3_relset_1_type, type, k3_relset_1: $i > $i > $i > $i).
% 0.54/0.73  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.54/0.73  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.54/0.73  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.54/0.73  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.54/0.73  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.54/0.73  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.54/0.73  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.54/0.73  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.54/0.73  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.54/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.54/0.73  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.54/0.73  thf(t62_tops_2, conjecture,
% 0.54/0.73    (![A:$i]:
% 0.54/0.73     ( ( l1_struct_0 @ A ) =>
% 0.54/0.73       ( ![B:$i]:
% 0.54/0.73         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.54/0.73           ( ![C:$i]:
% 0.54/0.73             ( ( ( v1_funct_1 @ C ) & 
% 0.54/0.73                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.54/0.73                 ( m1_subset_1 @
% 0.54/0.73                   C @ 
% 0.54/0.73                   ( k1_zfmisc_1 @
% 0.54/0.73                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.54/0.73               ( ( ( ( k2_relset_1 @
% 0.54/0.73                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.54/0.73                     ( k2_struct_0 @ B ) ) & 
% 0.54/0.73                   ( v2_funct_1 @ C ) ) =>
% 0.54/0.73                 ( ( ( k1_relset_1 @
% 0.54/0.73                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.54/0.73                       ( k2_tops_2 @
% 0.54/0.73                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.54/0.73                     ( k2_struct_0 @ B ) ) & 
% 0.54/0.73                   ( ( k2_relset_1 @
% 0.54/0.73                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.54/0.73                       ( k2_tops_2 @
% 0.54/0.73                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.54/0.73                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.54/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.73    (~( ![A:$i]:
% 0.54/0.73        ( ( l1_struct_0 @ A ) =>
% 0.54/0.73          ( ![B:$i]:
% 0.54/0.73            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.54/0.73              ( ![C:$i]:
% 0.54/0.73                ( ( ( v1_funct_1 @ C ) & 
% 0.54/0.73                    ( v1_funct_2 @
% 0.54/0.73                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.54/0.73                    ( m1_subset_1 @
% 0.54/0.73                      C @ 
% 0.54/0.73                      ( k1_zfmisc_1 @
% 0.54/0.73                        ( k2_zfmisc_1 @
% 0.54/0.73                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.54/0.73                  ( ( ( ( k2_relset_1 @
% 0.54/0.73                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.54/0.73                        ( k2_struct_0 @ B ) ) & 
% 0.54/0.73                      ( v2_funct_1 @ C ) ) =>
% 0.54/0.73                    ( ( ( k1_relset_1 @
% 0.54/0.73                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.54/0.73                          ( k2_tops_2 @
% 0.54/0.73                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.54/0.73                        ( k2_struct_0 @ B ) ) & 
% 0.54/0.73                      ( ( k2_relset_1 @
% 0.54/0.73                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.54/0.73                          ( k2_tops_2 @
% 0.54/0.73                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.54/0.73                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.54/0.73    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 0.54/0.73  thf('0', plain,
% 0.54/0.73      ((m1_subset_1 @ sk_C @ 
% 0.54/0.73        (k1_zfmisc_1 @ 
% 0.54/0.73         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf(redefinition_k2_relset_1, axiom,
% 0.54/0.73    (![A:$i,B:$i,C:$i]:
% 0.54/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.73       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.54/0.73  thf('1', plain,
% 0.54/0.73      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.54/0.73         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 0.54/0.73          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.54/0.73      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.54/0.73  thf('2', plain,
% 0.54/0.73      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.54/0.73         = (k2_relat_1 @ sk_C))),
% 0.54/0.73      inference('sup-', [status(thm)], ['0', '1'])).
% 0.54/0.73  thf('3', plain,
% 0.54/0.73      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.54/0.73         = (k2_struct_0 @ sk_B))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('4', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.54/0.73      inference('sup+', [status(thm)], ['2', '3'])).
% 0.54/0.73  thf(fc5_struct_0, axiom,
% 0.54/0.73    (![A:$i]:
% 0.54/0.73     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.54/0.73       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.54/0.73  thf('5', plain,
% 0.54/0.73      (![X36 : $i]:
% 0.54/0.73         (~ (v1_xboole_0 @ (k2_struct_0 @ X36))
% 0.54/0.73          | ~ (l1_struct_0 @ X36)
% 0.54/0.73          | (v2_struct_0 @ X36))),
% 0.54/0.73      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.54/0.73  thf('6', plain,
% 0.54/0.73      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.54/0.73        | (v2_struct_0 @ sk_B)
% 0.54/0.73        | ~ (l1_struct_0 @ sk_B))),
% 0.54/0.73      inference('sup-', [status(thm)], ['4', '5'])).
% 0.54/0.73  thf('7', plain, ((l1_struct_0 @ sk_B)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('8', plain,
% 0.54/0.73      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.54/0.73      inference('demod', [status(thm)], ['6', '7'])).
% 0.54/0.73  thf('9', plain, (~ (v2_struct_0 @ sk_B)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('10', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.54/0.73      inference('clc', [status(thm)], ['8', '9'])).
% 0.54/0.73  thf(t169_relat_1, axiom,
% 0.54/0.73    (![A:$i]:
% 0.54/0.73     ( ( v1_relat_1 @ A ) =>
% 0.54/0.73       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.54/0.73  thf('11', plain,
% 0.54/0.73      (![X6 : $i]:
% 0.54/0.73         (((k10_relat_1 @ X6 @ (k2_relat_1 @ X6)) = (k1_relat_1 @ X6))
% 0.54/0.73          | ~ (v1_relat_1 @ X6))),
% 0.54/0.73      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.54/0.73  thf(d3_struct_0, axiom,
% 0.54/0.73    (![A:$i]:
% 0.54/0.73     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.54/0.73  thf('12', plain,
% 0.54/0.73      (![X35 : $i]:
% 0.54/0.73         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.54/0.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.54/0.73  thf('13', plain,
% 0.54/0.73      ((m1_subset_1 @ sk_C @ 
% 0.54/0.73        (k1_zfmisc_1 @ 
% 0.54/0.73         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('14', plain,
% 0.54/0.73      (((m1_subset_1 @ sk_C @ 
% 0.54/0.73         (k1_zfmisc_1 @ 
% 0.54/0.73          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.54/0.73        | ~ (l1_struct_0 @ sk_B))),
% 0.54/0.73      inference('sup+', [status(thm)], ['12', '13'])).
% 0.54/0.73  thf('15', plain, ((l1_struct_0 @ sk_B)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('16', plain,
% 0.54/0.73      ((m1_subset_1 @ sk_C @ 
% 0.54/0.73        (k1_zfmisc_1 @ 
% 0.54/0.73         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.54/0.73      inference('demod', [status(thm)], ['14', '15'])).
% 0.54/0.73  thf('17', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.54/0.73      inference('sup+', [status(thm)], ['2', '3'])).
% 0.54/0.73  thf('18', plain,
% 0.54/0.73      ((m1_subset_1 @ sk_C @ 
% 0.54/0.73        (k1_zfmisc_1 @ 
% 0.54/0.73         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.54/0.73      inference('demod', [status(thm)], ['16', '17'])).
% 0.54/0.73  thf('19', plain,
% 0.54/0.73      (![X35 : $i]:
% 0.54/0.73         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.54/0.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.54/0.73  thf('20', plain,
% 0.54/0.73      ((m1_subset_1 @ sk_C @ 
% 0.54/0.73        (k1_zfmisc_1 @ 
% 0.54/0.73         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf(cc5_funct_2, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.54/0.73       ( ![C:$i]:
% 0.54/0.73         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.73           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.54/0.73             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.54/0.73  thf('21', plain,
% 0.54/0.73      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.54/0.73         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.54/0.73          | (v1_partfun1 @ X27 @ X28)
% 0.54/0.73          | ~ (v1_funct_2 @ X27 @ X28 @ X29)
% 0.54/0.73          | ~ (v1_funct_1 @ X27)
% 0.54/0.73          | (v1_xboole_0 @ X29))),
% 0.54/0.73      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.54/0.73  thf('22', plain,
% 0.54/0.73      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.54/0.73        | ~ (v1_funct_1 @ sk_C)
% 0.54/0.73        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.54/0.73        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.54/0.73      inference('sup-', [status(thm)], ['20', '21'])).
% 0.54/0.73  thf('23', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('24', plain,
% 0.54/0.73      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('25', plain,
% 0.54/0.73      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.54/0.73        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.54/0.73      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.54/0.73  thf(d4_partfun1, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.54/0.73       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.54/0.73  thf('26', plain,
% 0.54/0.73      (![X30 : $i, X31 : $i]:
% 0.54/0.73         (~ (v1_partfun1 @ X31 @ X30)
% 0.54/0.73          | ((k1_relat_1 @ X31) = (X30))
% 0.54/0.73          | ~ (v4_relat_1 @ X31 @ X30)
% 0.54/0.73          | ~ (v1_relat_1 @ X31))),
% 0.54/0.73      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.54/0.73  thf('27', plain,
% 0.54/0.73      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.54/0.73        | ~ (v1_relat_1 @ sk_C)
% 0.54/0.73        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.54/0.73        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.54/0.73      inference('sup-', [status(thm)], ['25', '26'])).
% 0.54/0.73  thf('28', plain,
% 0.54/0.73      ((m1_subset_1 @ sk_C @ 
% 0.54/0.73        (k1_zfmisc_1 @ 
% 0.54/0.73         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf(cc2_relat_1, axiom,
% 0.54/0.73    (![A:$i]:
% 0.54/0.73     ( ( v1_relat_1 @ A ) =>
% 0.54/0.73       ( ![B:$i]:
% 0.54/0.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.54/0.73  thf('29', plain,
% 0.54/0.73      (![X1 : $i, X2 : $i]:
% 0.54/0.73         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.54/0.73          | (v1_relat_1 @ X1)
% 0.54/0.73          | ~ (v1_relat_1 @ X2))),
% 0.54/0.73      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.54/0.73  thf('30', plain,
% 0.54/0.73      ((~ (v1_relat_1 @ 
% 0.54/0.73           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.54/0.73        | (v1_relat_1 @ sk_C))),
% 0.54/0.73      inference('sup-', [status(thm)], ['28', '29'])).
% 0.54/0.73  thf(fc6_relat_1, axiom,
% 0.54/0.73    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.54/0.73  thf('31', plain,
% 0.54/0.73      (![X3 : $i, X4 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X3 @ X4))),
% 0.54/0.73      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.54/0.73  thf('32', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.73      inference('demod', [status(thm)], ['30', '31'])).
% 0.54/0.73  thf('33', plain,
% 0.54/0.73      ((m1_subset_1 @ sk_C @ 
% 0.54/0.73        (k1_zfmisc_1 @ 
% 0.54/0.73         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf(cc2_relset_1, axiom,
% 0.54/0.73    (![A:$i,B:$i,C:$i]:
% 0.54/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.73       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.54/0.73  thf('34', plain,
% 0.54/0.73      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.54/0.73         ((v4_relat_1 @ X12 @ X13)
% 0.54/0.73          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.54/0.73      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.54/0.73  thf('35', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.54/0.73      inference('sup-', [status(thm)], ['33', '34'])).
% 0.54/0.73  thf('36', plain,
% 0.54/0.73      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.54/0.73        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.54/0.73      inference('demod', [status(thm)], ['27', '32', '35'])).
% 0.54/0.73  thf('37', plain,
% 0.54/0.73      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.54/0.73        | ~ (l1_struct_0 @ sk_B)
% 0.54/0.73        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.54/0.73      inference('sup+', [status(thm)], ['19', '36'])).
% 0.54/0.73  thf('38', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.54/0.73      inference('sup+', [status(thm)], ['2', '3'])).
% 0.54/0.73  thf('39', plain, ((l1_struct_0 @ sk_B)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('40', plain,
% 0.54/0.73      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.54/0.73        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.54/0.73      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.54/0.73  thf('41', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.54/0.73      inference('clc', [status(thm)], ['8', '9'])).
% 0.54/0.73  thf('42', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.54/0.73      inference('clc', [status(thm)], ['40', '41'])).
% 0.54/0.73  thf('43', plain,
% 0.54/0.73      ((m1_subset_1 @ sk_C @ 
% 0.54/0.73        (k1_zfmisc_1 @ 
% 0.54/0.73         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.54/0.73      inference('demod', [status(thm)], ['18', '42'])).
% 0.54/0.73  thf(dt_k3_relset_1, axiom,
% 0.54/0.73    (![A:$i,B:$i,C:$i]:
% 0.54/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.73       ( m1_subset_1 @
% 0.54/0.73         ( k3_relset_1 @ A @ B @ C ) @ 
% 0.54/0.73         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ))).
% 0.54/0.73  thf('44', plain,
% 0.54/0.73      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.54/0.73         ((m1_subset_1 @ (k3_relset_1 @ X15 @ X16 @ X17) @ 
% 0.54/0.73           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X15)))
% 0.54/0.73          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.54/0.73      inference('cnf', [status(esa)], [dt_k3_relset_1])).
% 0.54/0.73  thf('45', plain,
% 0.54/0.73      ((m1_subset_1 @ 
% 0.54/0.73        (k3_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C) @ 
% 0.54/0.73        (k1_zfmisc_1 @ 
% 0.54/0.73         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.54/0.73      inference('sup-', [status(thm)], ['43', '44'])).
% 0.54/0.73  thf('46', plain,
% 0.54/0.73      (![X35 : $i]:
% 0.54/0.73         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.54/0.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.54/0.73  thf('47', plain,
% 0.54/0.73      ((m1_subset_1 @ sk_C @ 
% 0.54/0.73        (k1_zfmisc_1 @ 
% 0.54/0.73         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf(redefinition_k3_relset_1, axiom,
% 0.54/0.73    (![A:$i,B:$i,C:$i]:
% 0.54/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.73       ( ( k3_relset_1 @ A @ B @ C ) = ( k4_relat_1 @ C ) ) ))).
% 0.54/0.73  thf('48', plain,
% 0.54/0.73      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.54/0.73         (((k3_relset_1 @ X25 @ X26 @ X24) = (k4_relat_1 @ X24))
% 0.54/0.73          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.54/0.73      inference('cnf', [status(esa)], [redefinition_k3_relset_1])).
% 0.54/0.73  thf('49', plain,
% 0.54/0.73      (((k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.54/0.73         = (k4_relat_1 @ sk_C))),
% 0.54/0.73      inference('sup-', [status(thm)], ['47', '48'])).
% 0.54/0.73  thf('50', plain,
% 0.54/0.73      ((((k3_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.54/0.73          = (k4_relat_1 @ sk_C))
% 0.54/0.73        | ~ (l1_struct_0 @ sk_B))),
% 0.54/0.73      inference('sup+', [status(thm)], ['46', '49'])).
% 0.54/0.73  thf('51', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.54/0.73      inference('sup+', [status(thm)], ['2', '3'])).
% 0.54/0.73  thf('52', plain, ((l1_struct_0 @ sk_B)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('53', plain,
% 0.54/0.73      (((k3_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.54/0.73         = (k4_relat_1 @ sk_C))),
% 0.54/0.73      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.54/0.73  thf('54', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.54/0.73      inference('clc', [status(thm)], ['40', '41'])).
% 0.54/0.73  thf('55', plain,
% 0.54/0.73      (((k3_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.54/0.73         = (k4_relat_1 @ sk_C))),
% 0.54/0.73      inference('demod', [status(thm)], ['53', '54'])).
% 0.54/0.73  thf('56', plain,
% 0.54/0.73      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.54/0.73        (k1_zfmisc_1 @ 
% 0.54/0.73         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.54/0.73      inference('demod', [status(thm)], ['45', '55'])).
% 0.54/0.73  thf('57', plain,
% 0.54/0.73      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.54/0.73         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.54/0.73          | (v1_partfun1 @ X27 @ X28)
% 0.54/0.73          | ~ (v1_funct_2 @ X27 @ X28 @ X29)
% 0.54/0.73          | ~ (v1_funct_1 @ X27)
% 0.54/0.73          | (v1_xboole_0 @ X29))),
% 0.54/0.73      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.54/0.73  thf('58', plain,
% 0.54/0.73      (((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 0.54/0.73        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C))
% 0.54/0.73        | ~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.54/0.73             (k1_relat_1 @ sk_C))
% 0.54/0.73        | (v1_partfun1 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C)))),
% 0.54/0.73      inference('sup-', [status(thm)], ['56', '57'])).
% 0.54/0.73  thf('59', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf(d9_funct_1, axiom,
% 0.54/0.73    (![A:$i]:
% 0.54/0.73     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.54/0.73       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.54/0.73  thf('60', plain,
% 0.54/0.73      (![X8 : $i]:
% 0.54/0.73         (~ (v2_funct_1 @ X8)
% 0.54/0.73          | ((k2_funct_1 @ X8) = (k4_relat_1 @ X8))
% 0.54/0.73          | ~ (v1_funct_1 @ X8)
% 0.54/0.73          | ~ (v1_relat_1 @ X8))),
% 0.54/0.73      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.54/0.73  thf('61', plain,
% 0.54/0.73      ((~ (v1_relat_1 @ sk_C)
% 0.54/0.73        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 0.54/0.73        | ~ (v2_funct_1 @ sk_C))),
% 0.54/0.73      inference('sup-', [status(thm)], ['59', '60'])).
% 0.54/0.73  thf('62', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.73      inference('demod', [status(thm)], ['30', '31'])).
% 0.54/0.73  thf('63', plain, ((v2_funct_1 @ sk_C)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('64', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.54/0.73      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.54/0.73  thf(dt_k2_funct_1, axiom,
% 0.54/0.73    (![A:$i]:
% 0.54/0.73     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.54/0.73       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.54/0.73         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.54/0.73  thf('65', plain,
% 0.54/0.73      (![X9 : $i]:
% 0.54/0.73         ((v1_funct_1 @ (k2_funct_1 @ X9))
% 0.54/0.73          | ~ (v1_funct_1 @ X9)
% 0.54/0.73          | ~ (v1_relat_1 @ X9))),
% 0.54/0.73      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.54/0.73  thf('66', plain,
% 0.54/0.73      (((v1_funct_1 @ (k4_relat_1 @ sk_C))
% 0.54/0.73        | ~ (v1_relat_1 @ sk_C)
% 0.54/0.73        | ~ (v1_funct_1 @ sk_C))),
% 0.54/0.73      inference('sup+', [status(thm)], ['64', '65'])).
% 0.54/0.73  thf('67', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.73      inference('demod', [status(thm)], ['30', '31'])).
% 0.54/0.73  thf('68', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('69', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.54/0.73      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.54/0.73  thf('70', plain,
% 0.54/0.73      ((m1_subset_1 @ sk_C @ 
% 0.54/0.73        (k1_zfmisc_1 @ 
% 0.54/0.73         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.54/0.73      inference('demod', [status(thm)], ['18', '42'])).
% 0.54/0.73  thf(t31_funct_2, axiom,
% 0.54/0.73    (![A:$i,B:$i,C:$i]:
% 0.54/0.73     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.54/0.73         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.54/0.73       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.54/0.73         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.54/0.73           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.54/0.73           ( m1_subset_1 @
% 0.54/0.73             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.54/0.73  thf('71', plain,
% 0.54/0.73      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.54/0.73         (~ (v2_funct_1 @ X32)
% 0.54/0.73          | ((k2_relset_1 @ X34 @ X33 @ X32) != (X33))
% 0.54/0.73          | (v1_funct_2 @ (k2_funct_1 @ X32) @ X33 @ X34)
% 0.54/0.73          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.54/0.73          | ~ (v1_funct_2 @ X32 @ X34 @ X33)
% 0.54/0.73          | ~ (v1_funct_1 @ X32))),
% 0.54/0.73      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.54/0.73  thf('72', plain,
% 0.54/0.73      ((~ (v1_funct_1 @ sk_C)
% 0.54/0.73        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.54/0.73        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.54/0.73           (k1_relat_1 @ sk_C))
% 0.54/0.73        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.54/0.73            != (k2_relat_1 @ sk_C))
% 0.54/0.73        | ~ (v2_funct_1 @ sk_C))),
% 0.54/0.73      inference('sup-', [status(thm)], ['70', '71'])).
% 0.54/0.73  thf('73', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('74', plain,
% 0.54/0.73      (![X35 : $i]:
% 0.54/0.73         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.54/0.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.54/0.73  thf('75', plain,
% 0.54/0.73      (![X35 : $i]:
% 0.54/0.73         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.54/0.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.54/0.73  thf('76', plain,
% 0.54/0.73      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('77', plain,
% 0.54/0.73      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.54/0.73        | ~ (l1_struct_0 @ sk_A))),
% 0.54/0.73      inference('sup+', [status(thm)], ['75', '76'])).
% 0.54/0.73  thf('78', plain, ((l1_struct_0 @ sk_A)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('79', plain,
% 0.54/0.73      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.54/0.73      inference('demod', [status(thm)], ['77', '78'])).
% 0.54/0.73  thf('80', plain,
% 0.54/0.73      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.54/0.73        | ~ (l1_struct_0 @ sk_B))),
% 0.54/0.73      inference('sup+', [status(thm)], ['74', '79'])).
% 0.54/0.73  thf('81', plain, ((l1_struct_0 @ sk_B)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('82', plain,
% 0.54/0.73      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.54/0.73      inference('demod', [status(thm)], ['80', '81'])).
% 0.54/0.73  thf('83', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.54/0.73      inference('sup+', [status(thm)], ['2', '3'])).
% 0.54/0.73  thf('84', plain,
% 0.54/0.73      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.54/0.73      inference('demod', [status(thm)], ['82', '83'])).
% 0.54/0.73  thf('85', plain,
% 0.54/0.73      (![X35 : $i]:
% 0.54/0.73         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.54/0.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.54/0.73  thf('86', plain,
% 0.54/0.73      (![X35 : $i]:
% 0.54/0.73         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.54/0.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.54/0.73  thf('87', plain,
% 0.54/0.73      ((m1_subset_1 @ sk_C @ 
% 0.54/0.73        (k1_zfmisc_1 @ 
% 0.54/0.73         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('88', plain,
% 0.54/0.73      (((m1_subset_1 @ sk_C @ 
% 0.54/0.73         (k1_zfmisc_1 @ 
% 0.54/0.73          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.54/0.73        | ~ (l1_struct_0 @ sk_A))),
% 0.54/0.73      inference('sup+', [status(thm)], ['86', '87'])).
% 0.54/0.73  thf('89', plain, ((l1_struct_0 @ sk_A)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('90', plain,
% 0.54/0.73      ((m1_subset_1 @ sk_C @ 
% 0.54/0.73        (k1_zfmisc_1 @ 
% 0.54/0.73         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.54/0.73      inference('demod', [status(thm)], ['88', '89'])).
% 0.54/0.73  thf('91', plain,
% 0.54/0.73      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.54/0.73         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.54/0.73          | (v1_partfun1 @ X27 @ X28)
% 0.54/0.73          | ~ (v1_funct_2 @ X27 @ X28 @ X29)
% 0.54/0.73          | ~ (v1_funct_1 @ X27)
% 0.54/0.73          | (v1_xboole_0 @ X29))),
% 0.54/0.73      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.54/0.73  thf('92', plain,
% 0.54/0.73      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.54/0.73        | ~ (v1_funct_1 @ sk_C)
% 0.54/0.73        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.54/0.73        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.54/0.73      inference('sup-', [status(thm)], ['90', '91'])).
% 0.54/0.73  thf('93', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('94', plain,
% 0.54/0.73      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.54/0.73      inference('demod', [status(thm)], ['77', '78'])).
% 0.54/0.73  thf('95', plain,
% 0.54/0.73      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.54/0.73        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.54/0.73      inference('demod', [status(thm)], ['92', '93', '94'])).
% 0.54/0.73  thf('96', plain,
% 0.54/0.73      (![X30 : $i, X31 : $i]:
% 0.54/0.73         (~ (v1_partfun1 @ X31 @ X30)
% 0.54/0.73          | ((k1_relat_1 @ X31) = (X30))
% 0.54/0.73          | ~ (v4_relat_1 @ X31 @ X30)
% 0.54/0.73          | ~ (v1_relat_1 @ X31))),
% 0.54/0.73      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.54/0.73  thf('97', plain,
% 0.54/0.73      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.54/0.73        | ~ (v1_relat_1 @ sk_C)
% 0.54/0.73        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.54/0.73        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.54/0.73      inference('sup-', [status(thm)], ['95', '96'])).
% 0.54/0.73  thf('98', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.73      inference('demod', [status(thm)], ['30', '31'])).
% 0.54/0.73  thf('99', plain,
% 0.54/0.73      ((m1_subset_1 @ sk_C @ 
% 0.54/0.73        (k1_zfmisc_1 @ 
% 0.54/0.73         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.54/0.73      inference('demod', [status(thm)], ['88', '89'])).
% 0.54/0.73  thf('100', plain,
% 0.54/0.73      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.54/0.73         ((v4_relat_1 @ X12 @ X13)
% 0.54/0.73          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.54/0.73      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.54/0.73  thf('101', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.54/0.73      inference('sup-', [status(thm)], ['99', '100'])).
% 0.54/0.73  thf('102', plain,
% 0.54/0.73      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.54/0.73        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.54/0.73      inference('demod', [status(thm)], ['97', '98', '101'])).
% 0.54/0.73  thf('103', plain,
% 0.54/0.73      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.54/0.73        | ~ (l1_struct_0 @ sk_B)
% 0.54/0.73        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.54/0.73      inference('sup+', [status(thm)], ['85', '102'])).
% 0.54/0.73  thf('104', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.54/0.73      inference('sup+', [status(thm)], ['2', '3'])).
% 0.54/0.73  thf('105', plain, ((l1_struct_0 @ sk_B)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('106', plain,
% 0.54/0.73      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.54/0.73        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.54/0.73      inference('demod', [status(thm)], ['103', '104', '105'])).
% 0.54/0.73  thf('107', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.54/0.73      inference('clc', [status(thm)], ['8', '9'])).
% 0.54/0.73  thf('108', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.54/0.73      inference('clc', [status(thm)], ['106', '107'])).
% 0.54/0.73  thf('109', plain,
% 0.54/0.73      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.54/0.73      inference('demod', [status(thm)], ['84', '108'])).
% 0.54/0.73  thf('110', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.54/0.73      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.54/0.73  thf('111', plain,
% 0.54/0.73      (![X35 : $i]:
% 0.54/0.73         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.54/0.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.54/0.73  thf('112', plain,
% 0.54/0.73      (![X35 : $i]:
% 0.54/0.73         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.54/0.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.54/0.73  thf('113', plain,
% 0.54/0.73      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.54/0.73         = (k2_struct_0 @ sk_B))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('114', plain,
% 0.54/0.74      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.54/0.74          = (k2_struct_0 @ sk_B))
% 0.54/0.74        | ~ (l1_struct_0 @ sk_B))),
% 0.54/0.74      inference('sup+', [status(thm)], ['112', '113'])).
% 0.54/0.74  thf('115', plain, ((l1_struct_0 @ sk_B)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('116', plain,
% 0.54/0.74      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.54/0.74         = (k2_struct_0 @ sk_B))),
% 0.54/0.74      inference('demod', [status(thm)], ['114', '115'])).
% 0.54/0.74  thf('117', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.54/0.74      inference('sup+', [status(thm)], ['2', '3'])).
% 0.54/0.74  thf('118', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.54/0.74      inference('sup+', [status(thm)], ['2', '3'])).
% 0.54/0.74  thf('119', plain,
% 0.54/0.74      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.54/0.74         = (k2_relat_1 @ sk_C))),
% 0.54/0.74      inference('demod', [status(thm)], ['116', '117', '118'])).
% 0.54/0.74  thf('120', plain,
% 0.54/0.74      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.54/0.74          = (k2_relat_1 @ sk_C))
% 0.54/0.74        | ~ (l1_struct_0 @ sk_A))),
% 0.54/0.74      inference('sup+', [status(thm)], ['111', '119'])).
% 0.54/0.74  thf('121', plain, ((l1_struct_0 @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('122', plain,
% 0.54/0.74      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.54/0.74         = (k2_relat_1 @ sk_C))),
% 0.54/0.74      inference('demod', [status(thm)], ['120', '121'])).
% 0.54/0.74  thf('123', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.54/0.74      inference('clc', [status(thm)], ['106', '107'])).
% 0.54/0.74  thf('124', plain,
% 0.54/0.74      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.54/0.74         = (k2_relat_1 @ sk_C))),
% 0.54/0.74      inference('demod', [status(thm)], ['122', '123'])).
% 0.54/0.74  thf('125', plain, ((v2_funct_1 @ sk_C)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('126', plain,
% 0.54/0.74      (((v1_funct_2 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.54/0.74         (k1_relat_1 @ sk_C))
% 0.54/0.74        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.54/0.74      inference('demod', [status(thm)],
% 0.54/0.74                ['72', '73', '109', '110', '124', '125'])).
% 0.54/0.74  thf('127', plain,
% 0.54/0.74      ((v1_funct_2 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.54/0.74        (k1_relat_1 @ sk_C))),
% 0.54/0.74      inference('simplify', [status(thm)], ['126'])).
% 0.54/0.74  thf('128', plain,
% 0.54/0.74      (((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 0.54/0.74        | (v1_partfun1 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C)))),
% 0.54/0.74      inference('demod', [status(thm)], ['58', '69', '127'])).
% 0.54/0.74  thf('129', plain,
% 0.54/0.74      (![X30 : $i, X31 : $i]:
% 0.54/0.74         (~ (v1_partfun1 @ X31 @ X30)
% 0.54/0.74          | ((k1_relat_1 @ X31) = (X30))
% 0.54/0.74          | ~ (v4_relat_1 @ X31 @ X30)
% 0.54/0.74          | ~ (v1_relat_1 @ X31))),
% 0.54/0.74      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.54/0.74  thf('130', plain,
% 0.54/0.74      (((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 0.54/0.74        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.54/0.74        | ~ (v4_relat_1 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.54/0.74        | ((k1_relat_1 @ (k4_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['128', '129'])).
% 0.54/0.74  thf('131', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.54/0.74      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.54/0.74  thf('132', plain,
% 0.54/0.74      (![X9 : $i]:
% 0.54/0.74         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 0.54/0.74          | ~ (v1_funct_1 @ X9)
% 0.54/0.74          | ~ (v1_relat_1 @ X9))),
% 0.54/0.74      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.54/0.74  thf('133', plain,
% 0.54/0.74      (((v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.54/0.74        | ~ (v1_relat_1 @ sk_C)
% 0.54/0.74        | ~ (v1_funct_1 @ sk_C))),
% 0.54/0.74      inference('sup+', [status(thm)], ['131', '132'])).
% 0.54/0.74  thf('134', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.74      inference('demod', [status(thm)], ['30', '31'])).
% 0.54/0.74  thf('135', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('136', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.54/0.74      inference('demod', [status(thm)], ['133', '134', '135'])).
% 0.54/0.74  thf('137', plain,
% 0.54/0.74      (![X35 : $i]:
% 0.54/0.74         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.54/0.74      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.54/0.74  thf('138', plain,
% 0.54/0.74      ((m1_subset_1 @ sk_C @ 
% 0.54/0.74        (k1_zfmisc_1 @ 
% 0.54/0.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('139', plain,
% 0.54/0.74      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.54/0.74         ((m1_subset_1 @ (k3_relset_1 @ X15 @ X16 @ X17) @ 
% 0.54/0.74           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X15)))
% 0.54/0.74          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.54/0.74      inference('cnf', [status(esa)], [dt_k3_relset_1])).
% 0.54/0.74  thf('140', plain,
% 0.54/0.74      ((m1_subset_1 @ 
% 0.54/0.74        (k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.54/0.74        (k1_zfmisc_1 @ 
% 0.54/0.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.54/0.74      inference('sup-', [status(thm)], ['138', '139'])).
% 0.54/0.74  thf('141', plain,
% 0.54/0.74      (((k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.54/0.74         = (k4_relat_1 @ sk_C))),
% 0.54/0.74      inference('sup-', [status(thm)], ['47', '48'])).
% 0.54/0.74  thf('142', plain,
% 0.54/0.74      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.54/0.74        (k1_zfmisc_1 @ 
% 0.54/0.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.54/0.74      inference('demod', [status(thm)], ['140', '141'])).
% 0.54/0.74  thf('143', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.54/0.74      inference('clc', [status(thm)], ['40', '41'])).
% 0.54/0.74  thf('144', plain,
% 0.54/0.74      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.54/0.74        (k1_zfmisc_1 @ 
% 0.54/0.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 0.54/0.74      inference('demod', [status(thm)], ['142', '143'])).
% 0.54/0.74  thf('145', plain,
% 0.54/0.74      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.54/0.74         ((v4_relat_1 @ X12 @ X13)
% 0.54/0.74          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.54/0.74      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.54/0.74  thf('146', plain,
% 0.54/0.74      ((v4_relat_1 @ (k4_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.54/0.74      inference('sup-', [status(thm)], ['144', '145'])).
% 0.54/0.74  thf('147', plain,
% 0.54/0.74      (((v4_relat_1 @ (k4_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 0.54/0.74        | ~ (l1_struct_0 @ sk_B))),
% 0.54/0.74      inference('sup+', [status(thm)], ['137', '146'])).
% 0.54/0.74  thf('148', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.54/0.74      inference('sup+', [status(thm)], ['2', '3'])).
% 0.54/0.74  thf('149', plain, ((l1_struct_0 @ sk_B)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('150', plain, ((v4_relat_1 @ (k4_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.54/0.74      inference('demod', [status(thm)], ['147', '148', '149'])).
% 0.54/0.74  thf('151', plain,
% 0.54/0.74      (((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 0.54/0.74        | ((k1_relat_1 @ (k4_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C)))),
% 0.54/0.74      inference('demod', [status(thm)], ['130', '136', '150'])).
% 0.54/0.74  thf(l13_xboole_0, axiom,
% 0.54/0.74    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.54/0.74  thf('152', plain,
% 0.54/0.74      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.54/0.74      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.54/0.74  thf('153', plain,
% 0.54/0.74      ((((k1_relat_1 @ (k4_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C))
% 0.54/0.74        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['151', '152'])).
% 0.54/0.74  thf(t146_relat_1, axiom,
% 0.54/0.74    (![A:$i]:
% 0.54/0.74     ( ( v1_relat_1 @ A ) =>
% 0.54/0.74       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.54/0.74  thf('154', plain,
% 0.54/0.74      (![X5 : $i]:
% 0.54/0.74         (((k9_relat_1 @ X5 @ (k1_relat_1 @ X5)) = (k2_relat_1 @ X5))
% 0.54/0.74          | ~ (v1_relat_1 @ X5))),
% 0.54/0.74      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.54/0.74  thf('155', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.54/0.74      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.54/0.74  thf(t155_funct_1, axiom,
% 0.54/0.74    (![A:$i,B:$i]:
% 0.54/0.74     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.54/0.74       ( ( v2_funct_1 @ B ) =>
% 0.54/0.74         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 0.54/0.74  thf('156', plain,
% 0.54/0.74      (![X10 : $i, X11 : $i]:
% 0.54/0.74         (~ (v2_funct_1 @ X10)
% 0.54/0.74          | ((k10_relat_1 @ X10 @ X11)
% 0.54/0.74              = (k9_relat_1 @ (k2_funct_1 @ X10) @ X11))
% 0.54/0.74          | ~ (v1_funct_1 @ X10)
% 0.54/0.74          | ~ (v1_relat_1 @ X10))),
% 0.54/0.74      inference('cnf', [status(esa)], [t155_funct_1])).
% 0.54/0.74  thf('157', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         (((k10_relat_1 @ sk_C @ X0) = (k9_relat_1 @ (k4_relat_1 @ sk_C) @ X0))
% 0.54/0.74          | ~ (v1_relat_1 @ sk_C)
% 0.54/0.74          | ~ (v1_funct_1 @ sk_C)
% 0.54/0.74          | ~ (v2_funct_1 @ sk_C))),
% 0.54/0.74      inference('sup+', [status(thm)], ['155', '156'])).
% 0.54/0.74  thf('158', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.74      inference('demod', [status(thm)], ['30', '31'])).
% 0.54/0.74  thf('159', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('160', plain, ((v2_funct_1 @ sk_C)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('161', plain,
% 0.54/0.74      (![X0 : $i]:
% 0.54/0.74         ((k10_relat_1 @ sk_C @ X0) = (k9_relat_1 @ (k4_relat_1 @ sk_C) @ X0))),
% 0.54/0.74      inference('demod', [status(thm)], ['157', '158', '159', '160'])).
% 0.54/0.74  thf('162', plain,
% 0.54/0.74      ((((k10_relat_1 @ sk_C @ (k1_relat_1 @ (k4_relat_1 @ sk_C)))
% 0.54/0.74          = (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 0.54/0.74        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.54/0.74      inference('sup+', [status(thm)], ['154', '161'])).
% 0.54/0.74  thf('163', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.54/0.74      inference('demod', [status(thm)], ['133', '134', '135'])).
% 0.54/0.74  thf('164', plain,
% 0.54/0.74      (((k10_relat_1 @ sk_C @ (k1_relat_1 @ (k4_relat_1 @ sk_C)))
% 0.54/0.74         = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.54/0.74      inference('demod', [status(thm)], ['162', '163'])).
% 0.54/0.74  thf('165', plain,
% 0.54/0.74      ((((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C))
% 0.54/0.74          = (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 0.54/0.74        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.54/0.74      inference('sup+', [status(thm)], ['153', '164'])).
% 0.54/0.74  thf('166', plain,
% 0.54/0.74      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 0.54/0.74        | ~ (v1_relat_1 @ sk_C)
% 0.54/0.74        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.54/0.74      inference('sup+', [status(thm)], ['11', '165'])).
% 0.54/0.74  thf('167', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.74      inference('demod', [status(thm)], ['30', '31'])).
% 0.54/0.74  thf('168', plain,
% 0.54/0.74      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 0.54/0.74        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.54/0.74      inference('demod', [status(thm)], ['166', '167'])).
% 0.54/0.74  thf('169', plain,
% 0.54/0.74      (![X35 : $i]:
% 0.54/0.74         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.54/0.74      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.54/0.74  thf('170', plain,
% 0.54/0.74      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.54/0.74          != (k2_struct_0 @ sk_B))
% 0.54/0.74        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.54/0.74            != (k2_struct_0 @ sk_A)))),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('171', plain,
% 0.54/0.74      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.54/0.74          != (k2_struct_0 @ sk_A)))
% 0.54/0.74         <= (~
% 0.54/0.74             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.54/0.74                = (k2_struct_0 @ sk_A))))),
% 0.54/0.74      inference('split', [status(esa)], ['170'])).
% 0.54/0.74  thf('172', plain,
% 0.54/0.74      (((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.54/0.74           != (k2_struct_0 @ sk_A))
% 0.54/0.74         | ~ (l1_struct_0 @ sk_B)))
% 0.54/0.74         <= (~
% 0.54/0.74             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.54/0.74                = (k2_struct_0 @ sk_A))))),
% 0.54/0.74      inference('sup-', [status(thm)], ['169', '171'])).
% 0.54/0.74  thf('173', plain, ((l1_struct_0 @ sk_B)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('174', plain,
% 0.54/0.74      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.54/0.74          != (k2_struct_0 @ sk_A)))
% 0.54/0.74         <= (~
% 0.54/0.74             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.54/0.74                = (k2_struct_0 @ sk_A))))),
% 0.54/0.74      inference('demod', [status(thm)], ['172', '173'])).
% 0.54/0.74  thf('175', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.54/0.74      inference('clc', [status(thm)], ['40', '41'])).
% 0.54/0.74  thf('176', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.54/0.74      inference('clc', [status(thm)], ['40', '41'])).
% 0.54/0.74  thf('177', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.54/0.74      inference('sup+', [status(thm)], ['2', '3'])).
% 0.54/0.74  thf('178', plain,
% 0.54/0.74      ((m1_subset_1 @ sk_C @ 
% 0.54/0.74        (k1_zfmisc_1 @ 
% 0.54/0.74         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.54/0.74      inference('demod', [status(thm)], ['18', '42'])).
% 0.54/0.74  thf(d4_tops_2, axiom,
% 0.54/0.74    (![A:$i,B:$i,C:$i]:
% 0.54/0.74     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.54/0.74         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.54/0.74       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.54/0.74         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.54/0.74  thf('179', plain,
% 0.54/0.74      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.54/0.74         (((k2_relset_1 @ X38 @ X37 @ X39) != (X37))
% 0.54/0.74          | ~ (v2_funct_1 @ X39)
% 0.54/0.74          | ((k2_tops_2 @ X38 @ X37 @ X39) = (k2_funct_1 @ X39))
% 0.54/0.74          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 0.54/0.74          | ~ (v1_funct_2 @ X39 @ X38 @ X37)
% 0.54/0.74          | ~ (v1_funct_1 @ X39))),
% 0.54/0.74      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.54/0.74  thf('180', plain,
% 0.54/0.74      ((~ (v1_funct_1 @ sk_C)
% 0.54/0.74        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.54/0.74        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.54/0.74            = (k2_funct_1 @ sk_C))
% 0.54/0.74        | ~ (v2_funct_1 @ sk_C)
% 0.54/0.74        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.54/0.74            != (k2_relat_1 @ sk_C)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['178', '179'])).
% 0.54/0.74  thf('181', plain, ((v1_funct_1 @ sk_C)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('182', plain,
% 0.54/0.74      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.54/0.74      inference('demod', [status(thm)], ['84', '108'])).
% 0.54/0.74  thf('183', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.54/0.74      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.54/0.74  thf('184', plain, ((v2_funct_1 @ sk_C)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('185', plain,
% 0.54/0.74      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.54/0.74         = (k2_relat_1 @ sk_C))),
% 0.54/0.74      inference('demod', [status(thm)], ['122', '123'])).
% 0.54/0.74  thf('186', plain,
% 0.54/0.74      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.54/0.74          = (k4_relat_1 @ sk_C))
% 0.54/0.74        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.54/0.74      inference('demod', [status(thm)],
% 0.54/0.74                ['180', '181', '182', '183', '184', '185'])).
% 0.54/0.74  thf('187', plain,
% 0.54/0.74      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.54/0.74         = (k4_relat_1 @ sk_C))),
% 0.54/0.74      inference('simplify', [status(thm)], ['186'])).
% 0.54/0.74  thf('188', plain,
% 0.54/0.74      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.54/0.74        (k1_zfmisc_1 @ 
% 0.54/0.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 0.54/0.74      inference('demod', [status(thm)], ['142', '143'])).
% 0.54/0.74  thf('189', plain,
% 0.54/0.74      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.54/0.74         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 0.54/0.74          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.54/0.74      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.54/0.74  thf('190', plain,
% 0.54/0.74      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.54/0.74         (k4_relat_1 @ sk_C)) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['188', '189'])).
% 0.54/0.74  thf('191', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.54/0.74      inference('clc', [status(thm)], ['106', '107'])).
% 0.54/0.74  thf('192', plain,
% 0.54/0.74      ((((k2_relat_1 @ (k4_relat_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 0.54/0.74         <= (~
% 0.54/0.74             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.54/0.74                = (k2_struct_0 @ sk_A))))),
% 0.54/0.74      inference('demod', [status(thm)],
% 0.54/0.74                ['174', '175', '176', '177', '187', '190', '191'])).
% 0.54/0.74  thf('193', plain,
% 0.54/0.74      ((((k1_relat_1 @ (k4_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C))
% 0.54/0.74        | ((k1_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['151', '152'])).
% 0.54/0.74  thf('194', plain,
% 0.54/0.74      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.54/0.74         = (k4_relat_1 @ sk_C))),
% 0.54/0.74      inference('simplify', [status(thm)], ['186'])).
% 0.54/0.74  thf('195', plain,
% 0.54/0.74      (![X35 : $i]:
% 0.54/0.74         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.54/0.74      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.54/0.74  thf('196', plain,
% 0.54/0.74      (![X35 : $i]:
% 0.54/0.74         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.54/0.74      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.54/0.74  thf('197', plain,
% 0.54/0.74      (![X35 : $i]:
% 0.54/0.74         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.54/0.74      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.54/0.74  thf('198', plain,
% 0.54/0.74      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.54/0.74          != (k2_struct_0 @ sk_B)))
% 0.54/0.74         <= (~
% 0.54/0.74             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.54/0.74                = (k2_struct_0 @ sk_B))))),
% 0.54/0.74      inference('split', [status(esa)], ['170'])).
% 0.54/0.74  thf('199', plain,
% 0.54/0.74      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.54/0.74           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.54/0.74           != (k2_struct_0 @ sk_B))
% 0.54/0.74         | ~ (l1_struct_0 @ sk_A)))
% 0.54/0.74         <= (~
% 0.54/0.74             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.54/0.74                = (k2_struct_0 @ sk_B))))),
% 0.54/0.74      inference('sup-', [status(thm)], ['197', '198'])).
% 0.54/0.74  thf('200', plain, ((l1_struct_0 @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('201', plain,
% 0.54/0.74      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.54/0.74          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.54/0.74          != (k2_struct_0 @ sk_B)))
% 0.54/0.74         <= (~
% 0.54/0.74             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.54/0.74                = (k2_struct_0 @ sk_B))))),
% 0.54/0.74      inference('demod', [status(thm)], ['199', '200'])).
% 0.54/0.74  thf('202', plain,
% 0.54/0.74      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.54/0.74           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.54/0.74           != (k2_struct_0 @ sk_B))
% 0.54/0.74         | ~ (l1_struct_0 @ sk_B)))
% 0.54/0.74         <= (~
% 0.54/0.74             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.54/0.74                = (k2_struct_0 @ sk_B))))),
% 0.54/0.74      inference('sup-', [status(thm)], ['196', '201'])).
% 0.54/0.74  thf('203', plain, ((l1_struct_0 @ sk_B)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('204', plain,
% 0.54/0.74      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.54/0.74          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.54/0.74          != (k2_struct_0 @ sk_B)))
% 0.54/0.74         <= (~
% 0.54/0.74             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.54/0.74                = (k2_struct_0 @ sk_B))))),
% 0.54/0.74      inference('demod', [status(thm)], ['202', '203'])).
% 0.54/0.74  thf('205', plain,
% 0.54/0.74      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.54/0.74           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.54/0.74           != (k2_struct_0 @ sk_B))
% 0.54/0.74         | ~ (l1_struct_0 @ sk_A)))
% 0.54/0.74         <= (~
% 0.54/0.74             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.54/0.74                = (k2_struct_0 @ sk_B))))),
% 0.54/0.74      inference('sup-', [status(thm)], ['195', '204'])).
% 0.54/0.74  thf('206', plain, ((l1_struct_0 @ sk_A)),
% 0.54/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.74  thf('207', plain,
% 0.54/0.74      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.54/0.74          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.54/0.74          != (k2_struct_0 @ sk_B)))
% 0.54/0.74         <= (~
% 0.54/0.74             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.54/0.74                = (k2_struct_0 @ sk_B))))),
% 0.54/0.74      inference('demod', [status(thm)], ['205', '206'])).
% 0.54/0.74  thf('208', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.54/0.74      inference('clc', [status(thm)], ['106', '107'])).
% 0.54/0.74  thf('209', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.54/0.74      inference('clc', [status(thm)], ['106', '107'])).
% 0.54/0.74  thf('210', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.54/0.74      inference('sup+', [status(thm)], ['2', '3'])).
% 0.54/0.74  thf('211', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.54/0.74      inference('sup+', [status(thm)], ['2', '3'])).
% 0.54/0.74  thf('212', plain,
% 0.54/0.74      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.54/0.74          (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.54/0.74          != (k2_relat_1 @ sk_C)))
% 0.54/0.74         <= (~
% 0.54/0.74             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.54/0.74                = (k2_struct_0 @ sk_B))))),
% 0.54/0.74      inference('demod', [status(thm)], ['207', '208', '209', '210', '211'])).
% 0.54/0.74  thf('213', plain,
% 0.54/0.74      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.54/0.74          (k4_relat_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.54/0.74         <= (~
% 0.54/0.74             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.54/0.74                = (k2_struct_0 @ sk_B))))),
% 0.54/0.74      inference('sup-', [status(thm)], ['194', '212'])).
% 0.54/0.74  thf('214', plain,
% 0.54/0.74      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.54/0.74        (k1_zfmisc_1 @ 
% 0.54/0.74         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 0.54/0.74      inference('demod', [status(thm)], ['142', '143'])).
% 0.54/0.74  thf(redefinition_k1_relset_1, axiom,
% 0.54/0.74    (![A:$i,B:$i,C:$i]:
% 0.54/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.74       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.54/0.74  thf('215', plain,
% 0.54/0.74      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.54/0.74         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 0.54/0.74          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.54/0.74      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.54/0.74  thf('216', plain,
% 0.54/0.74      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.54/0.74         (k4_relat_1 @ sk_C)) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['214', '215'])).
% 0.54/0.74  thf('217', plain,
% 0.54/0.74      ((((k1_relat_1 @ (k4_relat_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.54/0.74         <= (~
% 0.54/0.74             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.54/0.74                = (k2_struct_0 @ sk_B))))),
% 0.54/0.74      inference('demod', [status(thm)], ['213', '216'])).
% 0.54/0.74  thf('218', plain,
% 0.54/0.74      (((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.54/0.74         | ((k1_relat_1 @ sk_C) = (k1_xboole_0))))
% 0.54/0.74         <= (~
% 0.54/0.74             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.54/0.74                = (k2_struct_0 @ sk_B))))),
% 0.54/0.74      inference('sup-', [status(thm)], ['193', '217'])).
% 0.54/0.74  thf('219', plain,
% 0.54/0.74      ((((k1_relat_1 @ sk_C) = (k1_xboole_0)))
% 0.54/0.74         <= (~
% 0.54/0.74             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.54/0.74                = (k2_struct_0 @ sk_B))))),
% 0.54/0.74      inference('simplify', [status(thm)], ['218'])).
% 0.54/0.74  thf(t65_relat_1, axiom,
% 0.54/0.74    (![A:$i]:
% 0.54/0.74     ( ( v1_relat_1 @ A ) =>
% 0.54/0.74       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.54/0.74         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.54/0.74  thf('220', plain,
% 0.54/0.74      (![X7 : $i]:
% 0.54/0.74         (((k1_relat_1 @ X7) != (k1_xboole_0))
% 0.54/0.74          | ((k2_relat_1 @ X7) = (k1_xboole_0))
% 0.54/0.74          | ~ (v1_relat_1 @ X7))),
% 0.54/0.74      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.54/0.74  thf('221', plain,
% 0.54/0.74      (((((k1_xboole_0) != (k1_xboole_0))
% 0.54/0.74         | ~ (v1_relat_1 @ sk_C)
% 0.54/0.74         | ((k2_relat_1 @ sk_C) = (k1_xboole_0))))
% 0.54/0.74         <= (~
% 0.54/0.74             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.54/0.74                = (k2_struct_0 @ sk_B))))),
% 0.54/0.74      inference('sup-', [status(thm)], ['219', '220'])).
% 0.54/0.74  thf('222', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.74      inference('demod', [status(thm)], ['30', '31'])).
% 0.54/0.74  thf('223', plain,
% 0.54/0.74      (((((k1_xboole_0) != (k1_xboole_0))
% 0.54/0.74         | ((k2_relat_1 @ sk_C) = (k1_xboole_0))))
% 0.54/0.74         <= (~
% 0.54/0.74             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.54/0.74                = (k2_struct_0 @ sk_B))))),
% 0.54/0.74      inference('demod', [status(thm)], ['221', '222'])).
% 0.54/0.74  thf('224', plain,
% 0.54/0.74      ((((k2_relat_1 @ sk_C) = (k1_xboole_0)))
% 0.54/0.74         <= (~
% 0.54/0.74             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.54/0.74                = (k2_struct_0 @ sk_B))))),
% 0.54/0.74      inference('simplify', [status(thm)], ['223'])).
% 0.54/0.74  thf('225', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.54/0.74      inference('clc', [status(thm)], ['8', '9'])).
% 0.54/0.74  thf('226', plain,
% 0.54/0.74      ((~ (v1_xboole_0 @ k1_xboole_0))
% 0.54/0.74         <= (~
% 0.54/0.74             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.54/0.74                = (k2_struct_0 @ sk_B))))),
% 0.54/0.74      inference('sup-', [status(thm)], ['224', '225'])).
% 0.54/0.74  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.54/0.74  thf('227', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.54/0.74      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.54/0.74  thf('228', plain,
% 0.54/0.74      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.54/0.74          = (k2_struct_0 @ sk_B)))),
% 0.54/0.74      inference('demod', [status(thm)], ['226', '227'])).
% 0.54/0.74  thf('229', plain,
% 0.54/0.74      (~
% 0.54/0.74       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.54/0.74          = (k2_struct_0 @ sk_A))) | 
% 0.54/0.74       ~
% 0.54/0.74       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.54/0.74          = (k2_struct_0 @ sk_B)))),
% 0.54/0.74      inference('split', [status(esa)], ['170'])).
% 0.54/0.74  thf('230', plain,
% 0.54/0.74      (~
% 0.54/0.74       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.54/0.74          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.54/0.74          = (k2_struct_0 @ sk_A)))),
% 0.54/0.74      inference('sat_resolution*', [status(thm)], ['228', '229'])).
% 0.54/0.74  thf('231', plain,
% 0.54/0.74      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) != (k1_relat_1 @ sk_C))),
% 0.54/0.74      inference('simpl_trail', [status(thm)], ['192', '230'])).
% 0.54/0.74  thf('232', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.54/0.74      inference('simplify_reflect-', [status(thm)], ['168', '231'])).
% 0.54/0.74  thf('233', plain,
% 0.54/0.74      (![X7 : $i]:
% 0.54/0.74         (((k1_relat_1 @ X7) != (k1_xboole_0))
% 0.54/0.74          | ((k2_relat_1 @ X7) = (k1_xboole_0))
% 0.54/0.74          | ~ (v1_relat_1 @ X7))),
% 0.54/0.74      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.54/0.74  thf('234', plain,
% 0.54/0.74      ((((k1_xboole_0) != (k1_xboole_0))
% 0.54/0.74        | ~ (v1_relat_1 @ sk_C)
% 0.54/0.74        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.54/0.74      inference('sup-', [status(thm)], ['232', '233'])).
% 0.54/0.74  thf('235', plain, ((v1_relat_1 @ sk_C)),
% 0.54/0.74      inference('demod', [status(thm)], ['30', '31'])).
% 0.54/0.74  thf('236', plain,
% 0.54/0.74      ((((k1_xboole_0) != (k1_xboole_0))
% 0.54/0.74        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.54/0.74      inference('demod', [status(thm)], ['234', '235'])).
% 0.54/0.74  thf('237', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.54/0.74      inference('simplify', [status(thm)], ['236'])).
% 0.54/0.74  thf('238', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.54/0.74      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.54/0.74  thf('239', plain, ($false),
% 0.54/0.74      inference('demod', [status(thm)], ['10', '237', '238'])).
% 0.54/0.74  
% 0.54/0.74  % SZS output end Refutation
% 0.54/0.74  
% 0.54/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
