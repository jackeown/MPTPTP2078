%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aQlaQoqiLj

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:04 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 355 expanded)
%              Number of leaves         :   41 ( 124 expanded)
%              Depth                    :   14
%              Number of atoms          : 1144 (8752 expanded)
%              Number of equality atoms :   87 ( 474 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_relset_1_type,type,(
    k3_relset_1: $i > $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
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
    ! [X22: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
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

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('11',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('13',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k8_relset_1 @ X18 @ X19 @ X20 @ X19 )
        = ( k1_relset_1 @ X18 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('14',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_B ) )
    = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('16',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('17',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_B ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','18'])).

thf('20',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('21',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t52_tops_2,axiom,(
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

thf('24',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( l1_struct_0 @ X26 )
      | ( ( k2_struct_0 @ X26 )
        = k1_xboole_0 )
      | ( ( k8_relset_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X26 ) @ X28 @ ( k2_struct_0 @ X26 ) )
        = ( k2_struct_0 @ X27 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X26 ) ) ) )
      | ~ ( v1_funct_2 @ X28 @ ( u1_struct_0 @ X27 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t52_tops_2])).

thf('25',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_struct_0 @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('30',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('31',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( k8_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( k2_relat_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','26','27','28','29','30','31'])).

thf('33',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','32'])).

thf('34',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('36',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('39',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X23 @ X25 )
       != X23 )
      | ~ ( v2_funct_1 @ X25 )
      | ( ( k2_tops_2 @ X24 @ X23 @ X25 )
        = ( k2_funct_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X24 @ X23 )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('40',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('45',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['40','41','42','43','44'])).

thf('46',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['37','45'])).

thf('47',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('48',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k3_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) )).

thf('52',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k3_relset_1 @ X6 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X6 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_relset_1])).

thf('53',plain,(
    m1_subset_1 @ ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k3_relset_1 @ A @ B @ C )
        = ( k4_relat_1 @ C ) ) ) )).

thf('55',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k3_relset_1 @ X16 @ X17 @ X15 )
        = ( k4_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_relset_1])).

thf('56',plain,
    ( ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('59',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('60',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('61',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('62',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_funct_1 @ X5 )
        = ( k4_relat_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('63',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,
    ( ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['56','66'])).

thf('68',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['53','67'])).

thf('69',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('70',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('72',plain,(
    ! [X4: $i] :
      ( ( ( k2_relat_1 @ X4 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('73',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('75',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['70','75'])).

thf('77',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['49'])).

thf('78',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['53','67'])).

thf('79',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('80',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('82',plain,(
    ! [X4: $i] :
      ( ( ( k1_relat_1 @ X4 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('83',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['59','60'])).

thf('85',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['80','85'])).

thf('87',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','50','76','77','86'])).

thf('88',plain,(
    ( k1_relat_1 @ sk_C )
 != ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['33','88'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('90',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('91',plain,(
    $false ),
    inference(demod,[status(thm)],['10','89','90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aQlaQoqiLj
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:00:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.37/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.56  % Solved by: fo/fo7.sh
% 0.37/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.56  % done 373 iterations in 0.100s
% 0.37/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.56  % SZS output start Refutation
% 0.37/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.37/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.56  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.37/0.56  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.37/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.56  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.37/0.56  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.37/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.56  thf(k3_relset_1_type, type, k3_relset_1: $i > $i > $i > $i).
% 0.37/0.56  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.37/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.56  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.37/0.56  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.37/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.56  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.37/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.37/0.56  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.37/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.37/0.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.37/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.56  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.37/0.56  thf(t62_tops_2, conjecture,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( l1_struct_0 @ A ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.37/0.56           ( ![C:$i]:
% 0.37/0.56             ( ( ( v1_funct_1 @ C ) & 
% 0.37/0.56                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.37/0.56                 ( m1_subset_1 @
% 0.37/0.56                   C @ 
% 0.37/0.56                   ( k1_zfmisc_1 @
% 0.37/0.56                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.37/0.56               ( ( ( ( k2_relset_1 @
% 0.37/0.56                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.37/0.56                     ( k2_struct_0 @ B ) ) & 
% 0.37/0.56                   ( v2_funct_1 @ C ) ) =>
% 0.37/0.56                 ( ( ( k1_relset_1 @
% 0.37/0.56                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.37/0.56                       ( k2_tops_2 @
% 0.37/0.56                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.37/0.56                     ( k2_struct_0 @ B ) ) & 
% 0.37/0.56                   ( ( k2_relset_1 @
% 0.37/0.56                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.37/0.56                       ( k2_tops_2 @
% 0.37/0.56                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.37/0.56                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.37/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.56    (~( ![A:$i]:
% 0.37/0.56        ( ( l1_struct_0 @ A ) =>
% 0.37/0.56          ( ![B:$i]:
% 0.37/0.56            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.37/0.56              ( ![C:$i]:
% 0.37/0.56                ( ( ( v1_funct_1 @ C ) & 
% 0.37/0.56                    ( v1_funct_2 @
% 0.37/0.56                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.37/0.56                    ( m1_subset_1 @
% 0.37/0.56                      C @ 
% 0.37/0.56                      ( k1_zfmisc_1 @
% 0.37/0.56                        ( k2_zfmisc_1 @
% 0.37/0.56                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.37/0.56                  ( ( ( ( k2_relset_1 @
% 0.37/0.56                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.37/0.56                        ( k2_struct_0 @ B ) ) & 
% 0.37/0.56                      ( v2_funct_1 @ C ) ) =>
% 0.37/0.56                    ( ( ( k1_relset_1 @
% 0.37/0.56                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.37/0.56                          ( k2_tops_2 @
% 0.37/0.56                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.37/0.56                        ( k2_struct_0 @ B ) ) & 
% 0.37/0.56                      ( ( k2_relset_1 @
% 0.37/0.56                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.37/0.56                          ( k2_tops_2 @
% 0.37/0.56                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.37/0.56                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.37/0.56    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 0.37/0.56  thf('0', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_C @ 
% 0.37/0.56        (k1_zfmisc_1 @ 
% 0.37/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(redefinition_k2_relset_1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.56       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.37/0.56  thf('1', plain,
% 0.37/0.56      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.37/0.56         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 0.37/0.56          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.37/0.56      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.37/0.56  thf('2', plain,
% 0.37/0.56      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.56         = (k2_relat_1 @ sk_C))),
% 0.37/0.56      inference('sup-', [status(thm)], ['0', '1'])).
% 0.37/0.56  thf('3', plain,
% 0.37/0.56      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.37/0.56         = (k2_struct_0 @ sk_B))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('4', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.38/0.56      inference('sup+', [status(thm)], ['2', '3'])).
% 0.38/0.56  thf(fc5_struct_0, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.38/0.56       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.38/0.56  thf('5', plain,
% 0.38/0.56      (![X22 : $i]:
% 0.38/0.56         (~ (v1_xboole_0 @ (k2_struct_0 @ X22))
% 0.38/0.56          | ~ (l1_struct_0 @ X22)
% 0.38/0.56          | (v2_struct_0 @ X22))),
% 0.38/0.56      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.38/0.56  thf('6', plain,
% 0.38/0.56      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.38/0.56        | (v2_struct_0 @ sk_B)
% 0.38/0.56        | ~ (l1_struct_0 @ sk_B))),
% 0.38/0.56      inference('sup-', [status(thm)], ['4', '5'])).
% 0.38/0.56  thf('7', plain, ((l1_struct_0 @ sk_B)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('8', plain,
% 0.38/0.56      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.38/0.56      inference('demod', [status(thm)], ['6', '7'])).
% 0.38/0.56  thf('9', plain, (~ (v2_struct_0 @ sk_B)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('10', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.38/0.56      inference('clc', [status(thm)], ['8', '9'])).
% 0.38/0.56  thf(d3_struct_0, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.38/0.56  thf('11', plain,
% 0.38/0.56      (![X21 : $i]:
% 0.38/0.56         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.38/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.56  thf('12', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_C @ 
% 0.38/0.56        (k1_zfmisc_1 @ 
% 0.38/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(t38_relset_1, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.56       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.38/0.56         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.38/0.56  thf('13', plain,
% 0.38/0.56      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.38/0.56         (((k8_relset_1 @ X18 @ X19 @ X20 @ X19)
% 0.38/0.56            = (k1_relset_1 @ X18 @ X19 @ X20))
% 0.38/0.56          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.38/0.56      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.38/0.56  thf('14', plain,
% 0.38/0.56      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.38/0.56         (u1_struct_0 @ sk_B))
% 0.38/0.56         = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.38/0.56      inference('sup-', [status(thm)], ['12', '13'])).
% 0.38/0.56  thf('15', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_C @ 
% 0.38/0.56        (k1_zfmisc_1 @ 
% 0.38/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(redefinition_k1_relset_1, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.56       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.38/0.56  thf('16', plain,
% 0.38/0.56      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.38/0.56         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 0.38/0.56          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.38/0.56      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.38/0.56  thf('17', plain,
% 0.38/0.56      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.38/0.56         = (k1_relat_1 @ sk_C))),
% 0.38/0.56      inference('sup-', [status(thm)], ['15', '16'])).
% 0.38/0.56  thf('18', plain,
% 0.38/0.56      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.38/0.56         (u1_struct_0 @ sk_B)) = (k1_relat_1 @ sk_C))),
% 0.38/0.56      inference('demod', [status(thm)], ['14', '17'])).
% 0.38/0.56  thf('19', plain,
% 0.38/0.56      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.38/0.56          (k2_struct_0 @ sk_B)) = (k1_relat_1 @ sk_C))
% 0.38/0.56        | ~ (l1_struct_0 @ sk_B))),
% 0.38/0.56      inference('sup+', [status(thm)], ['11', '18'])).
% 0.38/0.56  thf('20', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.38/0.56      inference('sup+', [status(thm)], ['2', '3'])).
% 0.38/0.56  thf('21', plain, ((l1_struct_0 @ sk_B)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('22', plain,
% 0.38/0.56      (((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.38/0.56         (k2_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.38/0.56      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.38/0.56  thf('23', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_C @ 
% 0.38/0.56        (k1_zfmisc_1 @ 
% 0.38/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(t52_tops_2, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( l1_struct_0 @ A ) =>
% 0.38/0.56       ( ![B:$i]:
% 0.38/0.56         ( ( l1_struct_0 @ B ) =>
% 0.38/0.56           ( ![C:$i]:
% 0.38/0.56             ( ( ( v1_funct_1 @ C ) & 
% 0.38/0.56                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.38/0.56                 ( m1_subset_1 @
% 0.38/0.56                   C @ 
% 0.38/0.56                   ( k1_zfmisc_1 @
% 0.38/0.56                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.38/0.56               ( ( ( ( k2_struct_0 @ B ) = ( k1_xboole_0 ) ) =>
% 0.38/0.56                   ( ( k2_struct_0 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.38/0.56                 ( ( k8_relset_1 @
% 0.38/0.56                     ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.38/0.56                     ( k2_struct_0 @ B ) ) =
% 0.38/0.56                   ( k2_struct_0 @ A ) ) ) ) ) ) ) ))).
% 0.38/0.56  thf('24', plain,
% 0.38/0.56      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.38/0.56         (~ (l1_struct_0 @ X26)
% 0.38/0.56          | ((k2_struct_0 @ X26) = (k1_xboole_0))
% 0.38/0.56          | ((k8_relset_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X26) @ X28 @ 
% 0.38/0.56              (k2_struct_0 @ X26)) = (k2_struct_0 @ X27))
% 0.38/0.56          | ~ (m1_subset_1 @ X28 @ 
% 0.38/0.56               (k1_zfmisc_1 @ 
% 0.38/0.56                (k2_zfmisc_1 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X26))))
% 0.38/0.56          | ~ (v1_funct_2 @ X28 @ (u1_struct_0 @ X27) @ (u1_struct_0 @ X26))
% 0.38/0.56          | ~ (v1_funct_1 @ X28)
% 0.38/0.56          | ~ (l1_struct_0 @ X27))),
% 0.38/0.56      inference('cnf', [status(esa)], [t52_tops_2])).
% 0.38/0.56  thf('25', plain,
% 0.38/0.56      ((~ (l1_struct_0 @ sk_A)
% 0.38/0.56        | ~ (v1_funct_1 @ sk_C)
% 0.38/0.56        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.38/0.56        | ((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.38/0.56            (k2_struct_0 @ sk_B)) = (k2_struct_0 @ sk_A))
% 0.38/0.56        | ((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.38/0.56        | ~ (l1_struct_0 @ sk_B))),
% 0.38/0.56      inference('sup-', [status(thm)], ['23', '24'])).
% 0.38/0.56  thf('26', plain, ((l1_struct_0 @ sk_A)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('27', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('28', plain,
% 0.38/0.56      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('29', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.38/0.56      inference('sup+', [status(thm)], ['2', '3'])).
% 0.38/0.56  thf('30', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.38/0.56      inference('sup+', [status(thm)], ['2', '3'])).
% 0.38/0.56  thf('31', plain, ((l1_struct_0 @ sk_B)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('32', plain,
% 0.38/0.56      ((((k8_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.38/0.56          (k2_relat_1 @ sk_C)) = (k2_struct_0 @ sk_A))
% 0.38/0.56        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.38/0.56      inference('demod', [status(thm)],
% 0.38/0.56                ['25', '26', '27', '28', '29', '30', '31'])).
% 0.38/0.56  thf('33', plain,
% 0.38/0.56      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))
% 0.38/0.56        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.38/0.56      inference('sup+', [status(thm)], ['22', '32'])).
% 0.38/0.56  thf('34', plain,
% 0.38/0.56      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.56          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.38/0.56          != (k2_struct_0 @ sk_B))
% 0.38/0.56        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.56            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.38/0.56            != (k2_struct_0 @ sk_A)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('35', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.38/0.56      inference('sup+', [status(thm)], ['2', '3'])).
% 0.38/0.56  thf('36', plain,
% 0.38/0.56      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.56          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.38/0.56          != (k2_relat_1 @ sk_C))
% 0.38/0.56        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.56            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.38/0.56            != (k2_struct_0 @ sk_A)))),
% 0.38/0.56      inference('demod', [status(thm)], ['34', '35'])).
% 0.38/0.56  thf('37', plain,
% 0.38/0.56      (![X21 : $i]:
% 0.38/0.56         (((k2_struct_0 @ X21) = (u1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.38/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.38/0.56  thf('38', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_C @ 
% 0.38/0.56        (k1_zfmisc_1 @ 
% 0.38/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(d4_tops_2, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.38/0.56         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.56       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.38/0.56         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.38/0.56  thf('39', plain,
% 0.38/0.56      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.38/0.56         (((k2_relset_1 @ X24 @ X23 @ X25) != (X23))
% 0.38/0.56          | ~ (v2_funct_1 @ X25)
% 0.38/0.56          | ((k2_tops_2 @ X24 @ X23 @ X25) = (k2_funct_1 @ X25))
% 0.38/0.56          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23)))
% 0.38/0.56          | ~ (v1_funct_2 @ X25 @ X24 @ X23)
% 0.38/0.56          | ~ (v1_funct_1 @ X25))),
% 0.38/0.56      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.38/0.56  thf('40', plain,
% 0.38/0.56      ((~ (v1_funct_1 @ sk_C)
% 0.38/0.56        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.38/0.56        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.38/0.56            = (k2_funct_1 @ sk_C))
% 0.38/0.56        | ~ (v2_funct_1 @ sk_C)
% 0.38/0.56        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.38/0.56            != (u1_struct_0 @ sk_B)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['38', '39'])).
% 0.38/0.56  thf('41', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('42', plain,
% 0.38/0.56      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('43', plain, ((v2_funct_1 @ sk_C)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('44', plain,
% 0.38/0.56      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.38/0.56         = (k2_relat_1 @ sk_C))),
% 0.38/0.56      inference('sup-', [status(thm)], ['0', '1'])).
% 0.38/0.56  thf('45', plain,
% 0.38/0.56      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.38/0.56          = (k2_funct_1 @ sk_C))
% 0.38/0.56        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.38/0.56      inference('demod', [status(thm)], ['40', '41', '42', '43', '44'])).
% 0.38/0.56  thf('46', plain,
% 0.38/0.56      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.38/0.56        | ~ (l1_struct_0 @ sk_B)
% 0.38/0.56        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.38/0.56            = (k2_funct_1 @ sk_C)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['37', '45'])).
% 0.38/0.56  thf('47', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.38/0.56      inference('sup+', [status(thm)], ['2', '3'])).
% 0.38/0.56  thf('48', plain, ((l1_struct_0 @ sk_B)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('49', plain,
% 0.38/0.56      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.38/0.56        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.38/0.56            = (k2_funct_1 @ sk_C)))),
% 0.38/0.56      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.38/0.56  thf('50', plain,
% 0.38/0.56      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.38/0.56         = (k2_funct_1 @ sk_C))),
% 0.38/0.56      inference('simplify', [status(thm)], ['49'])).
% 0.38/0.56  thf('51', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_C @ 
% 0.38/0.56        (k1_zfmisc_1 @ 
% 0.38/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(dt_k3_relset_1, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.56       ( m1_subset_1 @
% 0.38/0.56         ( k3_relset_1 @ A @ B @ C ) @ 
% 0.38/0.56         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ))).
% 0.38/0.56  thf('52', plain,
% 0.38/0.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.38/0.56         ((m1_subset_1 @ (k3_relset_1 @ X6 @ X7 @ X8) @ 
% 0.38/0.56           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X6)))
% 0.38/0.56          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_k3_relset_1])).
% 0.38/0.56  thf('53', plain,
% 0.38/0.56      ((m1_subset_1 @ 
% 0.38/0.56        (k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.38/0.56        (k1_zfmisc_1 @ 
% 0.38/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['51', '52'])).
% 0.38/0.56  thf('54', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_C @ 
% 0.38/0.56        (k1_zfmisc_1 @ 
% 0.38/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(redefinition_k3_relset_1, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.56       ( ( k3_relset_1 @ A @ B @ C ) = ( k4_relat_1 @ C ) ) ))).
% 0.38/0.56  thf('55', plain,
% 0.38/0.56      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.38/0.56         (((k3_relset_1 @ X16 @ X17 @ X15) = (k4_relat_1 @ X15))
% 0.38/0.56          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.38/0.56      inference('cnf', [status(esa)], [redefinition_k3_relset_1])).
% 0.38/0.56  thf('56', plain,
% 0.38/0.56      (((k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.38/0.56         = (k4_relat_1 @ sk_C))),
% 0.38/0.56      inference('sup-', [status(thm)], ['54', '55'])).
% 0.38/0.56  thf('57', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_C @ 
% 0.38/0.56        (k1_zfmisc_1 @ 
% 0.38/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(cc2_relat_1, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( v1_relat_1 @ A ) =>
% 0.38/0.56       ( ![B:$i]:
% 0.38/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.38/0.56  thf('58', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.38/0.56          | (v1_relat_1 @ X0)
% 0.38/0.56          | ~ (v1_relat_1 @ X1))),
% 0.38/0.56      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.38/0.56  thf('59', plain,
% 0.38/0.56      ((~ (v1_relat_1 @ 
% 0.38/0.56           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.38/0.56        | (v1_relat_1 @ sk_C))),
% 0.38/0.56      inference('sup-', [status(thm)], ['57', '58'])).
% 0.38/0.56  thf(fc6_relat_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.38/0.56  thf('60', plain,
% 0.38/0.56      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.38/0.56      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.38/0.56  thf('61', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.56      inference('demod', [status(thm)], ['59', '60'])).
% 0.38/0.56  thf(d9_funct_1, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.56       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.38/0.56  thf('62', plain,
% 0.38/0.56      (![X5 : $i]:
% 0.38/0.56         (~ (v2_funct_1 @ X5)
% 0.38/0.56          | ((k2_funct_1 @ X5) = (k4_relat_1 @ X5))
% 0.38/0.56          | ~ (v1_funct_1 @ X5)
% 0.38/0.56          | ~ (v1_relat_1 @ X5))),
% 0.38/0.56      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.38/0.56  thf('63', plain,
% 0.38/0.56      ((~ (v1_funct_1 @ sk_C)
% 0.38/0.56        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 0.38/0.56        | ~ (v2_funct_1 @ sk_C))),
% 0.38/0.56      inference('sup-', [status(thm)], ['61', '62'])).
% 0.38/0.56  thf('64', plain, ((v1_funct_1 @ sk_C)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('65', plain, ((v2_funct_1 @ sk_C)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('66', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.38/0.56      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.38/0.56  thf('67', plain,
% 0.38/0.56      (((k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.38/0.56         = (k2_funct_1 @ sk_C))),
% 0.38/0.56      inference('demod', [status(thm)], ['56', '66'])).
% 0.38/0.56  thf('68', plain,
% 0.38/0.56      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.38/0.56        (k1_zfmisc_1 @ 
% 0.38/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.38/0.56      inference('demod', [status(thm)], ['53', '67'])).
% 0.38/0.56  thf('69', plain,
% 0.38/0.56      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.38/0.56         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 0.38/0.56          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.38/0.56      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.38/0.56  thf('70', plain,
% 0.38/0.56      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.56         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['68', '69'])).
% 0.38/0.56  thf('71', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.38/0.56      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.38/0.56  thf(t37_relat_1, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( v1_relat_1 @ A ) =>
% 0.38/0.56       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.38/0.56         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.38/0.56  thf('72', plain,
% 0.38/0.56      (![X4 : $i]:
% 0.38/0.56         (((k2_relat_1 @ X4) = (k1_relat_1 @ (k4_relat_1 @ X4)))
% 0.38/0.56          | ~ (v1_relat_1 @ X4))),
% 0.38/0.56      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.38/0.56  thf('73', plain,
% 0.38/0.56      ((((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.38/0.56        | ~ (v1_relat_1 @ sk_C))),
% 0.38/0.56      inference('sup+', [status(thm)], ['71', '72'])).
% 0.38/0.56  thf('74', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.56      inference('demod', [status(thm)], ['59', '60'])).
% 0.38/0.56  thf('75', plain,
% 0.38/0.56      (((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.38/0.56      inference('demod', [status(thm)], ['73', '74'])).
% 0.38/0.56  thf('76', plain,
% 0.38/0.56      (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.56         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 0.38/0.56      inference('demod', [status(thm)], ['70', '75'])).
% 0.38/0.56  thf('77', plain,
% 0.38/0.56      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.38/0.56         = (k2_funct_1 @ sk_C))),
% 0.38/0.56      inference('simplify', [status(thm)], ['49'])).
% 0.38/0.56  thf('78', plain,
% 0.38/0.56      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.38/0.56        (k1_zfmisc_1 @ 
% 0.38/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.38/0.56      inference('demod', [status(thm)], ['53', '67'])).
% 0.38/0.56  thf('79', plain,
% 0.38/0.56      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.38/0.56         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 0.38/0.56          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.38/0.56      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.38/0.56  thf('80', plain,
% 0.38/0.56      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.56         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['78', '79'])).
% 0.38/0.56  thf('81', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.38/0.56      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.38/0.56  thf('82', plain,
% 0.38/0.56      (![X4 : $i]:
% 0.38/0.56         (((k1_relat_1 @ X4) = (k2_relat_1 @ (k4_relat_1 @ X4)))
% 0.38/0.56          | ~ (v1_relat_1 @ X4))),
% 0.38/0.56      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.38/0.56  thf('83', plain,
% 0.38/0.56      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.38/0.56        | ~ (v1_relat_1 @ sk_C))),
% 0.38/0.56      inference('sup+', [status(thm)], ['81', '82'])).
% 0.38/0.56  thf('84', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.56      inference('demod', [status(thm)], ['59', '60'])).
% 0.38/0.56  thf('85', plain,
% 0.38/0.56      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.38/0.56      inference('demod', [status(thm)], ['83', '84'])).
% 0.38/0.56  thf('86', plain,
% 0.38/0.56      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.38/0.56         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.38/0.56      inference('demod', [status(thm)], ['80', '85'])).
% 0.38/0.56  thf('87', plain,
% 0.38/0.56      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.38/0.56        | ((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A)))),
% 0.38/0.56      inference('demod', [status(thm)], ['36', '50', '76', '77', '86'])).
% 0.38/0.56  thf('88', plain, (((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))),
% 0.38/0.56      inference('simplify', [status(thm)], ['87'])).
% 0.38/0.56  thf('89', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.38/0.56      inference('simplify_reflect-', [status(thm)], ['33', '88'])).
% 0.38/0.56  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.38/0.56  thf('90', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.38/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.38/0.56  thf('91', plain, ($false),
% 0.38/0.56      inference('demod', [status(thm)], ['10', '89', '90'])).
% 0.38/0.56  
% 0.38/0.56  % SZS output end Refutation
% 0.38/0.56  
% 0.38/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
