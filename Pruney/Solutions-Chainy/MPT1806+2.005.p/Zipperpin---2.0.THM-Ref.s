%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8MsWfIQ0jZ

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:03 EST 2020

% Result     : Theorem 0.86s
% Output     : Refutation 0.86s
% Verified   : 
% Statistics : Number of formulae       :  286 (6845 expanded)
%              Number of leaves         :   41 (1978 expanded)
%              Depth                    :   29
%              Number of atoms          : 3103 (183238 expanded)
%              Number of equality atoms :   67 ( 960 expanded)
%              Maximal formula depth    :   23 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k7_tmap_1_type,type,(
    k7_tmap_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k9_tmap_1_type,type,(
    k9_tmap_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k8_tmap_1_type,type,(
    k8_tmap_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t122_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( ( v1_tsep_1 @ B @ A )
              & ( m1_pre_topc @ B @ A ) )
          <=> ( ( v1_funct_1 @ ( k9_tmap_1 @ A @ B ) )
              & ( v1_funct_2 @ ( k9_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) )
              & ( v5_pre_topc @ ( k9_tmap_1 @ A @ B ) @ A @ ( k8_tmap_1 @ A @ B ) )
              & ( m1_subset_1 @ ( k9_tmap_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_pre_topc @ B @ A )
           => ( ( ( v1_tsep_1 @ B @ A )
                & ( m1_pre_topc @ B @ A ) )
            <=> ( ( v1_funct_1 @ ( k9_tmap_1 @ A @ B ) )
                & ( v1_funct_2 @ ( k9_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) )
                & ( v5_pre_topc @ ( k9_tmap_1 @ A @ B ) @ A @ ( k8_tmap_1 @ A @ B ) )
                & ( m1_subset_1 @ ( k9_tmap_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t122_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_pre_topc @ X32 @ X33 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X32 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('3',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(dt_k7_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) )
        & ( v1_funct_2 @ ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) )
        & ( m1_subset_1 @ ( k7_tmap_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( v1_funct_2 @ ( k7_tmap_1 @ X22 @ X23 ) @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('7',plain,
    ( ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(d10_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k7_tmap_1 @ A @ B )
            = ( k6_partfun1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('9',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( ( k7_tmap_1 @ X10 @ X9 )
        = ( k6_partfun1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_tmap_1])).

thf('10',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(d11_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( ( v1_pre_topc @ C )
                & ( v2_pre_topc @ C )
                & ( l1_pre_topc @ C ) )
             => ( ( C
                  = ( k8_tmap_1 @ A @ B ) )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                   => ( ( D
                        = ( u1_struct_0 @ B ) )
                     => ( C
                        = ( k6_tmap_1 @ A @ D ) ) ) ) ) ) ) ) )).

thf('17',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( X13
       != ( k8_tmap_1 @ X12 @ X11 ) )
      | ( X14
       != ( u1_struct_0 @ X11 ) )
      | ( X13
        = ( k6_tmap_1 @ X12 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ~ ( v1_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d11_tmap_1])).

thf('18',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v1_pre_topc @ ( k8_tmap_1 @ X12 @ X11 ) )
      | ~ ( v2_pre_topc @ ( k8_tmap_1 @ X12 @ X11 ) )
      | ~ ( l1_pre_topc @ ( k8_tmap_1 @ X12 @ X11 ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( ( k8_tmap_1 @ X12 @ X11 )
        = ( k6_tmap_1 @ X12 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( m1_pre_topc @ X11 @ X12 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ~ ( m1_pre_topc @ sk_B_1 @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_B_1 )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_pre_topc @ B @ A ) )
     => ( ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) )
        & ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) )
        & ( l1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ) )).

thf('22',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X25 @ X24 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('23',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X25 @ X24 )
      | ( v2_pre_topc @ ( k8_tmap_1 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('31',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_pre_topc @ X25 @ X24 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('39',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B_1 )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['19','20','28','36','44','45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B_1 )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t104_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) )
              = ( u1_struct_0 @ A ) )
            & ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) )
              = ( k5_tmap_1 @ A @ B ) ) ) ) ) )).

thf('51',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X29 @ X28 ) )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('52',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B_1 )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('59',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['7','15','49','59','60','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('66',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( m1_subset_1 @ ( k7_tmap_1 @ X22 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X22 @ X23 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('67',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('69',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B_1 )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('70',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('71',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68','69','70','71','72'])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) )
    | ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ) ),
    inference(split,[status(esa)],['76'])).

thf(d12_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) )
             => ( ( C
                  = ( k9_tmap_1 @ A @ B ) )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                   => ( ( D
                        = ( u1_struct_0 @ B ) )
                     => ( r1_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ D ) ) @ C @ ( k7_tmap_1 @ A @ D ) ) ) ) ) ) ) ) )).

thf('78',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( X17
       != ( k9_tmap_1 @ X16 @ X15 ) )
      | ( X18
       != ( u1_struct_0 @ X15 ) )
      | ( r1_funct_2 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X16 @ X15 ) ) @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X16 @ X18 ) ) @ X17 @ ( k7_tmap_1 @ X16 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X16 @ X15 ) ) ) ) )
      | ~ ( v1_funct_2 @ X17 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X16 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d12_tmap_1])).

thf('79',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v1_funct_1 @ ( k9_tmap_1 @ X16 @ X15 ) )
      | ~ ( v1_funct_2 @ ( k9_tmap_1 @ X16 @ X15 ) @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X16 @ X15 ) ) )
      | ~ ( m1_subset_1 @ ( k9_tmap_1 @ X16 @ X15 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X16 @ X15 ) ) ) ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( r1_funct_2 @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X16 @ X15 ) ) @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X16 @ ( u1_struct_0 @ X15 ) ) ) @ ( k9_tmap_1 @ X16 @ X15 ) @ ( k7_tmap_1 @ X16 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( m1_pre_topc @ X15 @ X16 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ( ~ ( m1_pre_topc @ sk_B_1 @ sk_A )
      | ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ) @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) )
      | ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['77','79'])).

thf('81',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('83',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B_1 )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('84',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('85',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('86',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('87',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('88',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_pre_topc @ B @ A ) )
     => ( ( v1_funct_1 @ ( k9_tmap_1 @ A @ B ) )
        & ( v1_funct_2 @ ( k9_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) )
        & ( m1_subset_1 @ ( k9_tmap_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) )).

thf('89',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ( v1_funct_2 @ ( k9_tmap_1 @ X26 @ X27 ) @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_tmap_1])).

thf('90',plain,
    ( ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('97',plain,(
    v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ( v1_funct_1 @ ( k9_tmap_1 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_tmap_1])).

thf('100',plain,
    ( ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('106',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['80','81','82','83','84','85','86','87','97','105','106','107'])).

thf('109',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ) ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('112',plain,
    ( ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ) ),
    inference(split,[status(esa)],['76'])).

thf('113',plain,
    ( ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf(redefinition_r1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ~ ( v1_xboole_0 @ B )
        & ~ ( v1_xboole_0 @ D )
        & ( v1_funct_1 @ E )
        & ( v1_funct_2 @ E @ A @ B )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( v1_funct_2 @ F @ C @ D )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F )
      <=> ( E = F ) ) ) )).

thf('114',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) )
      | ~ ( v1_funct_2 @ X3 @ X4 @ X5 )
      | ~ ( v1_funct_1 @ X3 )
      | ( v1_xboole_0 @ X6 )
      | ( v1_xboole_0 @ X5 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_funct_2 @ X7 @ X8 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X6 ) ) )
      | ( X3 = X7 )
      | ~ ( r1_funct_2 @ X4 @ X5 @ X8 @ X6 @ X3 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_funct_2])).

thf('115',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ X2 @ X1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ X0 )
        | ( ( k9_tmap_1 @ sk_A @ sk_B_1 )
          = X0 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
        | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
        | ~ ( v1_funct_1 @ X0 )
        | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
        | ( v1_xboole_0 @ X1 )
        | ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) )
        | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('117',plain,(
    v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('118',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ X2 @ X1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ X0 )
        | ( ( k9_tmap_1 @ sk_A @ sk_B_1 )
          = X0 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
        | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
        | ~ ( v1_funct_1 @ X0 )
        | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
        | ( v1_xboole_0 @ X1 ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['115','116','117'])).

thf('119',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( ( k9_tmap_1 @ sk_A @ sk_B_1 )
        = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['110','118'])).

thf('120',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('121',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( v1_funct_1 @ ( k7_tmap_1 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('122',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['122','123','124'])).

thf('126',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('129',plain,(
    v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( ( k9_tmap_1 @ sk_A @ sk_B_1 )
        = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['119','129'])).

thf('131',plain,
    ( ( ( ( k9_tmap_1 @ sk_A @ sk_B_1 )
        = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k9_tmap_1 @ sk_A @ sk_B_1 )
        = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['75','131'])).

thf('133',plain,
    ( ( ( ( k9_tmap_1 @ sk_A @ sk_B_1 )
        = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['64','132'])).

thf('134',plain,
    ( ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
   <= ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['134'])).

thf('136',plain,
    ( ( ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
      & ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ) ) ),
    inference('sup+',[status(thm)],['133','135'])).

thf('137',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ( m1_subset_1 @ ( k9_tmap_1 @ X26 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X26 @ X27 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_tmap_1])).

thf('139',plain,
    ( ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('141',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['139','140','141','142'])).

thf('144',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['143','144'])).

thf('146',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('147',plain,
    ( ~ ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) )
    | ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ~ ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) )
   <= ~ ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ) ),
    inference(split,[status(esa)],['147'])).

thf('149',plain,
    ( ~ ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ~ ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['146','148'])).

thf('150',plain,(
    m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['145','149'])).

thf('151',plain,(
    m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['150'])).

thf('152',plain,
    ( ( ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(simpl_trail,[status(thm)],['136','151'])).

thf('153',plain,
    ( ~ ( v1_tsep_1 @ sk_B_1 @ sk_A )
    | ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ) ),
    inference(split,[status(esa)],['147'])).

thf('154',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ~ ( m1_pre_topc @ sk_B_1 @ sk_A )
   <= ~ ( m1_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['147'])).

thf('156',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('158',plain,
    ( ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) )
   <= ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['147'])).

thf('159',plain,(
    v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('161',plain,
    ( ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) )
   <= ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference(split,[status(esa)],['147'])).

thf('162',plain,(
    v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,
    ( ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ( v1_tsep_1 @ sk_B_1 @ sk_A )
   <= ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['163'])).

thf('165',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(d1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_tsep_1 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( C
                    = ( u1_struct_0 @ B ) )
                 => ( v3_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('166',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ~ ( v1_tsep_1 @ X19 @ X20 )
      | ( X21
       != ( u1_struct_0 @ X19 ) )
      | ( v3_pre_topc @ X21 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('167',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X19 ) @ X20 )
      | ~ ( v1_tsep_1 @ X19 @ X20 )
      | ~ ( m1_pre_topc @ X19 @ X20 ) ) ),
    inference(simplify,[status(thm)],['166'])).

thf('168',plain,
    ( ~ ( m1_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B_1 @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['165','167'])).

thf('169',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,
    ( ~ ( v1_tsep_1 @ sk_B_1 @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['168','169','170'])).

thf('172',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ sk_A )
   <= ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['164','171'])).

thf('173',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t113_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) )
              & ( v1_funct_2 @ ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) )
              & ( v5_pre_topc @ ( k7_tmap_1 @ A @ B ) @ A @ ( k6_tmap_1 @ A @ B ) )
              & ( m1_subset_1 @ ( k7_tmap_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) )).

thf('174',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( v3_pre_topc @ X30 @ X31 )
      | ( v5_pre_topc @ ( k7_tmap_1 @ X31 @ X30 ) @ X31 @ ( k6_tmap_1 @ X31 @ X30 ) )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t113_tmap_1])).

thf('175',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('179',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B_1 )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('180',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['175','176','177','178','179'])).

thf('181',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ sk_A )
    | ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['180','181'])).

thf('183',plain,
    ( ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
   <= ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['172','182'])).

thf('184',plain,
    ( ( ( ( k9_tmap_1 @ sk_A @ sk_B_1 )
        = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['64','132'])).

thf('185',plain,
    ( ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
   <= ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['147'])).

thf('186',plain,
    ( ( ~ ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
      & ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['150'])).

thf('188',plain,
    ( ( ~ ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(simpl_trail,[status(thm)],['186','187'])).

thf('189',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
      & ( v1_tsep_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['183','188'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('190',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('191',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
      & ( v1_tsep_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('193',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('194',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
      & ( v1_tsep_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['191','194'])).

thf('196',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,
    ( ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,
    ( ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['134'])).

thf('199',plain,(
    v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B_1 ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['153','156','159','162','150','197','198'])).

thf('200',plain,
    ( ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['152','199'])).

thf('201',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('202',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( v1_funct_1 @ ( k7_tmap_1 @ X31 @ X30 ) )
      | ~ ( v1_funct_2 @ ( k7_tmap_1 @ X31 @ X30 ) @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X31 @ X30 ) ) )
      | ~ ( v5_pre_topc @ ( k7_tmap_1 @ X31 @ X30 ) @ X31 @ ( k6_tmap_1 @ X31 @ X30 ) )
      | ~ ( m1_subset_1 @ ( k7_tmap_1 @ X31 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X31 @ X30 ) ) ) ) )
      | ( v3_pre_topc @ X30 @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t113_tmap_1])).

thf('203',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ sk_A )
    | ~ ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) )
    | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['201','202'])).

thf('204',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B_1 )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('205',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('206',plain,(
    m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('207',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('210',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B_1 )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('211',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('212',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B_1 )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('213',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('214',plain,(
    v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('215',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B_1 ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('216',plain,(
    v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('217',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('218',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ sk_A )
    | ~ ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['203','204','205','206','207','208','209','210','211','212','213','214','215','216','217'])).

thf('219',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,
    ( ~ ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['218','219'])).

thf('221',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( ( sk_C @ X19 @ X20 )
        = ( u1_struct_0 @ X19 ) )
      | ( v1_tsep_1 @ X19 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('223',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tsep_1 @ sk_B_1 @ sk_A )
    | ( ( sk_C @ sk_B_1 @ sk_A )
      = ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['221','222'])).

thf('224',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,
    ( ( v1_tsep_1 @ sk_B_1 @ sk_A )
    | ( ( sk_C @ sk_B_1 @ sk_A )
      = ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['223','224'])).

thf('226',plain,
    ( ~ ( v1_tsep_1 @ sk_B_1 @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['147'])).

thf('227',plain,
    ( ( ( sk_C @ sk_B_1 @ sk_A )
      = ( u1_struct_0 @ sk_B_1 ) )
   <= ~ ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['225','226'])).

thf('228',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ~ ( v3_pre_topc @ ( sk_C @ X19 @ X20 ) @ X20 )
      | ( v1_tsep_1 @ X19 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('229',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_tsep_1 @ sk_B_1 @ sk_A )
      | ~ ( m1_pre_topc @ sk_B_1 @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['227','228'])).

thf('230',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ sk_A )
      | ( v1_tsep_1 @ sk_B_1 @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['229','230','231'])).

thf('233',plain,
    ( ~ ( v1_tsep_1 @ sk_B_1 @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['147'])).

thf('234',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['232','233'])).

thf('235',plain,(
    ~ ( v1_tsep_1 @ sk_B_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['153','156','159','162','150','197'])).

thf('236',plain,(
    ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['234','235'])).

thf('237',plain,(
    ~ ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['220','236'])).

thf('238',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['200','237'])).

thf('239',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('240',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['238','239'])).

thf('241',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['192','193'])).

thf('242',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['240','241'])).

thf('243',plain,(
    $false ),
    inference(demod,[status(thm)],['0','242'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8MsWfIQ0jZ
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:33:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.86/1.04  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.86/1.04  % Solved by: fo/fo7.sh
% 0.86/1.04  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.86/1.04  % done 384 iterations in 0.592s
% 0.86/1.04  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.86/1.04  % SZS output start Refutation
% 0.86/1.04  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.86/1.04  thf(sk_A_type, type, sk_A: $i).
% 0.86/1.04  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.86/1.04  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.86/1.04  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.86/1.04  thf(k7_tmap_1_type, type, k7_tmap_1: $i > $i > $i).
% 0.86/1.04  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.86/1.04  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.86/1.04  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.86/1.04  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.86/1.04  thf(k9_tmap_1_type, type, k9_tmap_1: $i > $i > $i).
% 0.86/1.04  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.86/1.04  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.86/1.04  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.86/1.04  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.86/1.04  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.86/1.04  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 0.86/1.04  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.86/1.04  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.86/1.04  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.86/1.04  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.86/1.04  thf(k8_tmap_1_type, type, k8_tmap_1: $i > $i > $i).
% 0.86/1.04  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.86/1.04  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 0.86/1.04  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.86/1.04  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.86/1.04  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.86/1.04  thf(t122_tmap_1, conjecture,
% 0.86/1.04    (![A:$i]:
% 0.86/1.04     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.86/1.04       ( ![B:$i]:
% 0.86/1.04         ( ( m1_pre_topc @ B @ A ) =>
% 0.86/1.04           ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.86/1.04             ( ( v1_funct_1 @ ( k9_tmap_1 @ A @ B ) ) & 
% 0.86/1.04               ( v1_funct_2 @
% 0.86/1.04                 ( k9_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.86/1.04                 ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 0.86/1.04               ( v5_pre_topc @
% 0.86/1.04                 ( k9_tmap_1 @ A @ B ) @ A @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.86/1.04               ( m1_subset_1 @
% 0.86/1.04                 ( k9_tmap_1 @ A @ B ) @ 
% 0.86/1.04                 ( k1_zfmisc_1 @
% 0.86/1.04                   ( k2_zfmisc_1 @
% 0.86/1.04                     ( u1_struct_0 @ A ) @ 
% 0.86/1.04                     ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) ))).
% 0.86/1.04  thf(zf_stmt_0, negated_conjecture,
% 0.86/1.04    (~( ![A:$i]:
% 0.86/1.04        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.86/1.04            ( l1_pre_topc @ A ) ) =>
% 0.86/1.04          ( ![B:$i]:
% 0.86/1.04            ( ( m1_pre_topc @ B @ A ) =>
% 0.86/1.04              ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.86/1.04                ( ( v1_funct_1 @ ( k9_tmap_1 @ A @ B ) ) & 
% 0.86/1.04                  ( v1_funct_2 @
% 0.86/1.04                    ( k9_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.86/1.04                    ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 0.86/1.04                  ( v5_pre_topc @
% 0.86/1.04                    ( k9_tmap_1 @ A @ B ) @ A @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.86/1.04                  ( m1_subset_1 @
% 0.86/1.04                    ( k9_tmap_1 @ A @ B ) @ 
% 0.86/1.04                    ( k1_zfmisc_1 @
% 0.86/1.04                      ( k2_zfmisc_1 @
% 0.86/1.04                        ( u1_struct_0 @ A ) @ 
% 0.86/1.04                        ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) ) )),
% 0.86/1.04    inference('cnf.neg', [status(esa)], [t122_tmap_1])).
% 0.86/1.04  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('1', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf(t1_tsep_1, axiom,
% 0.86/1.04    (![A:$i]:
% 0.86/1.04     ( ( l1_pre_topc @ A ) =>
% 0.86/1.04       ( ![B:$i]:
% 0.86/1.04         ( ( m1_pre_topc @ B @ A ) =>
% 0.86/1.04           ( m1_subset_1 @
% 0.86/1.04             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.86/1.04  thf('2', plain,
% 0.86/1.04      (![X32 : $i, X33 : $i]:
% 0.86/1.04         (~ (m1_pre_topc @ X32 @ X33)
% 0.86/1.04          | (m1_subset_1 @ (u1_struct_0 @ X32) @ 
% 0.86/1.04             (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.86/1.04          | ~ (l1_pre_topc @ X33))),
% 0.86/1.04      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.86/1.04  thf('3', plain,
% 0.86/1.04      ((~ (l1_pre_topc @ sk_A)
% 0.86/1.04        | (m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.86/1.04           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.86/1.04      inference('sup-', [status(thm)], ['1', '2'])).
% 0.86/1.04  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('5', plain,
% 0.86/1.04      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.86/1.04        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.86/1.04      inference('demod', [status(thm)], ['3', '4'])).
% 0.86/1.04  thf(dt_k7_tmap_1, axiom,
% 0.86/1.04    (![A:$i,B:$i]:
% 0.86/1.04     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.86/1.04         ( l1_pre_topc @ A ) & 
% 0.86/1.04         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.86/1.04       ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) ) & 
% 0.86/1.04         ( v1_funct_2 @
% 0.86/1.04           ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.86/1.04           ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 0.86/1.04         ( m1_subset_1 @
% 0.86/1.04           ( k7_tmap_1 @ A @ B ) @ 
% 0.86/1.04           ( k1_zfmisc_1 @
% 0.86/1.04             ( k2_zfmisc_1 @
% 0.86/1.04               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ))).
% 0.86/1.04  thf('6', plain,
% 0.86/1.04      (![X22 : $i, X23 : $i]:
% 0.86/1.04         (~ (l1_pre_topc @ X22)
% 0.86/1.04          | ~ (v2_pre_topc @ X22)
% 0.86/1.04          | (v2_struct_0 @ X22)
% 0.86/1.04          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.86/1.04          | (v1_funct_2 @ (k7_tmap_1 @ X22 @ X23) @ (u1_struct_0 @ X22) @ 
% 0.86/1.04             (u1_struct_0 @ (k6_tmap_1 @ X22 @ X23))))),
% 0.86/1.04      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.86/1.04  thf('7', plain,
% 0.86/1.04      (((v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)) @ 
% 0.86/1.04         (u1_struct_0 @ sk_A) @ 
% 0.86/1.04         (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))))
% 0.86/1.04        | (v2_struct_0 @ sk_A)
% 0.86/1.04        | ~ (v2_pre_topc @ sk_A)
% 0.86/1.04        | ~ (l1_pre_topc @ sk_A))),
% 0.86/1.04      inference('sup-', [status(thm)], ['5', '6'])).
% 0.86/1.04  thf('8', plain,
% 0.86/1.04      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.86/1.04        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.86/1.04      inference('demod', [status(thm)], ['3', '4'])).
% 0.86/1.04  thf(d10_tmap_1, axiom,
% 0.86/1.04    (![A:$i]:
% 0.86/1.04     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.86/1.04       ( ![B:$i]:
% 0.86/1.04         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.86/1.04           ( ( k7_tmap_1 @ A @ B ) = ( k6_partfun1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.86/1.04  thf('9', plain,
% 0.86/1.04      (![X9 : $i, X10 : $i]:
% 0.86/1.04         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.86/1.04          | ((k7_tmap_1 @ X10 @ X9) = (k6_partfun1 @ (u1_struct_0 @ X10)))
% 0.86/1.04          | ~ (l1_pre_topc @ X10)
% 0.86/1.04          | ~ (v2_pre_topc @ X10)
% 0.86/1.04          | (v2_struct_0 @ X10))),
% 0.86/1.04      inference('cnf', [status(esa)], [d10_tmap_1])).
% 0.86/1.04  thf('10', plain,
% 0.86/1.04      (((v2_struct_0 @ sk_A)
% 0.86/1.04        | ~ (v2_pre_topc @ sk_A)
% 0.86/1.04        | ~ (l1_pre_topc @ sk_A)
% 0.86/1.04        | ((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))
% 0.86/1.04            = (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 0.86/1.04      inference('sup-', [status(thm)], ['8', '9'])).
% 0.86/1.04  thf('11', plain, ((v2_pre_topc @ sk_A)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('13', plain,
% 0.86/1.04      (((v2_struct_0 @ sk_A)
% 0.86/1.04        | ((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))
% 0.86/1.04            = (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 0.86/1.04      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.86/1.04  thf('14', plain, (~ (v2_struct_0 @ sk_A)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('15', plain,
% 0.86/1.04      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))
% 0.86/1.04         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.86/1.04      inference('clc', [status(thm)], ['13', '14'])).
% 0.86/1.04  thf('16', plain,
% 0.86/1.04      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.86/1.04        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.86/1.04      inference('demod', [status(thm)], ['3', '4'])).
% 0.86/1.04  thf(d11_tmap_1, axiom,
% 0.86/1.04    (![A:$i]:
% 0.86/1.04     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.86/1.04       ( ![B:$i]:
% 0.86/1.04         ( ( m1_pre_topc @ B @ A ) =>
% 0.86/1.04           ( ![C:$i]:
% 0.86/1.04             ( ( ( v1_pre_topc @ C ) & ( v2_pre_topc @ C ) & 
% 0.86/1.04                 ( l1_pre_topc @ C ) ) =>
% 0.86/1.04               ( ( ( C ) = ( k8_tmap_1 @ A @ B ) ) <=>
% 0.86/1.04                 ( ![D:$i]:
% 0.86/1.04                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.86/1.04                     ( ( ( D ) = ( u1_struct_0 @ B ) ) =>
% 0.86/1.04                       ( ( C ) = ( k6_tmap_1 @ A @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.86/1.04  thf('17', plain,
% 0.86/1.04      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.86/1.04         (~ (m1_pre_topc @ X11 @ X12)
% 0.86/1.04          | ((X13) != (k8_tmap_1 @ X12 @ X11))
% 0.86/1.04          | ((X14) != (u1_struct_0 @ X11))
% 0.86/1.04          | ((X13) = (k6_tmap_1 @ X12 @ X14))
% 0.86/1.04          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.86/1.04          | ~ (l1_pre_topc @ X13)
% 0.86/1.04          | ~ (v2_pre_topc @ X13)
% 0.86/1.04          | ~ (v1_pre_topc @ X13)
% 0.86/1.04          | ~ (l1_pre_topc @ X12)
% 0.86/1.04          | ~ (v2_pre_topc @ X12)
% 0.86/1.04          | (v2_struct_0 @ X12))),
% 0.86/1.04      inference('cnf', [status(esa)], [d11_tmap_1])).
% 0.86/1.04  thf('18', plain,
% 0.86/1.04      (![X11 : $i, X12 : $i]:
% 0.86/1.04         ((v2_struct_0 @ X12)
% 0.86/1.04          | ~ (v2_pre_topc @ X12)
% 0.86/1.04          | ~ (l1_pre_topc @ X12)
% 0.86/1.04          | ~ (v1_pre_topc @ (k8_tmap_1 @ X12 @ X11))
% 0.86/1.04          | ~ (v2_pre_topc @ (k8_tmap_1 @ X12 @ X11))
% 0.86/1.04          | ~ (l1_pre_topc @ (k8_tmap_1 @ X12 @ X11))
% 0.86/1.04          | ~ (m1_subset_1 @ (u1_struct_0 @ X11) @ 
% 0.86/1.04               (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.86/1.04          | ((k8_tmap_1 @ X12 @ X11) = (k6_tmap_1 @ X12 @ (u1_struct_0 @ X11)))
% 0.86/1.04          | ~ (m1_pre_topc @ X11 @ X12))),
% 0.86/1.04      inference('simplify', [status(thm)], ['17'])).
% 0.86/1.04  thf('19', plain,
% 0.86/1.04      ((~ (m1_pre_topc @ sk_B_1 @ sk_A)
% 0.86/1.04        | ((k8_tmap_1 @ sk_A @ sk_B_1)
% 0.86/1.04            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 0.86/1.04        | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))
% 0.86/1.04        | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))
% 0.86/1.04        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))
% 0.86/1.04        | ~ (l1_pre_topc @ sk_A)
% 0.86/1.04        | ~ (v2_pre_topc @ sk_A)
% 0.86/1.04        | (v2_struct_0 @ sk_A))),
% 0.86/1.04      inference('sup-', [status(thm)], ['16', '18'])).
% 0.86/1.04  thf('20', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('21', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf(dt_k8_tmap_1, axiom,
% 0.86/1.04    (![A:$i,B:$i]:
% 0.86/1.04     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.86/1.04         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.86/1.04       ( ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.86/1.04         ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.86/1.04         ( l1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ))).
% 0.86/1.04  thf('22', plain,
% 0.86/1.04      (![X24 : $i, X25 : $i]:
% 0.86/1.04         (~ (l1_pre_topc @ X24)
% 0.86/1.04          | ~ (v2_pre_topc @ X24)
% 0.86/1.04          | (v2_struct_0 @ X24)
% 0.86/1.04          | ~ (m1_pre_topc @ X25 @ X24)
% 0.86/1.04          | (l1_pre_topc @ (k8_tmap_1 @ X24 @ X25)))),
% 0.86/1.04      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.86/1.04  thf('23', plain,
% 0.86/1.04      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))
% 0.86/1.04        | (v2_struct_0 @ sk_A)
% 0.86/1.04        | ~ (v2_pre_topc @ sk_A)
% 0.86/1.04        | ~ (l1_pre_topc @ sk_A))),
% 0.86/1.04      inference('sup-', [status(thm)], ['21', '22'])).
% 0.86/1.04  thf('24', plain, ((v2_pre_topc @ sk_A)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('26', plain,
% 0.86/1.04      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.86/1.04      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.86/1.04  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('28', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))),
% 0.86/1.04      inference('clc', [status(thm)], ['26', '27'])).
% 0.86/1.04  thf('29', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('30', plain,
% 0.86/1.04      (![X24 : $i, X25 : $i]:
% 0.86/1.04         (~ (l1_pre_topc @ X24)
% 0.86/1.04          | ~ (v2_pre_topc @ X24)
% 0.86/1.04          | (v2_struct_0 @ X24)
% 0.86/1.04          | ~ (m1_pre_topc @ X25 @ X24)
% 0.86/1.04          | (v2_pre_topc @ (k8_tmap_1 @ X24 @ X25)))),
% 0.86/1.04      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.86/1.04  thf('31', plain,
% 0.86/1.04      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))
% 0.86/1.04        | (v2_struct_0 @ sk_A)
% 0.86/1.04        | ~ (v2_pre_topc @ sk_A)
% 0.86/1.04        | ~ (l1_pre_topc @ sk_A))),
% 0.86/1.04      inference('sup-', [status(thm)], ['29', '30'])).
% 0.86/1.04  thf('32', plain, ((v2_pre_topc @ sk_A)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('34', plain,
% 0.86/1.04      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.86/1.04      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.86/1.04  thf('35', plain, (~ (v2_struct_0 @ sk_A)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('36', plain, ((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))),
% 0.86/1.04      inference('clc', [status(thm)], ['34', '35'])).
% 0.86/1.04  thf('37', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('38', plain,
% 0.86/1.04      (![X24 : $i, X25 : $i]:
% 0.86/1.04         (~ (l1_pre_topc @ X24)
% 0.86/1.04          | ~ (v2_pre_topc @ X24)
% 0.86/1.04          | (v2_struct_0 @ X24)
% 0.86/1.04          | ~ (m1_pre_topc @ X25 @ X24)
% 0.86/1.04          | (v1_pre_topc @ (k8_tmap_1 @ X24 @ X25)))),
% 0.86/1.04      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.86/1.04  thf('39', plain,
% 0.86/1.04      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))
% 0.86/1.04        | (v2_struct_0 @ sk_A)
% 0.86/1.04        | ~ (v2_pre_topc @ sk_A)
% 0.86/1.04        | ~ (l1_pre_topc @ sk_A))),
% 0.86/1.04      inference('sup-', [status(thm)], ['37', '38'])).
% 0.86/1.04  thf('40', plain, ((v2_pre_topc @ sk_A)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('42', plain,
% 0.86/1.04      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.86/1.04      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.86/1.04  thf('43', plain, (~ (v2_struct_0 @ sk_A)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('44', plain, ((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B_1))),
% 0.86/1.04      inference('clc', [status(thm)], ['42', '43'])).
% 0.86/1.04  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('46', plain, ((v2_pre_topc @ sk_A)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('47', plain,
% 0.86/1.04      ((((k8_tmap_1 @ sk_A @ sk_B_1)
% 0.86/1.04          = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 0.86/1.04        | (v2_struct_0 @ sk_A))),
% 0.86/1.04      inference('demod', [status(thm)],
% 0.86/1.04                ['19', '20', '28', '36', '44', '45', '46'])).
% 0.86/1.04  thf('48', plain, (~ (v2_struct_0 @ sk_A)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('49', plain,
% 0.86/1.04      (((k8_tmap_1 @ sk_A @ sk_B_1)
% 0.86/1.04         = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))),
% 0.86/1.04      inference('clc', [status(thm)], ['47', '48'])).
% 0.86/1.04  thf('50', plain,
% 0.86/1.04      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.86/1.04        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.86/1.04      inference('demod', [status(thm)], ['3', '4'])).
% 0.86/1.04  thf(t104_tmap_1, axiom,
% 0.86/1.04    (![A:$i]:
% 0.86/1.04     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.86/1.04       ( ![B:$i]:
% 0.86/1.04         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.86/1.04           ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.86/1.04             ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.86/1.04  thf('51', plain,
% 0.86/1.04      (![X28 : $i, X29 : $i]:
% 0.86/1.04         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.86/1.04          | ((u1_struct_0 @ (k6_tmap_1 @ X29 @ X28)) = (u1_struct_0 @ X29))
% 0.86/1.04          | ~ (l1_pre_topc @ X29)
% 0.86/1.04          | ~ (v2_pre_topc @ X29)
% 0.86/1.04          | (v2_struct_0 @ X29))),
% 0.86/1.04      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.86/1.04  thf('52', plain,
% 0.86/1.04      (((v2_struct_0 @ sk_A)
% 0.86/1.04        | ~ (v2_pre_topc @ sk_A)
% 0.86/1.04        | ~ (l1_pre_topc @ sk_A)
% 0.86/1.04        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 0.86/1.04            = (u1_struct_0 @ sk_A)))),
% 0.86/1.04      inference('sup-', [status(thm)], ['50', '51'])).
% 0.86/1.04  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('55', plain,
% 0.86/1.04      (((v2_struct_0 @ sk_A)
% 0.86/1.04        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 0.86/1.04            = (u1_struct_0 @ sk_A)))),
% 0.86/1.04      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.86/1.04  thf('56', plain, (~ (v2_struct_0 @ sk_A)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('57', plain,
% 0.86/1.04      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 0.86/1.04         = (u1_struct_0 @ sk_A))),
% 0.86/1.04      inference('clc', [status(thm)], ['55', '56'])).
% 0.86/1.04  thf('58', plain,
% 0.86/1.04      (((k8_tmap_1 @ sk_A @ sk_B_1)
% 0.86/1.04         = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))),
% 0.86/1.04      inference('clc', [status(thm)], ['47', '48'])).
% 0.86/1.04  thf('59', plain,
% 0.86/1.04      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A))),
% 0.86/1.04      inference('demod', [status(thm)], ['57', '58'])).
% 0.86/1.04  thf('60', plain, ((v2_pre_topc @ sk_A)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('62', plain,
% 0.86/1.04      (((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.86/1.04         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.86/1.04        | (v2_struct_0 @ sk_A))),
% 0.86/1.04      inference('demod', [status(thm)], ['7', '15', '49', '59', '60', '61'])).
% 0.86/1.04  thf('63', plain, (~ (v2_struct_0 @ sk_A)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('64', plain,
% 0.86/1.04      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.86/1.04        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.86/1.04      inference('clc', [status(thm)], ['62', '63'])).
% 0.86/1.04  thf('65', plain,
% 0.86/1.04      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.86/1.04        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.86/1.04      inference('demod', [status(thm)], ['3', '4'])).
% 0.86/1.04  thf('66', plain,
% 0.86/1.04      (![X22 : $i, X23 : $i]:
% 0.86/1.04         (~ (l1_pre_topc @ X22)
% 0.86/1.04          | ~ (v2_pre_topc @ X22)
% 0.86/1.04          | (v2_struct_0 @ X22)
% 0.86/1.04          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.86/1.04          | (m1_subset_1 @ (k7_tmap_1 @ X22 @ X23) @ 
% 0.86/1.04             (k1_zfmisc_1 @ 
% 0.86/1.04              (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ 
% 0.86/1.04               (u1_struct_0 @ (k6_tmap_1 @ X22 @ X23))))))),
% 0.86/1.04      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.86/1.04  thf('67', plain,
% 0.86/1.04      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)) @ 
% 0.86/1.04         (k1_zfmisc_1 @ 
% 0.86/1.04          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))))))
% 0.86/1.04        | (v2_struct_0 @ sk_A)
% 0.86/1.04        | ~ (v2_pre_topc @ sk_A)
% 0.86/1.04        | ~ (l1_pre_topc @ sk_A))),
% 0.86/1.04      inference('sup-', [status(thm)], ['65', '66'])).
% 0.86/1.04  thf('68', plain,
% 0.86/1.04      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))
% 0.86/1.04         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.86/1.04      inference('clc', [status(thm)], ['13', '14'])).
% 0.86/1.04  thf('69', plain,
% 0.86/1.04      (((k8_tmap_1 @ sk_A @ sk_B_1)
% 0.86/1.04         = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))),
% 0.86/1.04      inference('clc', [status(thm)], ['47', '48'])).
% 0.86/1.04  thf('70', plain,
% 0.86/1.04      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A))),
% 0.86/1.04      inference('demod', [status(thm)], ['57', '58'])).
% 0.86/1.04  thf('71', plain, ((v2_pre_topc @ sk_A)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('73', plain,
% 0.86/1.04      (((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.86/1.04         (k1_zfmisc_1 @ 
% 0.86/1.04          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.86/1.04        | (v2_struct_0 @ sk_A))),
% 0.86/1.04      inference('demod', [status(thm)], ['67', '68', '69', '70', '71', '72'])).
% 0.86/1.04  thf('74', plain, (~ (v2_struct_0 @ sk_A)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('75', plain,
% 0.86/1.04      ((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.86/1.04        (k1_zfmisc_1 @ 
% 0.86/1.04         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 0.86/1.04      inference('clc', [status(thm)], ['73', '74'])).
% 0.86/1.04  thf('76', plain,
% 0.86/1.04      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.86/1.04         (k1_zfmisc_1 @ 
% 0.86/1.04          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))
% 0.86/1.04        | (v1_tsep_1 @ sk_B_1 @ sk_A))),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('77', plain,
% 0.86/1.04      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.86/1.04         (k1_zfmisc_1 @ 
% 0.86/1.04          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1))))))
% 0.86/1.04         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.86/1.04               (k1_zfmisc_1 @ 
% 0.86/1.04                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))))),
% 0.86/1.04      inference('split', [status(esa)], ['76'])).
% 0.86/1.04  thf(d12_tmap_1, axiom,
% 0.86/1.04    (![A:$i]:
% 0.86/1.04     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.86/1.04       ( ![B:$i]:
% 0.86/1.04         ( ( m1_pre_topc @ B @ A ) =>
% 0.86/1.04           ( ![C:$i]:
% 0.86/1.04             ( ( ( v1_funct_1 @ C ) & 
% 0.86/1.04                 ( v1_funct_2 @
% 0.86/1.04                   C @ ( u1_struct_0 @ A ) @ 
% 0.86/1.04                   ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 0.86/1.04                 ( m1_subset_1 @
% 0.86/1.04                   C @ 
% 0.86/1.04                   ( k1_zfmisc_1 @
% 0.86/1.04                     ( k2_zfmisc_1 @
% 0.86/1.04                       ( u1_struct_0 @ A ) @ 
% 0.86/1.04                       ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) =>
% 0.86/1.04               ( ( ( C ) = ( k9_tmap_1 @ A @ B ) ) <=>
% 0.86/1.04                 ( ![D:$i]:
% 0.86/1.04                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.86/1.04                     ( ( ( D ) = ( u1_struct_0 @ B ) ) =>
% 0.86/1.04                       ( r1_funct_2 @
% 0.86/1.04                         ( u1_struct_0 @ A ) @ 
% 0.86/1.04                         ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) @ 
% 0.86/1.04                         ( u1_struct_0 @ A ) @ 
% 0.86/1.04                         ( u1_struct_0 @ ( k6_tmap_1 @ A @ D ) ) @ C @ 
% 0.86/1.04                         ( k7_tmap_1 @ A @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.86/1.04  thf('78', plain,
% 0.86/1.04      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.86/1.04         (~ (m1_pre_topc @ X15 @ X16)
% 0.86/1.04          | ((X17) != (k9_tmap_1 @ X16 @ X15))
% 0.86/1.04          | ((X18) != (u1_struct_0 @ X15))
% 0.86/1.04          | (r1_funct_2 @ (u1_struct_0 @ X16) @ 
% 0.86/1.04             (u1_struct_0 @ (k8_tmap_1 @ X16 @ X15)) @ (u1_struct_0 @ X16) @ 
% 0.86/1.04             (u1_struct_0 @ (k6_tmap_1 @ X16 @ X18)) @ X17 @ 
% 0.86/1.04             (k7_tmap_1 @ X16 @ X18))
% 0.86/1.04          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.86/1.04          | ~ (m1_subset_1 @ X17 @ 
% 0.86/1.04               (k1_zfmisc_1 @ 
% 0.86/1.04                (k2_zfmisc_1 @ (u1_struct_0 @ X16) @ 
% 0.86/1.04                 (u1_struct_0 @ (k8_tmap_1 @ X16 @ X15)))))
% 0.86/1.04          | ~ (v1_funct_2 @ X17 @ (u1_struct_0 @ X16) @ 
% 0.86/1.04               (u1_struct_0 @ (k8_tmap_1 @ X16 @ X15)))
% 0.86/1.04          | ~ (v1_funct_1 @ X17)
% 0.86/1.04          | ~ (l1_pre_topc @ X16)
% 0.86/1.04          | ~ (v2_pre_topc @ X16)
% 0.86/1.04          | (v2_struct_0 @ X16))),
% 0.86/1.04      inference('cnf', [status(esa)], [d12_tmap_1])).
% 0.86/1.04  thf('79', plain,
% 0.86/1.04      (![X15 : $i, X16 : $i]:
% 0.86/1.04         ((v2_struct_0 @ X16)
% 0.86/1.04          | ~ (v2_pre_topc @ X16)
% 0.86/1.04          | ~ (l1_pre_topc @ X16)
% 0.86/1.04          | ~ (v1_funct_1 @ (k9_tmap_1 @ X16 @ X15))
% 0.86/1.04          | ~ (v1_funct_2 @ (k9_tmap_1 @ X16 @ X15) @ (u1_struct_0 @ X16) @ 
% 0.86/1.04               (u1_struct_0 @ (k8_tmap_1 @ X16 @ X15)))
% 0.86/1.04          | ~ (m1_subset_1 @ (k9_tmap_1 @ X16 @ X15) @ 
% 0.86/1.04               (k1_zfmisc_1 @ 
% 0.86/1.04                (k2_zfmisc_1 @ (u1_struct_0 @ X16) @ 
% 0.86/1.04                 (u1_struct_0 @ (k8_tmap_1 @ X16 @ X15)))))
% 0.86/1.04          | ~ (m1_subset_1 @ (u1_struct_0 @ X15) @ 
% 0.86/1.04               (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.86/1.04          | (r1_funct_2 @ (u1_struct_0 @ X16) @ 
% 0.86/1.04             (u1_struct_0 @ (k8_tmap_1 @ X16 @ X15)) @ (u1_struct_0 @ X16) @ 
% 0.86/1.04             (u1_struct_0 @ (k6_tmap_1 @ X16 @ (u1_struct_0 @ X15))) @ 
% 0.86/1.04             (k9_tmap_1 @ X16 @ X15) @ (k7_tmap_1 @ X16 @ (u1_struct_0 @ X15)))
% 0.86/1.04          | ~ (m1_pre_topc @ X15 @ X16))),
% 0.86/1.04      inference('simplify', [status(thm)], ['78'])).
% 0.86/1.04  thf('80', plain,
% 0.86/1.04      (((~ (m1_pre_topc @ sk_B_1 @ sk_A)
% 0.86/1.04         | (r1_funct_2 @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04            (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) @ 
% 0.86/1.04            (u1_struct_0 @ sk_A) @ 
% 0.86/1.04            (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))) @ 
% 0.86/1.04            (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.86/1.04            (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 0.86/1.04         | ~ (m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.86/1.04              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.86/1.04         | ~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.86/1.04              (u1_struct_0 @ sk_A) @ 
% 0.86/1.04              (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))
% 0.86/1.04         | ~ (v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B_1))
% 0.86/1.04         | ~ (l1_pre_topc @ sk_A)
% 0.86/1.04         | ~ (v2_pre_topc @ sk_A)
% 0.86/1.04         | (v2_struct_0 @ sk_A)))
% 0.86/1.04         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.86/1.04               (k1_zfmisc_1 @ 
% 0.86/1.04                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))))),
% 0.86/1.04      inference('sup-', [status(thm)], ['77', '79'])).
% 0.86/1.04  thf('81', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('82', plain,
% 0.86/1.04      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A))),
% 0.86/1.04      inference('demod', [status(thm)], ['57', '58'])).
% 0.86/1.04  thf('83', plain,
% 0.86/1.04      (((k8_tmap_1 @ sk_A @ sk_B_1)
% 0.86/1.04         = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))),
% 0.86/1.04      inference('clc', [status(thm)], ['47', '48'])).
% 0.86/1.04  thf('84', plain,
% 0.86/1.04      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A))),
% 0.86/1.04      inference('demod', [status(thm)], ['57', '58'])).
% 0.86/1.04  thf('85', plain,
% 0.86/1.04      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))
% 0.86/1.04         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.86/1.04      inference('clc', [status(thm)], ['13', '14'])).
% 0.86/1.04  thf('86', plain,
% 0.86/1.04      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.86/1.04        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.86/1.04      inference('demod', [status(thm)], ['3', '4'])).
% 0.86/1.04  thf('87', plain,
% 0.86/1.04      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A))),
% 0.86/1.04      inference('demod', [status(thm)], ['57', '58'])).
% 0.86/1.04  thf('88', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf(dt_k9_tmap_1, axiom,
% 0.86/1.04    (![A:$i,B:$i]:
% 0.86/1.04     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.86/1.04         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.86/1.04       ( ( v1_funct_1 @ ( k9_tmap_1 @ A @ B ) ) & 
% 0.86/1.04         ( v1_funct_2 @
% 0.86/1.04           ( k9_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.86/1.04           ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 0.86/1.04         ( m1_subset_1 @
% 0.86/1.04           ( k9_tmap_1 @ A @ B ) @ 
% 0.86/1.04           ( k1_zfmisc_1 @
% 0.86/1.04             ( k2_zfmisc_1 @
% 0.86/1.04               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ))).
% 0.86/1.04  thf('89', plain,
% 0.86/1.04      (![X26 : $i, X27 : $i]:
% 0.86/1.04         (~ (l1_pre_topc @ X26)
% 0.86/1.04          | ~ (v2_pre_topc @ X26)
% 0.86/1.04          | (v2_struct_0 @ X26)
% 0.86/1.04          | ~ (m1_pre_topc @ X27 @ X26)
% 0.86/1.04          | (v1_funct_2 @ (k9_tmap_1 @ X26 @ X27) @ (u1_struct_0 @ X26) @ 
% 0.86/1.04             (u1_struct_0 @ (k8_tmap_1 @ X26 @ X27))))),
% 0.86/1.04      inference('cnf', [status(esa)], [dt_k9_tmap_1])).
% 0.86/1.04  thf('90', plain,
% 0.86/1.04      (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04         (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))
% 0.86/1.04        | (v2_struct_0 @ sk_A)
% 0.86/1.04        | ~ (v2_pre_topc @ sk_A)
% 0.86/1.04        | ~ (l1_pre_topc @ sk_A))),
% 0.86/1.04      inference('sup-', [status(thm)], ['88', '89'])).
% 0.86/1.04  thf('91', plain, ((v2_pre_topc @ sk_A)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('92', plain, ((l1_pre_topc @ sk_A)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('93', plain,
% 0.86/1.04      (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04         (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))
% 0.86/1.04        | (v2_struct_0 @ sk_A))),
% 0.86/1.04      inference('demod', [status(thm)], ['90', '91', '92'])).
% 0.86/1.04  thf('94', plain, (~ (v2_struct_0 @ sk_A)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('95', plain,
% 0.86/1.04      ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04        (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))),
% 0.86/1.04      inference('clc', [status(thm)], ['93', '94'])).
% 0.86/1.04  thf('96', plain,
% 0.86/1.04      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A))),
% 0.86/1.04      inference('demod', [status(thm)], ['57', '58'])).
% 0.86/1.04  thf('97', plain,
% 0.86/1.04      ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04        (u1_struct_0 @ sk_A))),
% 0.86/1.04      inference('demod', [status(thm)], ['95', '96'])).
% 0.86/1.04  thf('98', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('99', plain,
% 0.86/1.04      (![X26 : $i, X27 : $i]:
% 0.86/1.04         (~ (l1_pre_topc @ X26)
% 0.86/1.04          | ~ (v2_pre_topc @ X26)
% 0.86/1.04          | (v2_struct_0 @ X26)
% 0.86/1.04          | ~ (m1_pre_topc @ X27 @ X26)
% 0.86/1.04          | (v1_funct_1 @ (k9_tmap_1 @ X26 @ X27)))),
% 0.86/1.04      inference('cnf', [status(esa)], [dt_k9_tmap_1])).
% 0.86/1.04  thf('100', plain,
% 0.86/1.04      (((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B_1))
% 0.86/1.04        | (v2_struct_0 @ sk_A)
% 0.86/1.04        | ~ (v2_pre_topc @ sk_A)
% 0.86/1.04        | ~ (l1_pre_topc @ sk_A))),
% 0.86/1.04      inference('sup-', [status(thm)], ['98', '99'])).
% 0.86/1.04  thf('101', plain, ((v2_pre_topc @ sk_A)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('102', plain, ((l1_pre_topc @ sk_A)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('103', plain,
% 0.86/1.04      (((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.86/1.04      inference('demod', [status(thm)], ['100', '101', '102'])).
% 0.86/1.04  thf('104', plain, (~ (v2_struct_0 @ sk_A)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('105', plain, ((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B_1))),
% 0.86/1.04      inference('clc', [status(thm)], ['103', '104'])).
% 0.86/1.04  thf('106', plain, ((l1_pre_topc @ sk_A)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('107', plain, ((v2_pre_topc @ sk_A)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('108', plain,
% 0.86/1.04      ((((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04          (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04          (k9_tmap_1 @ sk_A @ sk_B_1) @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 0.86/1.04         | (v2_struct_0 @ sk_A)))
% 0.86/1.04         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.86/1.04               (k1_zfmisc_1 @ 
% 0.86/1.04                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))))),
% 0.86/1.04      inference('demod', [status(thm)],
% 0.86/1.04                ['80', '81', '82', '83', '84', '85', '86', '87', '97', '105', 
% 0.86/1.04                 '106', '107'])).
% 0.86/1.04  thf('109', plain, (~ (v2_struct_0 @ sk_A)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('110', plain,
% 0.86/1.04      (((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04         (k9_tmap_1 @ sk_A @ sk_B_1) @ (k6_partfun1 @ (u1_struct_0 @ sk_A))))
% 0.86/1.04         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.86/1.04               (k1_zfmisc_1 @ 
% 0.86/1.04                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))))),
% 0.86/1.04      inference('clc', [status(thm)], ['108', '109'])).
% 0.86/1.04  thf('111', plain,
% 0.86/1.04      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A))),
% 0.86/1.04      inference('demod', [status(thm)], ['57', '58'])).
% 0.86/1.04  thf('112', plain,
% 0.86/1.04      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.86/1.04         (k1_zfmisc_1 @ 
% 0.86/1.04          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1))))))
% 0.86/1.04         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.86/1.04               (k1_zfmisc_1 @ 
% 0.86/1.04                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))))),
% 0.86/1.04      inference('split', [status(esa)], ['76'])).
% 0.86/1.04  thf('113', plain,
% 0.86/1.04      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.86/1.04         (k1_zfmisc_1 @ 
% 0.86/1.04          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))
% 0.86/1.04         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.86/1.04               (k1_zfmisc_1 @ 
% 0.86/1.04                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))))),
% 0.86/1.04      inference('sup+', [status(thm)], ['111', '112'])).
% 0.86/1.04  thf(redefinition_r1_funct_2, axiom,
% 0.86/1.04    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.86/1.04     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 0.86/1.04         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 0.86/1.04         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.86/1.04         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 0.86/1.04         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.86/1.04       ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F ) <=> ( ( E ) = ( F ) ) ) ))).
% 0.86/1.04  thf('114', plain,
% 0.86/1.04      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.86/1.04         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5)))
% 0.86/1.04          | ~ (v1_funct_2 @ X3 @ X4 @ X5)
% 0.86/1.04          | ~ (v1_funct_1 @ X3)
% 0.86/1.04          | (v1_xboole_0 @ X6)
% 0.86/1.04          | (v1_xboole_0 @ X5)
% 0.86/1.04          | ~ (v1_funct_1 @ X7)
% 0.86/1.04          | ~ (v1_funct_2 @ X7 @ X8 @ X6)
% 0.86/1.04          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X6)))
% 0.86/1.04          | ((X3) = (X7))
% 0.86/1.04          | ~ (r1_funct_2 @ X4 @ X5 @ X8 @ X6 @ X3 @ X7))),
% 0.86/1.04      inference('cnf', [status(esa)], [redefinition_r1_funct_2])).
% 0.86/1.04  thf('115', plain,
% 0.86/1.04      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.86/1.04          (~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ X2 @ 
% 0.86/1.04              X1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ X0)
% 0.86/1.04           | ((k9_tmap_1 @ sk_A @ sk_B_1) = (X0))
% 0.86/1.04           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.86/1.04           | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 0.86/1.04           | ~ (v1_funct_1 @ X0)
% 0.86/1.04           | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.86/1.04           | (v1_xboole_0 @ X1)
% 0.86/1.04           | ~ (v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B_1))
% 0.86/1.04           | ~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.86/1.04                (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.86/1.04         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.86/1.04               (k1_zfmisc_1 @ 
% 0.86/1.04                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))))),
% 0.86/1.04      inference('sup-', [status(thm)], ['113', '114'])).
% 0.86/1.04  thf('116', plain, ((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B_1))),
% 0.86/1.04      inference('clc', [status(thm)], ['103', '104'])).
% 0.86/1.04  thf('117', plain,
% 0.86/1.04      ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04        (u1_struct_0 @ sk_A))),
% 0.86/1.04      inference('demod', [status(thm)], ['95', '96'])).
% 0.86/1.04  thf('118', plain,
% 0.86/1.04      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.86/1.04          (~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ X2 @ 
% 0.86/1.04              X1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ X0)
% 0.86/1.04           | ((k9_tmap_1 @ sk_A @ sk_B_1) = (X0))
% 0.86/1.04           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.86/1.04           | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 0.86/1.04           | ~ (v1_funct_1 @ X0)
% 0.86/1.04           | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.86/1.04           | (v1_xboole_0 @ X1)))
% 0.86/1.04         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.86/1.04               (k1_zfmisc_1 @ 
% 0.86/1.04                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))))),
% 0.86/1.04      inference('demod', [status(thm)], ['115', '116', '117'])).
% 0.86/1.04  thf('119', plain,
% 0.86/1.04      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.86/1.04         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.86/1.04         | ~ (v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 0.86/1.04         | ~ (v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.86/1.04              (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.86/1.04         | ~ (m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.86/1.04              (k1_zfmisc_1 @ 
% 0.86/1.04               (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.86/1.04         | ((k9_tmap_1 @ sk_A @ sk_B_1) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))))
% 0.86/1.04         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.86/1.04               (k1_zfmisc_1 @ 
% 0.86/1.04                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))))),
% 0.86/1.04      inference('sup-', [status(thm)], ['110', '118'])).
% 0.86/1.04  thf('120', plain,
% 0.86/1.04      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.86/1.04        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.86/1.04      inference('demod', [status(thm)], ['3', '4'])).
% 0.86/1.04  thf('121', plain,
% 0.86/1.04      (![X22 : $i, X23 : $i]:
% 0.86/1.04         (~ (l1_pre_topc @ X22)
% 0.86/1.04          | ~ (v2_pre_topc @ X22)
% 0.86/1.04          | (v2_struct_0 @ X22)
% 0.86/1.04          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.86/1.04          | (v1_funct_1 @ (k7_tmap_1 @ X22 @ X23)))),
% 0.86/1.04      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.86/1.04  thf('122', plain,
% 0.86/1.04      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 0.86/1.04        | (v2_struct_0 @ sk_A)
% 0.86/1.04        | ~ (v2_pre_topc @ sk_A)
% 0.86/1.04        | ~ (l1_pre_topc @ sk_A))),
% 0.86/1.04      inference('sup-', [status(thm)], ['120', '121'])).
% 0.86/1.04  thf('123', plain, ((v2_pre_topc @ sk_A)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('124', plain, ((l1_pre_topc @ sk_A)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('125', plain,
% 0.86/1.04      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 0.86/1.04        | (v2_struct_0 @ sk_A))),
% 0.86/1.04      inference('demod', [status(thm)], ['122', '123', '124'])).
% 0.86/1.04  thf('126', plain, (~ (v2_struct_0 @ sk_A)),
% 0.86/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.04  thf('127', plain,
% 0.86/1.04      ((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))),
% 0.86/1.04      inference('clc', [status(thm)], ['125', '126'])).
% 0.86/1.04  thf('128', plain,
% 0.86/1.04      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))
% 0.86/1.04         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.86/1.04      inference('clc', [status(thm)], ['13', '14'])).
% 0.86/1.04  thf('129', plain, ((v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.86/1.04      inference('demod', [status(thm)], ['127', '128'])).
% 0.86/1.04  thf('130', plain,
% 0.86/1.04      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.86/1.04         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.86/1.04         | ~ (v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.86/1.04              (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.86/1.04         | ~ (m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.86/1.04              (k1_zfmisc_1 @ 
% 0.86/1.04               (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.86/1.04         | ((k9_tmap_1 @ sk_A @ sk_B_1) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))))
% 0.86/1.04         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.86/1.04               (k1_zfmisc_1 @ 
% 0.86/1.04                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))))),
% 0.86/1.04      inference('demod', [status(thm)], ['119', '129'])).
% 0.86/1.04  thf('131', plain,
% 0.86/1.04      (((((k9_tmap_1 @ sk_A @ sk_B_1) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 0.86/1.04         | ~ (m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.86/1.04              (k1_zfmisc_1 @ 
% 0.86/1.04               (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.86/1.04         | ~ (v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.86/1.04              (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.86/1.04         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.86/1.04         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.86/1.04               (k1_zfmisc_1 @ 
% 0.86/1.04                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))))),
% 0.86/1.04      inference('simplify', [status(thm)], ['130'])).
% 0.86/1.04  thf('132', plain,
% 0.86/1.04      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.86/1.04         | ~ (v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.86/1.04              (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.86/1.04         | ((k9_tmap_1 @ sk_A @ sk_B_1) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))))
% 0.86/1.04         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.86/1.04               (k1_zfmisc_1 @ 
% 0.86/1.04                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))))),
% 0.86/1.04      inference('sup-', [status(thm)], ['75', '131'])).
% 0.86/1.04  thf('133', plain,
% 0.86/1.04      (((((k9_tmap_1 @ sk_A @ sk_B_1) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 0.86/1.04         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.86/1.04         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.86/1.04               (k1_zfmisc_1 @ 
% 0.86/1.04                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.04                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))))),
% 0.86/1.04      inference('sup-', [status(thm)], ['64', '132'])).
% 0.86/1.04  thf('134', plain,
% 0.86/1.04      (((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_A @ 
% 0.86/1.04         (k8_tmap_1 @ sk_A @ sk_B_1))
% 0.86/1.05        | (v1_tsep_1 @ sk_B_1 @ sk_A))),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('135', plain,
% 0.86/1.05      (((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_A @ 
% 0.86/1.05         (k8_tmap_1 @ sk_A @ sk_B_1)))
% 0.86/1.05         <= (((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_A @ 
% 0.86/1.05               (k8_tmap_1 @ sk_A @ sk_B_1))))),
% 0.86/1.05      inference('split', [status(esa)], ['134'])).
% 0.86/1.05  thf('136', plain,
% 0.86/1.05      ((((v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 0.86/1.05          (k8_tmap_1 @ sk_A @ sk_B_1))
% 0.86/1.05         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.86/1.05         <= (((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_A @ 
% 0.86/1.05               (k8_tmap_1 @ sk_A @ sk_B_1))) & 
% 0.86/1.05             ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.86/1.05               (k1_zfmisc_1 @ 
% 0.86/1.05                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.05                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))))),
% 0.86/1.05      inference('sup+', [status(thm)], ['133', '135'])).
% 0.86/1.05  thf('137', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('138', plain,
% 0.86/1.05      (![X26 : $i, X27 : $i]:
% 0.86/1.05         (~ (l1_pre_topc @ X26)
% 0.86/1.05          | ~ (v2_pre_topc @ X26)
% 0.86/1.05          | (v2_struct_0 @ X26)
% 0.86/1.05          | ~ (m1_pre_topc @ X27 @ X26)
% 0.86/1.05          | (m1_subset_1 @ (k9_tmap_1 @ X26 @ X27) @ 
% 0.86/1.05             (k1_zfmisc_1 @ 
% 0.86/1.05              (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ 
% 0.86/1.05               (u1_struct_0 @ (k8_tmap_1 @ X26 @ X27))))))),
% 0.86/1.05      inference('cnf', [status(esa)], [dt_k9_tmap_1])).
% 0.86/1.05  thf('139', plain,
% 0.86/1.05      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.86/1.05         (k1_zfmisc_1 @ 
% 0.86/1.05          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.05           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))
% 0.86/1.05        | (v2_struct_0 @ sk_A)
% 0.86/1.05        | ~ (v2_pre_topc @ sk_A)
% 0.86/1.05        | ~ (l1_pre_topc @ sk_A))),
% 0.86/1.05      inference('sup-', [status(thm)], ['137', '138'])).
% 0.86/1.05  thf('140', plain,
% 0.86/1.05      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A))),
% 0.86/1.05      inference('demod', [status(thm)], ['57', '58'])).
% 0.86/1.05  thf('141', plain, ((v2_pre_topc @ sk_A)),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('142', plain, ((l1_pre_topc @ sk_A)),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('143', plain,
% 0.86/1.05      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.86/1.05         (k1_zfmisc_1 @ 
% 0.86/1.05          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.86/1.05        | (v2_struct_0 @ sk_A))),
% 0.86/1.05      inference('demod', [status(thm)], ['139', '140', '141', '142'])).
% 0.86/1.05  thf('144', plain, (~ (v2_struct_0 @ sk_A)),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('145', plain,
% 0.86/1.05      ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.86/1.05        (k1_zfmisc_1 @ 
% 0.86/1.05         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 0.86/1.05      inference('clc', [status(thm)], ['143', '144'])).
% 0.86/1.05  thf('146', plain,
% 0.86/1.05      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A))),
% 0.86/1.05      inference('demod', [status(thm)], ['57', '58'])).
% 0.86/1.05  thf('147', plain,
% 0.86/1.05      ((~ (m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.86/1.05           (k1_zfmisc_1 @ 
% 0.86/1.05            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.05             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))
% 0.86/1.05        | ~ (v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_A @ 
% 0.86/1.05             (k8_tmap_1 @ sk_A @ sk_B_1))
% 0.86/1.05        | ~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.05             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))
% 0.86/1.05        | ~ (v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B_1))
% 0.86/1.05        | ~ (m1_pre_topc @ sk_B_1 @ sk_A)
% 0.86/1.05        | ~ (v1_tsep_1 @ sk_B_1 @ sk_A))),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('148', plain,
% 0.86/1.05      ((~ (m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.86/1.05           (k1_zfmisc_1 @ 
% 0.86/1.05            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.05             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1))))))
% 0.86/1.05         <= (~
% 0.86/1.05             ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.86/1.05               (k1_zfmisc_1 @ 
% 0.86/1.05                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.05                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))))),
% 0.86/1.05      inference('split', [status(esa)], ['147'])).
% 0.86/1.05  thf('149', plain,
% 0.86/1.05      ((~ (m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.86/1.05           (k1_zfmisc_1 @ 
% 0.86/1.05            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))
% 0.86/1.05         <= (~
% 0.86/1.05             ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.86/1.05               (k1_zfmisc_1 @ 
% 0.86/1.05                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.05                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))))),
% 0.86/1.05      inference('sup-', [status(thm)], ['146', '148'])).
% 0.86/1.05  thf('150', plain,
% 0.86/1.05      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.86/1.05         (k1_zfmisc_1 @ 
% 0.86/1.05          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.05           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1))))))),
% 0.86/1.05      inference('sup-', [status(thm)], ['145', '149'])).
% 0.86/1.05  thf('151', plain,
% 0.86/1.05      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.86/1.05         (k1_zfmisc_1 @ 
% 0.86/1.05          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.05           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1))))))),
% 0.86/1.05      inference('sat_resolution*', [status(thm)], ['150'])).
% 0.86/1.05  thf('152', plain,
% 0.86/1.05      ((((v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 0.86/1.05          (k8_tmap_1 @ sk_A @ sk_B_1))
% 0.86/1.05         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.86/1.05         <= (((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_A @ 
% 0.86/1.05               (k8_tmap_1 @ sk_A @ sk_B_1))))),
% 0.86/1.05      inference('simpl_trail', [status(thm)], ['136', '151'])).
% 0.86/1.05  thf('153', plain,
% 0.86/1.05      (~ ((v1_tsep_1 @ sk_B_1 @ sk_A)) | 
% 0.86/1.05       ~
% 0.86/1.05       ((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_A @ 
% 0.86/1.05         (k8_tmap_1 @ sk_A @ sk_B_1))) | 
% 0.86/1.05       ~ ((m1_pre_topc @ sk_B_1 @ sk_A)) | 
% 0.86/1.05       ~ ((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B_1))) | 
% 0.86/1.05       ~
% 0.86/1.05       ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.05         (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))) | 
% 0.86/1.05       ~
% 0.86/1.05       ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.86/1.05         (k1_zfmisc_1 @ 
% 0.86/1.05          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.05           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1))))))),
% 0.86/1.05      inference('split', [status(esa)], ['147'])).
% 0.86/1.05  thf('154', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('155', plain,
% 0.86/1.05      ((~ (m1_pre_topc @ sk_B_1 @ sk_A)) <= (~ ((m1_pre_topc @ sk_B_1 @ sk_A)))),
% 0.86/1.05      inference('split', [status(esa)], ['147'])).
% 0.86/1.05  thf('156', plain, (((m1_pre_topc @ sk_B_1 @ sk_A))),
% 0.86/1.05      inference('sup-', [status(thm)], ['154', '155'])).
% 0.86/1.05  thf('157', plain, ((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B_1))),
% 0.86/1.05      inference('clc', [status(thm)], ['103', '104'])).
% 0.86/1.05  thf('158', plain,
% 0.86/1.05      ((~ (v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B_1)))
% 0.86/1.05         <= (~ ((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B_1))))),
% 0.86/1.05      inference('split', [status(esa)], ['147'])).
% 0.86/1.05  thf('159', plain, (((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B_1)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['157', '158'])).
% 0.86/1.05  thf('160', plain,
% 0.86/1.05      ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.05        (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))),
% 0.86/1.05      inference('clc', [status(thm)], ['93', '94'])).
% 0.86/1.05  thf('161', plain,
% 0.86/1.05      ((~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.05           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1))))
% 0.86/1.05         <= (~
% 0.86/1.05             ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.86/1.05               (u1_struct_0 @ sk_A) @ 
% 0.86/1.05               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))),
% 0.86/1.05      inference('split', [status(esa)], ['147'])).
% 0.86/1.05  thf('162', plain,
% 0.86/1.05      (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.05         (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1))))),
% 0.86/1.05      inference('sup-', [status(thm)], ['160', '161'])).
% 0.86/1.05  thf('163', plain,
% 0.86/1.05      (((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B_1))
% 0.86/1.05        | (v1_tsep_1 @ sk_B_1 @ sk_A))),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('164', plain,
% 0.86/1.05      (((v1_tsep_1 @ sk_B_1 @ sk_A)) <= (((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 0.86/1.05      inference('split', [status(esa)], ['163'])).
% 0.86/1.05  thf('165', plain,
% 0.86/1.05      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.86/1.05        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.86/1.05      inference('demod', [status(thm)], ['3', '4'])).
% 0.86/1.05  thf(d1_tsep_1, axiom,
% 0.86/1.05    (![A:$i]:
% 0.86/1.05     ( ( l1_pre_topc @ A ) =>
% 0.86/1.05       ( ![B:$i]:
% 0.86/1.05         ( ( m1_pre_topc @ B @ A ) =>
% 0.86/1.05           ( ( v1_tsep_1 @ B @ A ) <=>
% 0.86/1.05             ( ![C:$i]:
% 0.86/1.05               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.86/1.05                 ( ( ( C ) = ( u1_struct_0 @ B ) ) => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.86/1.05  thf('166', plain,
% 0.86/1.05      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.86/1.05         (~ (m1_pre_topc @ X19 @ X20)
% 0.86/1.05          | ~ (v1_tsep_1 @ X19 @ X20)
% 0.86/1.05          | ((X21) != (u1_struct_0 @ X19))
% 0.86/1.05          | (v3_pre_topc @ X21 @ X20)
% 0.86/1.05          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.86/1.05          | ~ (l1_pre_topc @ X20))),
% 0.86/1.05      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.86/1.05  thf('167', plain,
% 0.86/1.05      (![X19 : $i, X20 : $i]:
% 0.86/1.05         (~ (l1_pre_topc @ X20)
% 0.86/1.05          | ~ (m1_subset_1 @ (u1_struct_0 @ X19) @ 
% 0.86/1.05               (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.86/1.05          | (v3_pre_topc @ (u1_struct_0 @ X19) @ X20)
% 0.86/1.05          | ~ (v1_tsep_1 @ X19 @ X20)
% 0.86/1.05          | ~ (m1_pre_topc @ X19 @ X20))),
% 0.86/1.05      inference('simplify', [status(thm)], ['166'])).
% 0.86/1.05  thf('168', plain,
% 0.86/1.05      ((~ (m1_pre_topc @ sk_B_1 @ sk_A)
% 0.86/1.05        | ~ (v1_tsep_1 @ sk_B_1 @ sk_A)
% 0.86/1.05        | (v3_pre_topc @ (u1_struct_0 @ sk_B_1) @ sk_A)
% 0.86/1.05        | ~ (l1_pre_topc @ sk_A))),
% 0.86/1.05      inference('sup-', [status(thm)], ['165', '167'])).
% 0.86/1.05  thf('169', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('170', plain, ((l1_pre_topc @ sk_A)),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('171', plain,
% 0.86/1.05      ((~ (v1_tsep_1 @ sk_B_1 @ sk_A)
% 0.86/1.05        | (v3_pre_topc @ (u1_struct_0 @ sk_B_1) @ sk_A))),
% 0.86/1.05      inference('demod', [status(thm)], ['168', '169', '170'])).
% 0.86/1.05  thf('172', plain,
% 0.86/1.05      (((v3_pre_topc @ (u1_struct_0 @ sk_B_1) @ sk_A))
% 0.86/1.05         <= (((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['164', '171'])).
% 0.86/1.05  thf('173', plain,
% 0.86/1.05      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.86/1.05        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.86/1.05      inference('demod', [status(thm)], ['3', '4'])).
% 0.86/1.05  thf(t113_tmap_1, axiom,
% 0.86/1.05    (![A:$i]:
% 0.86/1.05     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.86/1.05       ( ![B:$i]:
% 0.86/1.05         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.86/1.05           ( ( v3_pre_topc @ B @ A ) <=>
% 0.86/1.05             ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) ) & 
% 0.86/1.05               ( v1_funct_2 @
% 0.86/1.05                 ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.86/1.05                 ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 0.86/1.05               ( v5_pre_topc @
% 0.86/1.05                 ( k7_tmap_1 @ A @ B ) @ A @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.86/1.05               ( m1_subset_1 @
% 0.86/1.05                 ( k7_tmap_1 @ A @ B ) @ 
% 0.86/1.05                 ( k1_zfmisc_1 @
% 0.86/1.05                   ( k2_zfmisc_1 @
% 0.86/1.05                     ( u1_struct_0 @ A ) @ 
% 0.86/1.05                     ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) ))).
% 0.86/1.05  thf('174', plain,
% 0.86/1.05      (![X30 : $i, X31 : $i]:
% 0.86/1.05         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.86/1.05          | ~ (v3_pre_topc @ X30 @ X31)
% 0.86/1.05          | (v5_pre_topc @ (k7_tmap_1 @ X31 @ X30) @ X31 @ 
% 0.86/1.05             (k6_tmap_1 @ X31 @ X30))
% 0.86/1.05          | ~ (l1_pre_topc @ X31)
% 0.86/1.05          | ~ (v2_pre_topc @ X31)
% 0.86/1.05          | (v2_struct_0 @ X31))),
% 0.86/1.05      inference('cnf', [status(esa)], [t113_tmap_1])).
% 0.86/1.05  thf('175', plain,
% 0.86/1.05      (((v2_struct_0 @ sk_A)
% 0.86/1.05        | ~ (v2_pre_topc @ sk_A)
% 0.86/1.05        | ~ (l1_pre_topc @ sk_A)
% 0.86/1.05        | (v5_pre_topc @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)) @ sk_A @ 
% 0.86/1.05           (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 0.86/1.05        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B_1) @ sk_A))),
% 0.86/1.05      inference('sup-', [status(thm)], ['173', '174'])).
% 0.86/1.05  thf('176', plain, ((v2_pre_topc @ sk_A)),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('177', plain, ((l1_pre_topc @ sk_A)),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('178', plain,
% 0.86/1.05      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))
% 0.86/1.05         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.86/1.05      inference('clc', [status(thm)], ['13', '14'])).
% 0.86/1.05  thf('179', plain,
% 0.86/1.05      (((k8_tmap_1 @ sk_A @ sk_B_1)
% 0.86/1.05         = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))),
% 0.86/1.05      inference('clc', [status(thm)], ['47', '48'])).
% 0.86/1.05  thf('180', plain,
% 0.86/1.05      (((v2_struct_0 @ sk_A)
% 0.86/1.05        | (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 0.86/1.05           (k8_tmap_1 @ sk_A @ sk_B_1))
% 0.86/1.05        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B_1) @ sk_A))),
% 0.86/1.05      inference('demod', [status(thm)], ['175', '176', '177', '178', '179'])).
% 0.86/1.05  thf('181', plain, (~ (v2_struct_0 @ sk_A)),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('182', plain,
% 0.86/1.05      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_B_1) @ sk_A)
% 0.86/1.05        | (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 0.86/1.05           (k8_tmap_1 @ sk_A @ sk_B_1)))),
% 0.86/1.05      inference('clc', [status(thm)], ['180', '181'])).
% 0.86/1.05  thf('183', plain,
% 0.86/1.05      (((v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 0.86/1.05         (k8_tmap_1 @ sk_A @ sk_B_1))) <= (((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['172', '182'])).
% 0.86/1.05  thf('184', plain,
% 0.86/1.05      (((((k9_tmap_1 @ sk_A @ sk_B_1) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 0.86/1.05         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.86/1.05         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.86/1.05               (k1_zfmisc_1 @ 
% 0.86/1.05                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.05                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))))),
% 0.86/1.05      inference('sup-', [status(thm)], ['64', '132'])).
% 0.86/1.05  thf('185', plain,
% 0.86/1.05      ((~ (v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_A @ 
% 0.86/1.05           (k8_tmap_1 @ sk_A @ sk_B_1)))
% 0.86/1.05         <= (~
% 0.86/1.05             ((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_A @ 
% 0.86/1.05               (k8_tmap_1 @ sk_A @ sk_B_1))))),
% 0.86/1.05      inference('split', [status(esa)], ['147'])).
% 0.86/1.05  thf('186', plain,
% 0.86/1.05      (((~ (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 0.86/1.05            (k8_tmap_1 @ sk_A @ sk_B_1))
% 0.86/1.05         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.86/1.05         <= (~
% 0.86/1.05             ((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_A @ 
% 0.86/1.05               (k8_tmap_1 @ sk_A @ sk_B_1))) & 
% 0.86/1.05             ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.86/1.05               (k1_zfmisc_1 @ 
% 0.86/1.05                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.05                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)))))))),
% 0.86/1.05      inference('sup-', [status(thm)], ['184', '185'])).
% 0.86/1.05  thf('187', plain,
% 0.86/1.05      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B_1) @ 
% 0.86/1.05         (k1_zfmisc_1 @ 
% 0.86/1.05          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.05           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1))))))),
% 0.86/1.05      inference('sat_resolution*', [status(thm)], ['150'])).
% 0.86/1.05  thf('188', plain,
% 0.86/1.05      (((~ (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 0.86/1.05            (k8_tmap_1 @ sk_A @ sk_B_1))
% 0.86/1.05         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.86/1.05         <= (~
% 0.86/1.05             ((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_A @ 
% 0.86/1.05               (k8_tmap_1 @ sk_A @ sk_B_1))))),
% 0.86/1.05      inference('simpl_trail', [status(thm)], ['186', '187'])).
% 0.86/1.05  thf('189', plain,
% 0.86/1.05      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.86/1.05         <= (~
% 0.86/1.05             ((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_A @ 
% 0.86/1.05               (k8_tmap_1 @ sk_A @ sk_B_1))) & 
% 0.86/1.05             ((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['183', '188'])).
% 0.86/1.05  thf(fc2_struct_0, axiom,
% 0.86/1.05    (![A:$i]:
% 0.86/1.05     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.86/1.05       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.86/1.05  thf('190', plain,
% 0.86/1.05      (![X1 : $i]:
% 0.86/1.05         (~ (v1_xboole_0 @ (u1_struct_0 @ X1))
% 0.86/1.05          | ~ (l1_struct_0 @ X1)
% 0.86/1.05          | (v2_struct_0 @ X1))),
% 0.86/1.05      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.86/1.05  thf('191', plain,
% 0.86/1.05      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.86/1.05         <= (~
% 0.86/1.05             ((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_A @ 
% 0.86/1.05               (k8_tmap_1 @ sk_A @ sk_B_1))) & 
% 0.86/1.05             ((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['189', '190'])).
% 0.86/1.05  thf('192', plain, ((l1_pre_topc @ sk_A)),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf(dt_l1_pre_topc, axiom,
% 0.86/1.05    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.86/1.05  thf('193', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.86/1.05      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.86/1.05  thf('194', plain, ((l1_struct_0 @ sk_A)),
% 0.86/1.05      inference('sup-', [status(thm)], ['192', '193'])).
% 0.86/1.05  thf('195', plain,
% 0.86/1.05      (((v2_struct_0 @ sk_A))
% 0.86/1.05         <= (~
% 0.86/1.05             ((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_A @ 
% 0.86/1.05               (k8_tmap_1 @ sk_A @ sk_B_1))) & 
% 0.86/1.05             ((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 0.86/1.05      inference('demod', [status(thm)], ['191', '194'])).
% 0.86/1.05  thf('196', plain, (~ (v2_struct_0 @ sk_A)),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('197', plain,
% 0.86/1.05      (((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_A @ 
% 0.86/1.05         (k8_tmap_1 @ sk_A @ sk_B_1))) | 
% 0.86/1.05       ~ ((v1_tsep_1 @ sk_B_1 @ sk_A))),
% 0.86/1.05      inference('sup-', [status(thm)], ['195', '196'])).
% 0.86/1.05  thf('198', plain,
% 0.86/1.05      (((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_A @ 
% 0.86/1.05         (k8_tmap_1 @ sk_A @ sk_B_1))) | 
% 0.86/1.05       ((v1_tsep_1 @ sk_B_1 @ sk_A))),
% 0.86/1.05      inference('split', [status(esa)], ['134'])).
% 0.86/1.05  thf('199', plain,
% 0.86/1.05      (((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B_1) @ sk_A @ 
% 0.86/1.05         (k8_tmap_1 @ sk_A @ sk_B_1)))),
% 0.86/1.05      inference('sat_resolution*', [status(thm)],
% 0.86/1.05                ['153', '156', '159', '162', '150', '197', '198'])).
% 0.86/1.05  thf('200', plain,
% 0.86/1.05      (((v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 0.86/1.05         (k8_tmap_1 @ sk_A @ sk_B_1))
% 0.86/1.05        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.86/1.05      inference('simpl_trail', [status(thm)], ['152', '199'])).
% 0.86/1.05  thf('201', plain,
% 0.86/1.05      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))
% 0.86/1.05         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.86/1.05      inference('clc', [status(thm)], ['13', '14'])).
% 0.86/1.05  thf('202', plain,
% 0.86/1.05      (![X30 : $i, X31 : $i]:
% 0.86/1.05         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.86/1.05          | ~ (v1_funct_1 @ (k7_tmap_1 @ X31 @ X30))
% 0.86/1.05          | ~ (v1_funct_2 @ (k7_tmap_1 @ X31 @ X30) @ (u1_struct_0 @ X31) @ 
% 0.86/1.05               (u1_struct_0 @ (k6_tmap_1 @ X31 @ X30)))
% 0.86/1.05          | ~ (v5_pre_topc @ (k7_tmap_1 @ X31 @ X30) @ X31 @ 
% 0.86/1.05               (k6_tmap_1 @ X31 @ X30))
% 0.86/1.05          | ~ (m1_subset_1 @ (k7_tmap_1 @ X31 @ X30) @ 
% 0.86/1.05               (k1_zfmisc_1 @ 
% 0.86/1.05                (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ 
% 0.86/1.05                 (u1_struct_0 @ (k6_tmap_1 @ X31 @ X30)))))
% 0.86/1.05          | (v3_pre_topc @ X30 @ X31)
% 0.86/1.05          | ~ (l1_pre_topc @ X31)
% 0.86/1.05          | ~ (v2_pre_topc @ X31)
% 0.86/1.05          | (v2_struct_0 @ X31))),
% 0.86/1.05      inference('cnf', [status(esa)], [t113_tmap_1])).
% 0.86/1.05  thf('203', plain,
% 0.86/1.05      ((~ (m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.86/1.05           (k1_zfmisc_1 @ 
% 0.86/1.05            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.86/1.05             (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))))))
% 0.86/1.05        | (v2_struct_0 @ sk_A)
% 0.86/1.05        | ~ (v2_pre_topc @ sk_A)
% 0.86/1.05        | ~ (l1_pre_topc @ sk_A)
% 0.86/1.05        | (v3_pre_topc @ (u1_struct_0 @ sk_B_1) @ sk_A)
% 0.86/1.05        | ~ (v5_pre_topc @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)) @ 
% 0.86/1.05             sk_A @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 0.86/1.05        | ~ (v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)) @ 
% 0.86/1.05             (u1_struct_0 @ sk_A) @ 
% 0.86/1.05             (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))))
% 0.86/1.05        | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))
% 0.86/1.05        | ~ (m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.86/1.05             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.86/1.05      inference('sup-', [status(thm)], ['201', '202'])).
% 0.86/1.05  thf('204', plain,
% 0.86/1.05      (((k8_tmap_1 @ sk_A @ sk_B_1)
% 0.86/1.05         = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))),
% 0.86/1.05      inference('clc', [status(thm)], ['47', '48'])).
% 0.86/1.05  thf('205', plain,
% 0.86/1.05      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A))),
% 0.86/1.05      inference('demod', [status(thm)], ['57', '58'])).
% 0.86/1.05  thf('206', plain,
% 0.86/1.05      ((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.86/1.05        (k1_zfmisc_1 @ 
% 0.86/1.05         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 0.86/1.05      inference('clc', [status(thm)], ['73', '74'])).
% 0.86/1.05  thf('207', plain, ((v2_pre_topc @ sk_A)),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('208', plain, ((l1_pre_topc @ sk_A)),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('209', plain,
% 0.86/1.05      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))
% 0.86/1.05         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.86/1.05      inference('clc', [status(thm)], ['13', '14'])).
% 0.86/1.05  thf('210', plain,
% 0.86/1.05      (((k8_tmap_1 @ sk_A @ sk_B_1)
% 0.86/1.05         = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))),
% 0.86/1.05      inference('clc', [status(thm)], ['47', '48'])).
% 0.86/1.05  thf('211', plain,
% 0.86/1.05      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))
% 0.86/1.05         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.86/1.05      inference('clc', [status(thm)], ['13', '14'])).
% 0.86/1.05  thf('212', plain,
% 0.86/1.05      (((k8_tmap_1 @ sk_A @ sk_B_1)
% 0.86/1.05         = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1)))),
% 0.86/1.05      inference('clc', [status(thm)], ['47', '48'])).
% 0.86/1.05  thf('213', plain,
% 0.86/1.05      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A))),
% 0.86/1.05      inference('demod', [status(thm)], ['57', '58'])).
% 0.86/1.05  thf('214', plain,
% 0.86/1.05      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.86/1.05        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.86/1.05      inference('clc', [status(thm)], ['62', '63'])).
% 0.86/1.05  thf('215', plain,
% 0.86/1.05      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B_1))
% 0.86/1.05         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.86/1.05      inference('clc', [status(thm)], ['13', '14'])).
% 0.86/1.05  thf('216', plain, ((v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.86/1.05      inference('demod', [status(thm)], ['127', '128'])).
% 0.86/1.05  thf('217', plain,
% 0.86/1.05      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.86/1.05        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.86/1.05      inference('demod', [status(thm)], ['3', '4'])).
% 0.86/1.05  thf('218', plain,
% 0.86/1.05      (((v2_struct_0 @ sk_A)
% 0.86/1.05        | (v3_pre_topc @ (u1_struct_0 @ sk_B_1) @ sk_A)
% 0.86/1.05        | ~ (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 0.86/1.05             (k8_tmap_1 @ sk_A @ sk_B_1)))),
% 0.86/1.05      inference('demod', [status(thm)],
% 0.86/1.05                ['203', '204', '205', '206', '207', '208', '209', '210', 
% 0.86/1.05                 '211', '212', '213', '214', '215', '216', '217'])).
% 0.86/1.05  thf('219', plain, (~ (v2_struct_0 @ sk_A)),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('220', plain,
% 0.86/1.05      ((~ (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 0.86/1.05           (k8_tmap_1 @ sk_A @ sk_B_1))
% 0.86/1.05        | (v3_pre_topc @ (u1_struct_0 @ sk_B_1) @ sk_A))),
% 0.86/1.05      inference('clc', [status(thm)], ['218', '219'])).
% 0.86/1.05  thf('221', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('222', plain,
% 0.86/1.05      (![X19 : $i, X20 : $i]:
% 0.86/1.05         (~ (m1_pre_topc @ X19 @ X20)
% 0.86/1.05          | ((sk_C @ X19 @ X20) = (u1_struct_0 @ X19))
% 0.86/1.05          | (v1_tsep_1 @ X19 @ X20)
% 0.86/1.05          | ~ (l1_pre_topc @ X20))),
% 0.86/1.05      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.86/1.05  thf('223', plain,
% 0.86/1.05      ((~ (l1_pre_topc @ sk_A)
% 0.86/1.05        | (v1_tsep_1 @ sk_B_1 @ sk_A)
% 0.86/1.05        | ((sk_C @ sk_B_1 @ sk_A) = (u1_struct_0 @ sk_B_1)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['221', '222'])).
% 0.86/1.05  thf('224', plain, ((l1_pre_topc @ sk_A)),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('225', plain,
% 0.86/1.05      (((v1_tsep_1 @ sk_B_1 @ sk_A)
% 0.86/1.05        | ((sk_C @ sk_B_1 @ sk_A) = (u1_struct_0 @ sk_B_1)))),
% 0.86/1.05      inference('demod', [status(thm)], ['223', '224'])).
% 0.86/1.05  thf('226', plain,
% 0.86/1.05      ((~ (v1_tsep_1 @ sk_B_1 @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 0.86/1.05      inference('split', [status(esa)], ['147'])).
% 0.86/1.05  thf('227', plain,
% 0.86/1.05      ((((sk_C @ sk_B_1 @ sk_A) = (u1_struct_0 @ sk_B_1)))
% 0.86/1.05         <= (~ ((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['225', '226'])).
% 0.86/1.05  thf('228', plain,
% 0.86/1.05      (![X19 : $i, X20 : $i]:
% 0.86/1.05         (~ (m1_pre_topc @ X19 @ X20)
% 0.86/1.05          | ~ (v3_pre_topc @ (sk_C @ X19 @ X20) @ X20)
% 0.86/1.05          | (v1_tsep_1 @ X19 @ X20)
% 0.86/1.05          | ~ (l1_pre_topc @ X20))),
% 0.86/1.05      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.86/1.05  thf('229', plain,
% 0.86/1.05      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_B_1) @ sk_A)
% 0.86/1.05         | ~ (l1_pre_topc @ sk_A)
% 0.86/1.05         | (v1_tsep_1 @ sk_B_1 @ sk_A)
% 0.86/1.05         | ~ (m1_pre_topc @ sk_B_1 @ sk_A)))
% 0.86/1.05         <= (~ ((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 0.86/1.05      inference('sup-', [status(thm)], ['227', '228'])).
% 0.86/1.05  thf('230', plain, ((l1_pre_topc @ sk_A)),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('231', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.86/1.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.05  thf('232', plain,
% 0.86/1.05      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_B_1) @ sk_A)
% 0.86/1.05         | (v1_tsep_1 @ sk_B_1 @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 0.86/1.05      inference('demod', [status(thm)], ['229', '230', '231'])).
% 0.86/1.05  thf('233', plain,
% 0.86/1.05      ((~ (v1_tsep_1 @ sk_B_1 @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 0.86/1.05      inference('split', [status(esa)], ['147'])).
% 0.86/1.05  thf('234', plain,
% 0.86/1.05      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_B_1) @ sk_A))
% 0.86/1.05         <= (~ ((v1_tsep_1 @ sk_B_1 @ sk_A)))),
% 0.86/1.05      inference('clc', [status(thm)], ['232', '233'])).
% 0.86/1.05  thf('235', plain, (~ ((v1_tsep_1 @ sk_B_1 @ sk_A))),
% 0.86/1.05      inference('sat_resolution*', [status(thm)],
% 0.86/1.05                ['153', '156', '159', '162', '150', '197'])).
% 0.86/1.05  thf('236', plain, (~ (v3_pre_topc @ (u1_struct_0 @ sk_B_1) @ sk_A)),
% 0.86/1.05      inference('simpl_trail', [status(thm)], ['234', '235'])).
% 0.86/1.05  thf('237', plain,
% 0.86/1.05      (~ (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 0.86/1.05          (k8_tmap_1 @ sk_A @ sk_B_1))),
% 0.86/1.05      inference('clc', [status(thm)], ['220', '236'])).
% 0.86/1.05  thf('238', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.86/1.05      inference('clc', [status(thm)], ['200', '237'])).
% 0.86/1.05  thf('239', plain,
% 0.86/1.05      (![X1 : $i]:
% 0.86/1.05         (~ (v1_xboole_0 @ (u1_struct_0 @ X1))
% 0.86/1.05          | ~ (l1_struct_0 @ X1)
% 0.86/1.05          | (v2_struct_0 @ X1))),
% 0.86/1.05      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.86/1.05  thf('240', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.86/1.05      inference('sup-', [status(thm)], ['238', '239'])).
% 0.86/1.05  thf('241', plain, ((l1_struct_0 @ sk_A)),
% 0.86/1.05      inference('sup-', [status(thm)], ['192', '193'])).
% 0.86/1.05  thf('242', plain, ((v2_struct_0 @ sk_A)),
% 0.86/1.05      inference('demod', [status(thm)], ['240', '241'])).
% 0.86/1.05  thf('243', plain, ($false), inference('demod', [status(thm)], ['0', '242'])).
% 0.86/1.05  
% 0.86/1.05  % SZS output end Refutation
% 0.86/1.05  
% 0.86/1.05  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
