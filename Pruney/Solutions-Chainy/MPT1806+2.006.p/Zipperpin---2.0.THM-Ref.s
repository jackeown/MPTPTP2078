%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.P48LdYcmnK

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:03 EST 2020

% Result     : Theorem 0.67s
% Output     : Refutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :  360 (9687 expanded)
%              Number of leaves         :   42 (2775 expanded)
%              Depth                    :   38
%              Number of atoms          : 4246 (251456 expanded)
%              Number of equality atoms :   98 (1576 expanded)
%              Maximal formula depth    :   23 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k9_tmap_1_type,type,(
    k9_tmap_1: $i > $i > $i )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k8_tmap_1_type,type,(
    k8_tmap_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(k7_tmap_1_type,type,(
    k7_tmap_1: $i > $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

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

thf('0',plain,
    ( ~ ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
   <= ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('4',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
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

thf('6',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ( v1_funct_1 @ ( k9_tmap_1 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_tmap_1])).

thf('7',plain,
    ( ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
   <= ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,(
    v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ( v1_funct_2 @ ( k9_tmap_1 @ X25 @ X26 ) @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_tmap_1])).

thf('17',plain,
    ( ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('19',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_pre_topc @ X31 @ X32 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X31 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('20',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

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

thf('23',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X28 @ X27 ) )
        = ( u1_struct_0 @ X28 ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

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

thf('31',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( X12
       != ( k8_tmap_1 @ X11 @ X10 ) )
      | ( X13
       != ( u1_struct_0 @ X10 ) )
      | ( X12
        = ( k6_tmap_1 @ X11 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ~ ( v1_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d11_tmap_1])).

thf('32',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v1_pre_topc @ ( k8_tmap_1 @ X11 @ X10 ) )
      | ~ ( v2_pre_topc @ ( k8_tmap_1 @ X11 @ X10 ) )
      | ~ ( l1_pre_topc @ ( k8_tmap_1 @ X11 @ X10 ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( ( k8_tmap_1 @ X11 @ X10 )
        = ( k6_tmap_1 @ X11 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( m1_pre_topc @ X10 @ X11 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
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

thf('36',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('37',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ( v2_pre_topc @ ( k8_tmap_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('45',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('53',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34','42','50','58','59','60'])).

thf('62',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['29','63'])).

thf('65',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','64','65','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['29','63'])).

thf('71',plain,
    ( ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
   <= ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('72',plain,
    ( ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ( m1_subset_1 @ ( k9_tmap_1 @ X25 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X25 @ X26 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_tmap_1])).

thf('76',plain,
    ( ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['29','63'])).

thf('78',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['76','77','78','79'])).

thf('81',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['29','63'])).

thf('84',plain,
    ( ~ ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
   <= ~ ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('85',plain,
    ( ~ ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ~ ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['82','85'])).

thf('87',plain,
    ( ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['87'])).

thf('89',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

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

thf('90',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ~ ( v1_tsep_1 @ X18 @ X19 )
      | ( X20
       != ( u1_struct_0 @ X18 ) )
      | ( v3_pre_topc @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('91',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X18 ) @ X19 )
      | ~ ( v1_tsep_1 @ X18 @ X19 )
      | ~ ( m1_pre_topc @ X18 @ X19 ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['89','91'])).

thf('93',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('96',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['88','95'])).

thf('97',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

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

thf('98',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( v3_pre_topc @ X29 @ X30 )
      | ( v5_pre_topc @ ( k7_tmap_1 @ X30 @ X29 ) @ X30 @ ( k6_tmap_1 @ X30 @ X29 ) )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t113_tmap_1])).

thf('99',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(d10_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k7_tmap_1 @ A @ B )
            = ( k6_partfun1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('103',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( ( k7_tmap_1 @ X9 @ X8 )
        = ( k6_partfun1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_tmap_1])).

thf('104',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('111',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['99','100','101','109','110'])).

thf('112',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['111','112'])).

thf('114',plain,
    ( ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['96','113'])).

thf('115',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['27','28'])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('116',plain,(
    ! [X33: $i] :
      ( ( m1_pre_topc @ X33 @ X33 )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('117',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_pre_topc @ X31 @ X32 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X31 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['115','119'])).

thf('121',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('122',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('124',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('125',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['122','123','124'])).

thf(dt_k7_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) )
        & ( v1_funct_2 @ ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) )
        & ( m1_subset_1 @ ( k7_tmap_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) )).

thf('126',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v1_funct_2 @ ( k7_tmap_1 @ X21 @ X22 ) @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('127',plain,
    ( ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['122','123','124'])).

thf('129',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( ( k7_tmap_1 @ X9 @ X8 )
        = ( k6_partfun1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_tmap_1])).

thf('130',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['130','131','132'])).

thf('134',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X33: $i] :
      ( ( m1_pre_topc @ X33 @ X33 )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('137',plain,(
    ! [X33: $i] :
      ( ( m1_pre_topc @ X33 @ X33 )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('138',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('139',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,(
    ! [X33: $i] :
      ( ( m1_pre_topc @ X33 @ X33 )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('142',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ( v2_pre_topc @ ( k8_tmap_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('143',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,(
    ! [X33: $i] :
      ( ( m1_pre_topc @ X33 @ X33 )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('146',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['122','123','124'])).

thf('150',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v1_pre_topc @ ( k8_tmap_1 @ X11 @ X10 ) )
      | ~ ( v2_pre_topc @ ( k8_tmap_1 @ X11 @ X10 ) )
      | ~ ( l1_pre_topc @ ( k8_tmap_1 @ X11 @ X10 ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( ( k8_tmap_1 @ X11 @ X10 )
        = ( k6_tmap_1 @ X11 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( m1_pre_topc @ X10 @ X11 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('151',plain,
    ( ~ ( m1_pre_topc @ sk_A @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,
    ( ~ ( m1_pre_topc @ sk_A @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['151','152','153'])).

thf('155',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    | ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_pre_topc @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['148','154'])).

thf('156',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    | ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_pre_topc @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['155','156','157'])).

thf('159',plain,
    ( ~ ( m1_pre_topc @ sk_A @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['158'])).

thf('160',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    | ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_pre_topc @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['144','159'])).

thf('161',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    | ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_pre_topc @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['160','161','162'])).

thf('164',plain,
    ( ~ ( m1_pre_topc @ sk_A @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['163'])).

thf('165',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_pre_topc @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['140','164'])).

thf('166',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_pre_topc @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['165','166','167'])).

thf('169',plain,
    ( ~ ( m1_pre_topc @ sk_A @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['168'])).

thf('170',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_pre_topc @ sk_A @ sk_A ) ),
    inference(clc,[status(thm)],['169','170'])).

thf('172',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['136','171'])).

thf('173',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_A )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['172','173'])).

thf('175',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['122','123','124'])).

thf('176',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X28 @ X27 ) )
        = ( u1_struct_0 @ X28 ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('177',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['177','178','179'])).

thf('181',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['180','181'])).

thf('183',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_A )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['172','173'])).

thf('184',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['182','183'])).

thf('185',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,
    ( ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['127','135','174','184','185','186'])).

thf('188',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['187','188'])).

thf('190',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['122','123','124'])).

thf('191',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( m1_subset_1 @ ( k7_tmap_1 @ X21 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X21 @ X22 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('192',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['133','134'])).

thf('194',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_A )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['172','173'])).

thf('195',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['182','183'])).

thf('196',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,
    ( ( m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['192','193','194','195','196','197'])).

thf('199',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['198','199'])).

thf('201',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['29','63'])).

thf('202',plain,
    ( ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,
    ( ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
   <= ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['202'])).

thf('204',plain,
    ( ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['201','203'])).

thf('205',plain,
    ( ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,
    ( ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(split,[status(esa)],['205'])).

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

thf('207',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( X16
       != ( k9_tmap_1 @ X15 @ X14 ) )
      | ( X17
       != ( u1_struct_0 @ X14 ) )
      | ( r1_funct_2 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X15 @ X14 ) ) @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X15 @ X17 ) ) @ X16 @ ( k7_tmap_1 @ X15 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X15 @ X14 ) ) ) ) )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X15 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d12_tmap_1])).

thf('208',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v1_funct_1 @ ( k9_tmap_1 @ X15 @ X14 ) )
      | ~ ( v1_funct_2 @ ( k9_tmap_1 @ X15 @ X14 ) @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X15 @ X14 ) ) )
      | ~ ( m1_subset_1 @ ( k9_tmap_1 @ X15 @ X14 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X15 @ X14 ) ) ) ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( r1_funct_2 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X15 @ X14 ) ) @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X15 @ ( u1_struct_0 @ X14 ) ) ) @ ( k9_tmap_1 @ X15 @ X14 ) @ ( k7_tmap_1 @ X15 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( m1_pre_topc @ X14 @ X15 ) ) ),
    inference(simplify,[status(thm)],['207'])).

thf('209',plain,
    ( ( ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['206','208'])).

thf('210',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['29','63'])).

thf('212',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('213',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['29','63'])).

thf('214',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('215',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('216',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['29','63'])).

thf('217',plain,(
    v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('218',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,
    ( ( ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['209','210','211','212','213','214','215','216','217','218','219'])).

thf('221',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,
    ( ( ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(clc,[status(thm)],['220','221'])).

thf('223',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
      & ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['204','222'])).

thf('224',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['29','63'])).

thf('225',plain,
    ( ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
   <= ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['202'])).

thf('226',plain,
    ( ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(split,[status(esa)],['205'])).

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

thf('227',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X3 @ X4 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X5 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_funct_2 @ X6 @ X7 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X5 ) ) )
      | ( X2 = X6 )
      | ~ ( r1_funct_2 @ X3 @ X4 @ X7 @ X5 @ X2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_funct_2])).

thf('228',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) @ X2 @ X1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 )
        | ( ( k9_tmap_1 @ sk_A @ sk_B )
          = X0 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
        | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
        | ~ ( v1_funct_1 @ X0 )
        | ( v1_xboole_0 @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
        | ( v1_xboole_0 @ X1 )
        | ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
        | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['226','227'])).

thf('229',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
        | ( v1_xboole_0 @ X0 )
        | ( v1_xboole_0 @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
        | ~ ( v1_funct_1 @ X1 )
        | ~ ( v1_funct_2 @ X1 @ X2 @ X0 )
        | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
        | ( ( k9_tmap_1 @ sk_A @ sk_B )
          = X1 )
        | ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) @ X2 @ X0 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X1 ) )
   <= ( ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
      & ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['225','228'])).

thf('230',plain,(
    v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('231',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v1_xboole_0 @ X0 )
        | ( v1_xboole_0 @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
        | ~ ( v1_funct_1 @ X1 )
        | ~ ( v1_funct_2 @ X1 @ X2 @ X0 )
        | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
        | ( ( k9_tmap_1 @ sk_A @ sk_B )
          = X1 )
        | ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) @ X2 @ X0 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X1 ) )
   <= ( ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
      & ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['229','230'])).

thf('232',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ X2 @ X1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 )
        | ( ( k9_tmap_1 @ sk_A @ sk_B )
          = X0 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
        | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
        | ~ ( v1_funct_1 @ X0 )
        | ( v1_xboole_0 @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
        | ( v1_xboole_0 @ X1 ) )
   <= ( ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
      & ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['224','231'])).

thf('233',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['29','63'])).

thf('234',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ X2 @ X1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 )
        | ( ( k9_tmap_1 @ sk_A @ sk_B )
          = X0 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
        | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
        | ~ ( v1_funct_1 @ X0 )
        | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
        | ( v1_xboole_0 @ X1 ) )
   <= ( ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
      & ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['232','233'])).

thf('235',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( ( k9_tmap_1 @ sk_A @ sk_B )
        = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
      & ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['223','234'])).

thf('236',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('237',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v1_funct_1 @ ( k7_tmap_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('238',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['236','237'])).

thf('239',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['238','239','240'])).

thf('242',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,(
    v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['241','242'])).

thf('244',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('245',plain,(
    v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['243','244'])).

thf('246',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( ( k9_tmap_1 @ sk_A @ sk_B )
        = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
      & ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['235','245'])).

thf('247',plain,
    ( ( ( ( k9_tmap_1 @ sk_A @ sk_B )
        = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
      & ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['246'])).

thf('248',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k9_tmap_1 @ sk_A @ sk_B )
        = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
      & ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['200','247'])).

thf('249',plain,
    ( ( ( ( k9_tmap_1 @ sk_A @ sk_B )
        = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
      & ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['189','248'])).

thf('250',plain,
    ( ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('251',plain,
    ( ( ~ ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      & ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
      & ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['249','250'])).

thf('252',plain,(
    m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['86'])).

thf('253',plain,
    ( ( ~ ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      & ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(simpl_trail,[status(thm)],['251','252'])).

thf('254',plain,(
    v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['73'])).

thf('255',plain,
    ( ( ~ ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['253','254'])).

thf('256',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      & ( v1_tsep_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['114','255'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('257',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('258',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      & ( v1_tsep_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['256','257'])).

thf('259',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('260',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('261',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['259','260'])).

thf('262',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      & ( v1_tsep_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['258','261'])).

thf('263',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,
    ( ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['262','263'])).

thf('265',plain,
    ( ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('266',plain,
    ( ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['265'])).

thf('267',plain,
    ( ( ( ( k9_tmap_1 @ sk_A @ sk_B )
        = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
      & ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['189','248'])).

thf('268',plain,
    ( ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['265'])).

thf('269',plain,
    ( ( ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
      & ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      & ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ) ),
    inference('sup+',[status(thm)],['267','268'])).

thf('270',plain,(
    m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['86'])).

thf('271',plain,
    ( ( ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
      & ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['269','270'])).

thf('272',plain,(
    v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['73'])).

thf('273',plain,
    ( ( ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['271','272'])).

thf('274',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('275',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( v1_funct_1 @ ( k7_tmap_1 @ X30 @ X29 ) )
      | ~ ( v1_funct_2 @ ( k7_tmap_1 @ X30 @ X29 ) @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X30 @ X29 ) ) )
      | ~ ( v5_pre_topc @ ( k7_tmap_1 @ X30 @ X29 ) @ X30 @ ( k6_tmap_1 @ X30 @ X29 ) )
      | ~ ( m1_subset_1 @ ( k7_tmap_1 @ X30 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X30 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X30 @ X29 ) ) ) ) )
      | ( v3_pre_topc @ X29 @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t113_tmap_1])).

thf('276',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ~ ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['274','275'])).

thf('277',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('278',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['29','63'])).

thf('279',plain,(
    m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['198','199'])).

thf('280',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('281',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('282',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('283',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('284',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('285',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('286',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['29','63'])).

thf('287',plain,(
    v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['187','188'])).

thf('288',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('289',plain,(
    v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['243','244'])).

thf('290',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('291',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ~ ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['276','277','278','279','280','281','282','283','284','285','286','287','288','289','290'])).

thf('292',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('293',plain,
    ( ~ ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['291','292'])).

thf('294',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) )
   <= ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['273','293'])).

thf('295',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('296',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( ( sk_C @ X18 @ X19 )
        = ( u1_struct_0 @ X18 ) )
      | ( v1_tsep_1 @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('297',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['295','296'])).

thf('298',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('299',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['297','298'])).

thf('300',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('301',plain,
    ( ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['299','300'])).

thf('302',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ~ ( v3_pre_topc @ ( sk_C @ X18 @ X19 ) @ X19 )
      | ( v1_tsep_1 @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('303',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['301','302'])).

thf('304',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('305',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('306',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['303','304','305'])).

thf('307',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('308',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['306','307'])).

thf('309',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
      & ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['294','308'])).

thf('310',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('311',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
      & ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['309','310'])).

thf('312',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['259','260'])).

thf('313',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
      & ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['311','312'])).

thf('314',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('315',plain,
    ( ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['313','314'])).

thf('316',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','4','14','73','86','264','266','315'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.P48LdYcmnK
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:23:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.67/0.88  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.67/0.88  % Solved by: fo/fo7.sh
% 0.67/0.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.67/0.88  % done 442 iterations in 0.416s
% 0.67/0.88  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.67/0.88  % SZS output start Refutation
% 0.67/0.88  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.67/0.88  thf(k9_tmap_1_type, type, k9_tmap_1: $i > $i > $i).
% 0.67/0.88  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 0.67/0.88  thf(sk_A_type, type, sk_A: $i).
% 0.67/0.88  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.67/0.88  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.67/0.88  thf(k8_tmap_1_type, type, k8_tmap_1: $i > $i > $i).
% 0.67/0.88  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.67/0.88  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.67/0.88  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.67/0.88  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.67/0.88  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.67/0.88  thf(sk_B_type, type, sk_B: $i).
% 0.67/0.88  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 0.67/0.88  thf(k7_tmap_1_type, type, k7_tmap_1: $i > $i > $i).
% 0.67/0.88  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.67/0.88  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.67/0.88  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.67/0.88  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.67/0.88  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.67/0.88  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.67/0.88  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.67/0.88  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.67/0.88  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.67/0.88  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.67/0.88  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.67/0.88  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.67/0.88  thf(t122_tmap_1, conjecture,
% 0.67/0.88    (![A:$i]:
% 0.67/0.88     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.67/0.88       ( ![B:$i]:
% 0.67/0.88         ( ( m1_pre_topc @ B @ A ) =>
% 0.67/0.88           ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.67/0.88             ( ( v1_funct_1 @ ( k9_tmap_1 @ A @ B ) ) & 
% 0.67/0.88               ( v1_funct_2 @
% 0.67/0.88                 ( k9_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.67/0.88                 ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 0.67/0.88               ( v5_pre_topc @
% 0.67/0.88                 ( k9_tmap_1 @ A @ B ) @ A @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.67/0.88               ( m1_subset_1 @
% 0.67/0.88                 ( k9_tmap_1 @ A @ B ) @ 
% 0.67/0.88                 ( k1_zfmisc_1 @
% 0.67/0.88                   ( k2_zfmisc_1 @
% 0.67/0.88                     ( u1_struct_0 @ A ) @ 
% 0.67/0.88                     ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) ))).
% 0.67/0.88  thf(zf_stmt_0, negated_conjecture,
% 0.67/0.88    (~( ![A:$i]:
% 0.67/0.88        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.67/0.88            ( l1_pre_topc @ A ) ) =>
% 0.67/0.88          ( ![B:$i]:
% 0.67/0.88            ( ( m1_pre_topc @ B @ A ) =>
% 0.67/0.88              ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.67/0.88                ( ( v1_funct_1 @ ( k9_tmap_1 @ A @ B ) ) & 
% 0.67/0.88                  ( v1_funct_2 @
% 0.67/0.88                    ( k9_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.67/0.88                    ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 0.67/0.88                  ( v5_pre_topc @
% 0.67/0.88                    ( k9_tmap_1 @ A @ B ) @ A @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.67/0.88                  ( m1_subset_1 @
% 0.67/0.88                    ( k9_tmap_1 @ A @ B ) @ 
% 0.67/0.88                    ( k1_zfmisc_1 @
% 0.67/0.88                      ( k2_zfmisc_1 @
% 0.67/0.88                        ( u1_struct_0 @ A ) @ 
% 0.67/0.88                        ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) ) )),
% 0.67/0.88    inference('cnf.neg', [status(esa)], [t122_tmap_1])).
% 0.67/0.88  thf('0', plain,
% 0.67/0.88      ((~ (m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.67/0.88           (k1_zfmisc_1 @ 
% 0.67/0.88            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))
% 0.67/0.88        | ~ (v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.67/0.88             (k8_tmap_1 @ sk_A @ sk_B))
% 0.67/0.88        | ~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.67/0.88        | ~ (v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))
% 0.67/0.88        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.67/0.88        | ~ (v1_tsep_1 @ sk_B @ sk_A))),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('1', plain,
% 0.67/0.88      (~
% 0.67/0.88       ((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.67/0.88         (k8_tmap_1 @ sk_A @ sk_B))) | 
% 0.67/0.88       ~ ((v1_tsep_1 @ sk_B @ sk_A)) | ~ ((m1_pre_topc @ sk_B @ sk_A)) | 
% 0.67/0.88       ~ ((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))) | 
% 0.67/0.88       ~
% 0.67/0.88       ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88         (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))) | 
% 0.67/0.88       ~
% 0.67/0.88       ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.67/0.88         (k1_zfmisc_1 @ 
% 0.67/0.88          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))))),
% 0.67/0.88      inference('split', [status(esa)], ['0'])).
% 0.67/0.88  thf('2', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('3', plain,
% 0.67/0.88      ((~ (m1_pre_topc @ sk_B @ sk_A)) <= (~ ((m1_pre_topc @ sk_B @ sk_A)))),
% 0.67/0.88      inference('split', [status(esa)], ['0'])).
% 0.67/0.88  thf('4', plain, (((m1_pre_topc @ sk_B @ sk_A))),
% 0.67/0.88      inference('sup-', [status(thm)], ['2', '3'])).
% 0.67/0.88  thf('5', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf(dt_k9_tmap_1, axiom,
% 0.67/0.88    (![A:$i,B:$i]:
% 0.67/0.88     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.67/0.88         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.67/0.88       ( ( v1_funct_1 @ ( k9_tmap_1 @ A @ B ) ) & 
% 0.67/0.88         ( v1_funct_2 @
% 0.67/0.88           ( k9_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.67/0.88           ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 0.67/0.88         ( m1_subset_1 @
% 0.67/0.88           ( k9_tmap_1 @ A @ B ) @ 
% 0.67/0.88           ( k1_zfmisc_1 @
% 0.67/0.88             ( k2_zfmisc_1 @
% 0.67/0.88               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ))).
% 0.67/0.88  thf('6', plain,
% 0.67/0.88      (![X25 : $i, X26 : $i]:
% 0.67/0.88         (~ (l1_pre_topc @ X25)
% 0.67/0.88          | ~ (v2_pre_topc @ X25)
% 0.67/0.88          | (v2_struct_0 @ X25)
% 0.67/0.88          | ~ (m1_pre_topc @ X26 @ X25)
% 0.67/0.88          | (v1_funct_1 @ (k9_tmap_1 @ X25 @ X26)))),
% 0.67/0.88      inference('cnf', [status(esa)], [dt_k9_tmap_1])).
% 0.67/0.88  thf('7', plain,
% 0.67/0.88      (((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))
% 0.67/0.88        | (v2_struct_0 @ sk_A)
% 0.67/0.88        | ~ (v2_pre_topc @ sk_A)
% 0.67/0.88        | ~ (l1_pre_topc @ sk_A))),
% 0.67/0.88      inference('sup-', [status(thm)], ['5', '6'])).
% 0.67/0.88  thf('8', plain, ((v2_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('10', plain,
% 0.67/0.88      (((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.67/0.88      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.67/0.88  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('12', plain, ((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))),
% 0.67/0.88      inference('clc', [status(thm)], ['10', '11'])).
% 0.67/0.88  thf('13', plain,
% 0.67/0.88      ((~ (v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B)))
% 0.67/0.88         <= (~ ((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))))),
% 0.67/0.88      inference('split', [status(esa)], ['0'])).
% 0.67/0.88  thf('14', plain, (((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B)))),
% 0.67/0.88      inference('sup-', [status(thm)], ['12', '13'])).
% 0.67/0.88  thf('15', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('16', plain,
% 0.67/0.88      (![X25 : $i, X26 : $i]:
% 0.67/0.88         (~ (l1_pre_topc @ X25)
% 0.67/0.88          | ~ (v2_pre_topc @ X25)
% 0.67/0.88          | (v2_struct_0 @ X25)
% 0.67/0.88          | ~ (m1_pre_topc @ X26 @ X25)
% 0.67/0.88          | (v1_funct_2 @ (k9_tmap_1 @ X25 @ X26) @ (u1_struct_0 @ X25) @ 
% 0.67/0.88             (u1_struct_0 @ (k8_tmap_1 @ X25 @ X26))))),
% 0.67/0.88      inference('cnf', [status(esa)], [dt_k9_tmap_1])).
% 0.67/0.88  thf('17', plain,
% 0.67/0.88      (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88         (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.67/0.88        | (v2_struct_0 @ sk_A)
% 0.67/0.88        | ~ (v2_pre_topc @ sk_A)
% 0.67/0.88        | ~ (l1_pre_topc @ sk_A))),
% 0.67/0.88      inference('sup-', [status(thm)], ['15', '16'])).
% 0.67/0.88  thf('18', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf(t1_tsep_1, axiom,
% 0.67/0.88    (![A:$i]:
% 0.67/0.88     ( ( l1_pre_topc @ A ) =>
% 0.67/0.88       ( ![B:$i]:
% 0.67/0.88         ( ( m1_pre_topc @ B @ A ) =>
% 0.67/0.88           ( m1_subset_1 @
% 0.67/0.88             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.67/0.88  thf('19', plain,
% 0.67/0.88      (![X31 : $i, X32 : $i]:
% 0.67/0.88         (~ (m1_pre_topc @ X31 @ X32)
% 0.67/0.88          | (m1_subset_1 @ (u1_struct_0 @ X31) @ 
% 0.67/0.88             (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.67/0.88          | ~ (l1_pre_topc @ X32))),
% 0.67/0.88      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.67/0.88  thf('20', plain,
% 0.67/0.88      ((~ (l1_pre_topc @ sk_A)
% 0.67/0.88        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.67/0.88           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.67/0.88      inference('sup-', [status(thm)], ['18', '19'])).
% 0.67/0.88  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('22', plain,
% 0.67/0.88      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.67/0.88        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.88      inference('demod', [status(thm)], ['20', '21'])).
% 0.67/0.88  thf(t104_tmap_1, axiom,
% 0.67/0.88    (![A:$i]:
% 0.67/0.88     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.67/0.88       ( ![B:$i]:
% 0.67/0.88         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.67/0.88           ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.67/0.88             ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.67/0.88  thf('23', plain,
% 0.67/0.88      (![X27 : $i, X28 : $i]:
% 0.67/0.88         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.67/0.88          | ((u1_struct_0 @ (k6_tmap_1 @ X28 @ X27)) = (u1_struct_0 @ X28))
% 0.67/0.88          | ~ (l1_pre_topc @ X28)
% 0.67/0.88          | ~ (v2_pre_topc @ X28)
% 0.67/0.88          | (v2_struct_0 @ X28))),
% 0.67/0.88      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.67/0.88  thf('24', plain,
% 0.67/0.88      (((v2_struct_0 @ sk_A)
% 0.67/0.88        | ~ (v2_pre_topc @ sk_A)
% 0.67/0.88        | ~ (l1_pre_topc @ sk_A)
% 0.67/0.88        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.67/0.88            = (u1_struct_0 @ sk_A)))),
% 0.67/0.88      inference('sup-', [status(thm)], ['22', '23'])).
% 0.67/0.88  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('27', plain,
% 0.67/0.88      (((v2_struct_0 @ sk_A)
% 0.67/0.88        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.67/0.88            = (u1_struct_0 @ sk_A)))),
% 0.67/0.88      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.67/0.88  thf('28', plain, (~ (v2_struct_0 @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('29', plain,
% 0.67/0.88      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.67/0.88         = (u1_struct_0 @ sk_A))),
% 0.67/0.88      inference('clc', [status(thm)], ['27', '28'])).
% 0.67/0.88  thf('30', plain,
% 0.67/0.88      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.67/0.88        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.88      inference('demod', [status(thm)], ['20', '21'])).
% 0.67/0.88  thf(d11_tmap_1, axiom,
% 0.67/0.88    (![A:$i]:
% 0.67/0.88     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.67/0.88       ( ![B:$i]:
% 0.67/0.88         ( ( m1_pre_topc @ B @ A ) =>
% 0.67/0.88           ( ![C:$i]:
% 0.67/0.88             ( ( ( v1_pre_topc @ C ) & ( v2_pre_topc @ C ) & 
% 0.67/0.88                 ( l1_pre_topc @ C ) ) =>
% 0.67/0.88               ( ( ( C ) = ( k8_tmap_1 @ A @ B ) ) <=>
% 0.67/0.88                 ( ![D:$i]:
% 0.67/0.88                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.67/0.88                     ( ( ( D ) = ( u1_struct_0 @ B ) ) =>
% 0.67/0.88                       ( ( C ) = ( k6_tmap_1 @ A @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.67/0.88  thf('31', plain,
% 0.67/0.88      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.67/0.88         (~ (m1_pre_topc @ X10 @ X11)
% 0.67/0.88          | ((X12) != (k8_tmap_1 @ X11 @ X10))
% 0.67/0.88          | ((X13) != (u1_struct_0 @ X10))
% 0.67/0.88          | ((X12) = (k6_tmap_1 @ X11 @ X13))
% 0.67/0.88          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.67/0.88          | ~ (l1_pre_topc @ X12)
% 0.67/0.88          | ~ (v2_pre_topc @ X12)
% 0.67/0.88          | ~ (v1_pre_topc @ X12)
% 0.67/0.88          | ~ (l1_pre_topc @ X11)
% 0.67/0.88          | ~ (v2_pre_topc @ X11)
% 0.67/0.88          | (v2_struct_0 @ X11))),
% 0.67/0.88      inference('cnf', [status(esa)], [d11_tmap_1])).
% 0.67/0.88  thf('32', plain,
% 0.67/0.88      (![X10 : $i, X11 : $i]:
% 0.67/0.88         ((v2_struct_0 @ X11)
% 0.67/0.88          | ~ (v2_pre_topc @ X11)
% 0.67/0.88          | ~ (l1_pre_topc @ X11)
% 0.67/0.88          | ~ (v1_pre_topc @ (k8_tmap_1 @ X11 @ X10))
% 0.67/0.88          | ~ (v2_pre_topc @ (k8_tmap_1 @ X11 @ X10))
% 0.67/0.88          | ~ (l1_pre_topc @ (k8_tmap_1 @ X11 @ X10))
% 0.67/0.88          | ~ (m1_subset_1 @ (u1_struct_0 @ X10) @ 
% 0.67/0.88               (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.67/0.88          | ((k8_tmap_1 @ X11 @ X10) = (k6_tmap_1 @ X11 @ (u1_struct_0 @ X10)))
% 0.67/0.88          | ~ (m1_pre_topc @ X10 @ X11))),
% 0.67/0.88      inference('simplify', [status(thm)], ['31'])).
% 0.67/0.88  thf('33', plain,
% 0.67/0.88      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.67/0.88        | ((k8_tmap_1 @ sk_A @ sk_B)
% 0.67/0.88            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.67/0.88        | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.67/0.88        | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.67/0.88        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.67/0.88        | ~ (l1_pre_topc @ sk_A)
% 0.67/0.88        | ~ (v2_pre_topc @ sk_A)
% 0.67/0.88        | (v2_struct_0 @ sk_A))),
% 0.67/0.88      inference('sup-', [status(thm)], ['30', '32'])).
% 0.67/0.88  thf('34', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('35', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf(dt_k8_tmap_1, axiom,
% 0.67/0.88    (![A:$i,B:$i]:
% 0.67/0.88     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.67/0.88         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.67/0.88       ( ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.67/0.88         ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.67/0.88         ( l1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ))).
% 0.67/0.88  thf('36', plain,
% 0.67/0.88      (![X23 : $i, X24 : $i]:
% 0.67/0.88         (~ (l1_pre_topc @ X23)
% 0.67/0.88          | ~ (v2_pre_topc @ X23)
% 0.67/0.88          | (v2_struct_0 @ X23)
% 0.67/0.88          | ~ (m1_pre_topc @ X24 @ X23)
% 0.67/0.88          | (l1_pre_topc @ (k8_tmap_1 @ X23 @ X24)))),
% 0.67/0.88      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.67/0.88  thf('37', plain,
% 0.67/0.88      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.67/0.88        | (v2_struct_0 @ sk_A)
% 0.67/0.88        | ~ (v2_pre_topc @ sk_A)
% 0.67/0.88        | ~ (l1_pre_topc @ sk_A))),
% 0.67/0.88      inference('sup-', [status(thm)], ['35', '36'])).
% 0.67/0.88  thf('38', plain, ((v2_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('40', plain,
% 0.67/0.88      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.67/0.88      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.67/0.88  thf('41', plain, (~ (v2_struct_0 @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('42', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.67/0.88      inference('clc', [status(thm)], ['40', '41'])).
% 0.67/0.88  thf('43', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('44', plain,
% 0.67/0.88      (![X23 : $i, X24 : $i]:
% 0.67/0.88         (~ (l1_pre_topc @ X23)
% 0.67/0.88          | ~ (v2_pre_topc @ X23)
% 0.67/0.88          | (v2_struct_0 @ X23)
% 0.67/0.88          | ~ (m1_pre_topc @ X24 @ X23)
% 0.67/0.88          | (v2_pre_topc @ (k8_tmap_1 @ X23 @ X24)))),
% 0.67/0.88      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.67/0.88  thf('45', plain,
% 0.67/0.88      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.67/0.88        | (v2_struct_0 @ sk_A)
% 0.67/0.88        | ~ (v2_pre_topc @ sk_A)
% 0.67/0.88        | ~ (l1_pre_topc @ sk_A))),
% 0.67/0.88      inference('sup-', [status(thm)], ['43', '44'])).
% 0.67/0.88  thf('46', plain, ((v2_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('48', plain,
% 0.67/0.88      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.67/0.88      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.67/0.88  thf('49', plain, (~ (v2_struct_0 @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('50', plain, ((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.67/0.88      inference('clc', [status(thm)], ['48', '49'])).
% 0.67/0.88  thf('51', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('52', plain,
% 0.67/0.88      (![X23 : $i, X24 : $i]:
% 0.67/0.88         (~ (l1_pre_topc @ X23)
% 0.67/0.88          | ~ (v2_pre_topc @ X23)
% 0.67/0.88          | (v2_struct_0 @ X23)
% 0.67/0.88          | ~ (m1_pre_topc @ X24 @ X23)
% 0.67/0.88          | (v1_pre_topc @ (k8_tmap_1 @ X23 @ X24)))),
% 0.67/0.88      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.67/0.88  thf('53', plain,
% 0.67/0.88      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.67/0.88        | (v2_struct_0 @ sk_A)
% 0.67/0.88        | ~ (v2_pre_topc @ sk_A)
% 0.67/0.88        | ~ (l1_pre_topc @ sk_A))),
% 0.67/0.88      inference('sup-', [status(thm)], ['51', '52'])).
% 0.67/0.88  thf('54', plain, ((v2_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('56', plain,
% 0.67/0.88      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.67/0.88      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.67/0.88  thf('57', plain, (~ (v2_struct_0 @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('58', plain, ((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.67/0.88      inference('clc', [status(thm)], ['56', '57'])).
% 0.67/0.88  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('60', plain, ((v2_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('61', plain,
% 0.67/0.88      ((((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.67/0.88        | (v2_struct_0 @ sk_A))),
% 0.67/0.88      inference('demod', [status(thm)],
% 0.67/0.88                ['33', '34', '42', '50', '58', '59', '60'])).
% 0.67/0.88  thf('62', plain, (~ (v2_struct_0 @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('63', plain,
% 0.67/0.88      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.67/0.88      inference('clc', [status(thm)], ['61', '62'])).
% 0.67/0.88  thf('64', plain,
% 0.67/0.88      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.67/0.88      inference('demod', [status(thm)], ['29', '63'])).
% 0.67/0.88  thf('65', plain, ((v2_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('67', plain,
% 0.67/0.88      (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88         (u1_struct_0 @ sk_A))
% 0.67/0.88        | (v2_struct_0 @ sk_A))),
% 0.67/0.88      inference('demod', [status(thm)], ['17', '64', '65', '66'])).
% 0.67/0.88  thf('68', plain, (~ (v2_struct_0 @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('69', plain,
% 0.67/0.88      ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88        (u1_struct_0 @ sk_A))),
% 0.67/0.88      inference('clc', [status(thm)], ['67', '68'])).
% 0.67/0.88  thf('70', plain,
% 0.67/0.88      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.67/0.88      inference('demod', [status(thm)], ['29', '63'])).
% 0.67/0.88  thf('71', plain,
% 0.67/0.88      ((~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))
% 0.67/0.88         <= (~
% 0.67/0.88             ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))),
% 0.67/0.88      inference('split', [status(esa)], ['0'])).
% 0.67/0.88  thf('72', plain,
% 0.67/0.88      ((~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88           (u1_struct_0 @ sk_A)))
% 0.67/0.88         <= (~
% 0.67/0.88             ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))),
% 0.67/0.88      inference('sup-', [status(thm)], ['70', '71'])).
% 0.67/0.88  thf('73', plain,
% 0.67/0.88      (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88         (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.67/0.88      inference('sup-', [status(thm)], ['69', '72'])).
% 0.67/0.88  thf('74', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('75', plain,
% 0.67/0.88      (![X25 : $i, X26 : $i]:
% 0.67/0.88         (~ (l1_pre_topc @ X25)
% 0.67/0.88          | ~ (v2_pre_topc @ X25)
% 0.67/0.88          | (v2_struct_0 @ X25)
% 0.67/0.88          | ~ (m1_pre_topc @ X26 @ X25)
% 0.67/0.88          | (m1_subset_1 @ (k9_tmap_1 @ X25 @ X26) @ 
% 0.67/0.88             (k1_zfmisc_1 @ 
% 0.67/0.88              (k2_zfmisc_1 @ (u1_struct_0 @ X25) @ 
% 0.67/0.88               (u1_struct_0 @ (k8_tmap_1 @ X25 @ X26))))))),
% 0.67/0.88      inference('cnf', [status(esa)], [dt_k9_tmap_1])).
% 0.67/0.88  thf('76', plain,
% 0.67/0.88      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.67/0.88         (k1_zfmisc_1 @ 
% 0.67/0.88          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))
% 0.67/0.88        | (v2_struct_0 @ sk_A)
% 0.67/0.88        | ~ (v2_pre_topc @ sk_A)
% 0.67/0.88        | ~ (l1_pre_topc @ sk_A))),
% 0.67/0.88      inference('sup-', [status(thm)], ['74', '75'])).
% 0.67/0.88  thf('77', plain,
% 0.67/0.88      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.67/0.88      inference('demod', [status(thm)], ['29', '63'])).
% 0.67/0.88  thf('78', plain, ((v2_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('79', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('80', plain,
% 0.67/0.88      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.67/0.88         (k1_zfmisc_1 @ 
% 0.67/0.88          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.67/0.88        | (v2_struct_0 @ sk_A))),
% 0.67/0.88      inference('demod', [status(thm)], ['76', '77', '78', '79'])).
% 0.67/0.88  thf('81', plain, (~ (v2_struct_0 @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('82', plain,
% 0.67/0.88      ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.67/0.88        (k1_zfmisc_1 @ 
% 0.67/0.88         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 0.67/0.88      inference('clc', [status(thm)], ['80', '81'])).
% 0.67/0.88  thf('83', plain,
% 0.67/0.88      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.67/0.88      inference('demod', [status(thm)], ['29', '63'])).
% 0.67/0.88  thf('84', plain,
% 0.67/0.88      ((~ (m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.67/0.88           (k1_zfmisc_1 @ 
% 0.67/0.88            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))))
% 0.67/0.88         <= (~
% 0.67/0.88             ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.67/0.88               (k1_zfmisc_1 @ 
% 0.67/0.88                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.67/0.88      inference('split', [status(esa)], ['0'])).
% 0.67/0.88  thf('85', plain,
% 0.67/0.88      ((~ (m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.67/0.88           (k1_zfmisc_1 @ 
% 0.67/0.88            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))
% 0.67/0.88         <= (~
% 0.67/0.88             ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.67/0.88               (k1_zfmisc_1 @ 
% 0.67/0.88                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.67/0.88      inference('sup-', [status(thm)], ['83', '84'])).
% 0.67/0.88  thf('86', plain,
% 0.67/0.88      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.67/0.88         (k1_zfmisc_1 @ 
% 0.67/0.88          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))))),
% 0.67/0.88      inference('sup-', [status(thm)], ['82', '85'])).
% 0.67/0.88  thf('87', plain,
% 0.67/0.88      (((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B)) | (v1_tsep_1 @ sk_B @ sk_A))),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('88', plain,
% 0.67/0.88      (((v1_tsep_1 @ sk_B @ sk_A)) <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.67/0.88      inference('split', [status(esa)], ['87'])).
% 0.67/0.88  thf('89', plain,
% 0.67/0.88      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.67/0.88        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.88      inference('demod', [status(thm)], ['20', '21'])).
% 0.67/0.88  thf(d1_tsep_1, axiom,
% 0.67/0.88    (![A:$i]:
% 0.67/0.88     ( ( l1_pre_topc @ A ) =>
% 0.67/0.88       ( ![B:$i]:
% 0.67/0.88         ( ( m1_pre_topc @ B @ A ) =>
% 0.67/0.88           ( ( v1_tsep_1 @ B @ A ) <=>
% 0.67/0.88             ( ![C:$i]:
% 0.67/0.88               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.67/0.88                 ( ( ( C ) = ( u1_struct_0 @ B ) ) => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.67/0.88  thf('90', plain,
% 0.67/0.88      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.67/0.88         (~ (m1_pre_topc @ X18 @ X19)
% 0.67/0.88          | ~ (v1_tsep_1 @ X18 @ X19)
% 0.67/0.88          | ((X20) != (u1_struct_0 @ X18))
% 0.67/0.88          | (v3_pre_topc @ X20 @ X19)
% 0.67/0.88          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.67/0.88          | ~ (l1_pre_topc @ X19))),
% 0.67/0.88      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.67/0.88  thf('91', plain,
% 0.67/0.88      (![X18 : $i, X19 : $i]:
% 0.67/0.88         (~ (l1_pre_topc @ X19)
% 0.67/0.88          | ~ (m1_subset_1 @ (u1_struct_0 @ X18) @ 
% 0.67/0.88               (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.67/0.88          | (v3_pre_topc @ (u1_struct_0 @ X18) @ X19)
% 0.67/0.88          | ~ (v1_tsep_1 @ X18 @ X19)
% 0.67/0.88          | ~ (m1_pre_topc @ X18 @ X19))),
% 0.67/0.88      inference('simplify', [status(thm)], ['90'])).
% 0.67/0.88  thf('92', plain,
% 0.67/0.88      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.67/0.88        | ~ (v1_tsep_1 @ sk_B @ sk_A)
% 0.67/0.88        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.67/0.88        | ~ (l1_pre_topc @ sk_A))),
% 0.67/0.88      inference('sup-', [status(thm)], ['89', '91'])).
% 0.67/0.88  thf('93', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('94', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('95', plain,
% 0.67/0.88      ((~ (v1_tsep_1 @ sk_B @ sk_A)
% 0.67/0.88        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.67/0.88      inference('demod', [status(thm)], ['92', '93', '94'])).
% 0.67/0.88  thf('96', plain,
% 0.67/0.88      (((v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))
% 0.67/0.88         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.67/0.88      inference('sup-', [status(thm)], ['88', '95'])).
% 0.67/0.88  thf('97', plain,
% 0.67/0.88      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.67/0.88        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.88      inference('demod', [status(thm)], ['20', '21'])).
% 0.67/0.88  thf(t113_tmap_1, axiom,
% 0.67/0.88    (![A:$i]:
% 0.67/0.88     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.67/0.88       ( ![B:$i]:
% 0.67/0.88         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.67/0.88           ( ( v3_pre_topc @ B @ A ) <=>
% 0.67/0.88             ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) ) & 
% 0.67/0.88               ( v1_funct_2 @
% 0.67/0.88                 ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.67/0.88                 ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 0.67/0.88               ( v5_pre_topc @
% 0.67/0.88                 ( k7_tmap_1 @ A @ B ) @ A @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.67/0.88               ( m1_subset_1 @
% 0.67/0.88                 ( k7_tmap_1 @ A @ B ) @ 
% 0.67/0.88                 ( k1_zfmisc_1 @
% 0.67/0.88                   ( k2_zfmisc_1 @
% 0.67/0.88                     ( u1_struct_0 @ A ) @ 
% 0.67/0.88                     ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) ))).
% 0.67/0.88  thf('98', plain,
% 0.67/0.88      (![X29 : $i, X30 : $i]:
% 0.67/0.88         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.67/0.88          | ~ (v3_pre_topc @ X29 @ X30)
% 0.67/0.88          | (v5_pre_topc @ (k7_tmap_1 @ X30 @ X29) @ X30 @ 
% 0.67/0.88             (k6_tmap_1 @ X30 @ X29))
% 0.67/0.88          | ~ (l1_pre_topc @ X30)
% 0.67/0.88          | ~ (v2_pre_topc @ X30)
% 0.67/0.88          | (v2_struct_0 @ X30))),
% 0.67/0.88      inference('cnf', [status(esa)], [t113_tmap_1])).
% 0.67/0.88  thf('99', plain,
% 0.67/0.88      (((v2_struct_0 @ sk_A)
% 0.67/0.88        | ~ (v2_pre_topc @ sk_A)
% 0.67/0.88        | ~ (l1_pre_topc @ sk_A)
% 0.67/0.88        | (v5_pre_topc @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_A @ 
% 0.67/0.88           (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.67/0.88        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.67/0.88      inference('sup-', [status(thm)], ['97', '98'])).
% 0.67/0.88  thf('100', plain, ((v2_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('101', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('102', plain,
% 0.67/0.88      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.67/0.88        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.88      inference('demod', [status(thm)], ['20', '21'])).
% 0.67/0.88  thf(d10_tmap_1, axiom,
% 0.67/0.88    (![A:$i]:
% 0.67/0.88     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.67/0.88       ( ![B:$i]:
% 0.67/0.88         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.67/0.88           ( ( k7_tmap_1 @ A @ B ) = ( k6_partfun1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.67/0.88  thf('103', plain,
% 0.67/0.88      (![X8 : $i, X9 : $i]:
% 0.67/0.88         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.67/0.88          | ((k7_tmap_1 @ X9 @ X8) = (k6_partfun1 @ (u1_struct_0 @ X9)))
% 0.67/0.88          | ~ (l1_pre_topc @ X9)
% 0.67/0.88          | ~ (v2_pre_topc @ X9)
% 0.67/0.88          | (v2_struct_0 @ X9))),
% 0.67/0.88      inference('cnf', [status(esa)], [d10_tmap_1])).
% 0.67/0.88  thf('104', plain,
% 0.67/0.88      (((v2_struct_0 @ sk_A)
% 0.67/0.88        | ~ (v2_pre_topc @ sk_A)
% 0.67/0.88        | ~ (l1_pre_topc @ sk_A)
% 0.67/0.88        | ((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.67/0.88            = (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 0.67/0.88      inference('sup-', [status(thm)], ['102', '103'])).
% 0.67/0.88  thf('105', plain, ((v2_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('106', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('107', plain,
% 0.67/0.88      (((v2_struct_0 @ sk_A)
% 0.67/0.88        | ((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.67/0.88            = (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 0.67/0.88      inference('demod', [status(thm)], ['104', '105', '106'])).
% 0.67/0.88  thf('108', plain, (~ (v2_struct_0 @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('109', plain,
% 0.67/0.88      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.67/0.88         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.88      inference('clc', [status(thm)], ['107', '108'])).
% 0.67/0.88  thf('110', plain,
% 0.67/0.88      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.67/0.88      inference('clc', [status(thm)], ['61', '62'])).
% 0.67/0.88  thf('111', plain,
% 0.67/0.88      (((v2_struct_0 @ sk_A)
% 0.67/0.88        | (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 0.67/0.88           (k8_tmap_1 @ sk_A @ sk_B))
% 0.67/0.88        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.67/0.88      inference('demod', [status(thm)], ['99', '100', '101', '109', '110'])).
% 0.67/0.88  thf('112', plain, (~ (v2_struct_0 @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('113', plain,
% 0.67/0.88      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.67/0.88        | (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 0.67/0.88           (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.67/0.88      inference('clc', [status(thm)], ['111', '112'])).
% 0.67/0.88  thf('114', plain,
% 0.67/0.88      (((v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 0.67/0.88         (k8_tmap_1 @ sk_A @ sk_B))) <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.67/0.88      inference('sup-', [status(thm)], ['96', '113'])).
% 0.67/0.88  thf('115', plain,
% 0.67/0.88      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.67/0.88         = (u1_struct_0 @ sk_A))),
% 0.67/0.88      inference('clc', [status(thm)], ['27', '28'])).
% 0.67/0.88  thf(t2_tsep_1, axiom,
% 0.67/0.88    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.67/0.88  thf('116', plain,
% 0.67/0.88      (![X33 : $i]: ((m1_pre_topc @ X33 @ X33) | ~ (l1_pre_topc @ X33))),
% 0.67/0.88      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.67/0.88  thf('117', plain,
% 0.67/0.88      (![X31 : $i, X32 : $i]:
% 0.67/0.88         (~ (m1_pre_topc @ X31 @ X32)
% 0.67/0.88          | (m1_subset_1 @ (u1_struct_0 @ X31) @ 
% 0.67/0.88             (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.67/0.88          | ~ (l1_pre_topc @ X32))),
% 0.67/0.88      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.67/0.88  thf('118', plain,
% 0.67/0.88      (![X0 : $i]:
% 0.67/0.88         (~ (l1_pre_topc @ X0)
% 0.67/0.88          | ~ (l1_pre_topc @ X0)
% 0.67/0.88          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.67/0.88             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.67/0.88      inference('sup-', [status(thm)], ['116', '117'])).
% 0.67/0.88  thf('119', plain,
% 0.67/0.88      (![X0 : $i]:
% 0.67/0.88         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.67/0.88           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.67/0.88          | ~ (l1_pre_topc @ X0))),
% 0.67/0.88      inference('simplify', [status(thm)], ['118'])).
% 0.67/0.88  thf('120', plain,
% 0.67/0.88      (((m1_subset_1 @ 
% 0.67/0.88         (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))) @ 
% 0.67/0.88         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.67/0.88        | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.67/0.88      inference('sup+', [status(thm)], ['115', '119'])).
% 0.67/0.88  thf('121', plain,
% 0.67/0.88      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.67/0.88         = (u1_struct_0 @ sk_A))),
% 0.67/0.88      inference('clc', [status(thm)], ['27', '28'])).
% 0.67/0.88  thf('122', plain,
% 0.67/0.88      (((m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.67/0.88        | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 0.67/0.88      inference('demod', [status(thm)], ['120', '121'])).
% 0.67/0.88  thf('123', plain,
% 0.67/0.88      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.67/0.88      inference('clc', [status(thm)], ['61', '62'])).
% 0.67/0.88  thf('124', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.67/0.88      inference('clc', [status(thm)], ['40', '41'])).
% 0.67/0.88  thf('125', plain,
% 0.67/0.88      ((m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.88      inference('demod', [status(thm)], ['122', '123', '124'])).
% 0.67/0.88  thf(dt_k7_tmap_1, axiom,
% 0.67/0.88    (![A:$i,B:$i]:
% 0.67/0.88     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.67/0.88         ( l1_pre_topc @ A ) & 
% 0.67/0.88         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.67/0.88       ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) ) & 
% 0.67/0.88         ( v1_funct_2 @
% 0.67/0.88           ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.67/0.88           ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 0.67/0.88         ( m1_subset_1 @
% 0.67/0.88           ( k7_tmap_1 @ A @ B ) @ 
% 0.67/0.88           ( k1_zfmisc_1 @
% 0.67/0.88             ( k2_zfmisc_1 @
% 0.67/0.88               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ))).
% 0.67/0.88  thf('126', plain,
% 0.67/0.88      (![X21 : $i, X22 : $i]:
% 0.67/0.88         (~ (l1_pre_topc @ X21)
% 0.67/0.88          | ~ (v2_pre_topc @ X21)
% 0.67/0.88          | (v2_struct_0 @ X21)
% 0.67/0.88          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.67/0.88          | (v1_funct_2 @ (k7_tmap_1 @ X21 @ X22) @ (u1_struct_0 @ X21) @ 
% 0.67/0.88             (u1_struct_0 @ (k6_tmap_1 @ X21 @ X22))))),
% 0.67/0.88      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.67/0.88  thf('127', plain,
% 0.67/0.88      (((v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)) @ 
% 0.67/0.88         (u1_struct_0 @ sk_A) @ 
% 0.67/0.88         (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))))
% 0.67/0.88        | (v2_struct_0 @ sk_A)
% 0.67/0.88        | ~ (v2_pre_topc @ sk_A)
% 0.67/0.88        | ~ (l1_pre_topc @ sk_A))),
% 0.67/0.88      inference('sup-', [status(thm)], ['125', '126'])).
% 0.67/0.88  thf('128', plain,
% 0.67/0.88      ((m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.88      inference('demod', [status(thm)], ['122', '123', '124'])).
% 0.67/0.88  thf('129', plain,
% 0.67/0.88      (![X8 : $i, X9 : $i]:
% 0.67/0.88         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.67/0.88          | ((k7_tmap_1 @ X9 @ X8) = (k6_partfun1 @ (u1_struct_0 @ X9)))
% 0.67/0.88          | ~ (l1_pre_topc @ X9)
% 0.67/0.88          | ~ (v2_pre_topc @ X9)
% 0.67/0.88          | (v2_struct_0 @ X9))),
% 0.67/0.88      inference('cnf', [status(esa)], [d10_tmap_1])).
% 0.67/0.88  thf('130', plain,
% 0.67/0.88      (((v2_struct_0 @ sk_A)
% 0.67/0.88        | ~ (v2_pre_topc @ sk_A)
% 0.67/0.88        | ~ (l1_pre_topc @ sk_A)
% 0.67/0.88        | ((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))
% 0.67/0.88            = (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 0.67/0.88      inference('sup-', [status(thm)], ['128', '129'])).
% 0.67/0.88  thf('131', plain, ((v2_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('132', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('133', plain,
% 0.67/0.88      (((v2_struct_0 @ sk_A)
% 0.67/0.88        | ((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))
% 0.67/0.88            = (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 0.67/0.88      inference('demod', [status(thm)], ['130', '131', '132'])).
% 0.67/0.88  thf('134', plain, (~ (v2_struct_0 @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('135', plain,
% 0.67/0.88      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))
% 0.67/0.88         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.88      inference('clc', [status(thm)], ['133', '134'])).
% 0.67/0.88  thf('136', plain,
% 0.67/0.88      (![X33 : $i]: ((m1_pre_topc @ X33 @ X33) | ~ (l1_pre_topc @ X33))),
% 0.67/0.88      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.67/0.88  thf('137', plain,
% 0.67/0.88      (![X33 : $i]: ((m1_pre_topc @ X33 @ X33) | ~ (l1_pre_topc @ X33))),
% 0.67/0.88      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.67/0.88  thf('138', plain,
% 0.67/0.88      (![X23 : $i, X24 : $i]:
% 0.67/0.88         (~ (l1_pre_topc @ X23)
% 0.67/0.88          | ~ (v2_pre_topc @ X23)
% 0.67/0.88          | (v2_struct_0 @ X23)
% 0.67/0.88          | ~ (m1_pre_topc @ X24 @ X23)
% 0.67/0.88          | (v1_pre_topc @ (k8_tmap_1 @ X23 @ X24)))),
% 0.67/0.88      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.67/0.88  thf('139', plain,
% 0.67/0.88      (![X0 : $i]:
% 0.67/0.88         (~ (l1_pre_topc @ X0)
% 0.67/0.88          | (v1_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 0.67/0.88          | (v2_struct_0 @ X0)
% 0.67/0.88          | ~ (v2_pre_topc @ X0)
% 0.67/0.88          | ~ (l1_pre_topc @ X0))),
% 0.67/0.88      inference('sup-', [status(thm)], ['137', '138'])).
% 0.67/0.88  thf('140', plain,
% 0.67/0.88      (![X0 : $i]:
% 0.67/0.88         (~ (v2_pre_topc @ X0)
% 0.67/0.88          | (v2_struct_0 @ X0)
% 0.67/0.88          | (v1_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 0.67/0.88          | ~ (l1_pre_topc @ X0))),
% 0.67/0.88      inference('simplify', [status(thm)], ['139'])).
% 0.67/0.88  thf('141', plain,
% 0.67/0.88      (![X33 : $i]: ((m1_pre_topc @ X33 @ X33) | ~ (l1_pre_topc @ X33))),
% 0.67/0.88      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.67/0.88  thf('142', plain,
% 0.67/0.88      (![X23 : $i, X24 : $i]:
% 0.67/0.88         (~ (l1_pre_topc @ X23)
% 0.67/0.88          | ~ (v2_pre_topc @ X23)
% 0.67/0.88          | (v2_struct_0 @ X23)
% 0.67/0.88          | ~ (m1_pre_topc @ X24 @ X23)
% 0.67/0.88          | (v2_pre_topc @ (k8_tmap_1 @ X23 @ X24)))),
% 0.67/0.88      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.67/0.88  thf('143', plain,
% 0.67/0.88      (![X0 : $i]:
% 0.67/0.88         (~ (l1_pre_topc @ X0)
% 0.67/0.88          | (v2_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 0.67/0.88          | (v2_struct_0 @ X0)
% 0.67/0.88          | ~ (v2_pre_topc @ X0)
% 0.67/0.88          | ~ (l1_pre_topc @ X0))),
% 0.67/0.88      inference('sup-', [status(thm)], ['141', '142'])).
% 0.67/0.88  thf('144', plain,
% 0.67/0.88      (![X0 : $i]:
% 0.67/0.88         (~ (v2_pre_topc @ X0)
% 0.67/0.88          | (v2_struct_0 @ X0)
% 0.67/0.88          | (v2_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 0.67/0.88          | ~ (l1_pre_topc @ X0))),
% 0.67/0.88      inference('simplify', [status(thm)], ['143'])).
% 0.67/0.88  thf('145', plain,
% 0.67/0.88      (![X33 : $i]: ((m1_pre_topc @ X33 @ X33) | ~ (l1_pre_topc @ X33))),
% 0.67/0.88      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.67/0.88  thf('146', plain,
% 0.67/0.88      (![X23 : $i, X24 : $i]:
% 0.67/0.88         (~ (l1_pre_topc @ X23)
% 0.67/0.88          | ~ (v2_pre_topc @ X23)
% 0.67/0.88          | (v2_struct_0 @ X23)
% 0.67/0.88          | ~ (m1_pre_topc @ X24 @ X23)
% 0.67/0.88          | (l1_pre_topc @ (k8_tmap_1 @ X23 @ X24)))),
% 0.67/0.88      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.67/0.88  thf('147', plain,
% 0.67/0.88      (![X0 : $i]:
% 0.67/0.88         (~ (l1_pre_topc @ X0)
% 0.67/0.88          | (l1_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 0.67/0.88          | (v2_struct_0 @ X0)
% 0.67/0.88          | ~ (v2_pre_topc @ X0)
% 0.67/0.88          | ~ (l1_pre_topc @ X0))),
% 0.67/0.88      inference('sup-', [status(thm)], ['145', '146'])).
% 0.67/0.88  thf('148', plain,
% 0.67/0.88      (![X0 : $i]:
% 0.67/0.88         (~ (v2_pre_topc @ X0)
% 0.67/0.88          | (v2_struct_0 @ X0)
% 0.67/0.88          | (l1_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 0.67/0.88          | ~ (l1_pre_topc @ X0))),
% 0.67/0.88      inference('simplify', [status(thm)], ['147'])).
% 0.67/0.88  thf('149', plain,
% 0.67/0.88      ((m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.88      inference('demod', [status(thm)], ['122', '123', '124'])).
% 0.67/0.88  thf('150', plain,
% 0.67/0.88      (![X10 : $i, X11 : $i]:
% 0.67/0.88         ((v2_struct_0 @ X11)
% 0.67/0.88          | ~ (v2_pre_topc @ X11)
% 0.67/0.88          | ~ (l1_pre_topc @ X11)
% 0.67/0.88          | ~ (v1_pre_topc @ (k8_tmap_1 @ X11 @ X10))
% 0.67/0.88          | ~ (v2_pre_topc @ (k8_tmap_1 @ X11 @ X10))
% 0.67/0.88          | ~ (l1_pre_topc @ (k8_tmap_1 @ X11 @ X10))
% 0.67/0.88          | ~ (m1_subset_1 @ (u1_struct_0 @ X10) @ 
% 0.67/0.88               (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.67/0.88          | ((k8_tmap_1 @ X11 @ X10) = (k6_tmap_1 @ X11 @ (u1_struct_0 @ X10)))
% 0.67/0.88          | ~ (m1_pre_topc @ X10 @ X11))),
% 0.67/0.88      inference('simplify', [status(thm)], ['31'])).
% 0.67/0.88  thf('151', plain,
% 0.67/0.88      ((~ (m1_pre_topc @ sk_A @ sk_A)
% 0.67/0.88        | ((k8_tmap_1 @ sk_A @ sk_A)
% 0.67/0.88            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.67/0.88        | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 0.67/0.88        | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 0.67/0.88        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 0.67/0.88        | ~ (l1_pre_topc @ sk_A)
% 0.67/0.88        | ~ (v2_pre_topc @ sk_A)
% 0.67/0.88        | (v2_struct_0 @ sk_A))),
% 0.67/0.88      inference('sup-', [status(thm)], ['149', '150'])).
% 0.67/0.88  thf('152', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('153', plain, ((v2_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('154', plain,
% 0.67/0.88      ((~ (m1_pre_topc @ sk_A @ sk_A)
% 0.67/0.88        | ((k8_tmap_1 @ sk_A @ sk_A)
% 0.67/0.88            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.67/0.88        | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 0.67/0.88        | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 0.67/0.88        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 0.67/0.88        | (v2_struct_0 @ sk_A))),
% 0.67/0.88      inference('demod', [status(thm)], ['151', '152', '153'])).
% 0.67/0.88  thf('155', plain,
% 0.67/0.88      ((~ (l1_pre_topc @ sk_A)
% 0.67/0.88        | (v2_struct_0 @ sk_A)
% 0.67/0.88        | ~ (v2_pre_topc @ sk_A)
% 0.67/0.88        | (v2_struct_0 @ sk_A)
% 0.67/0.88        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 0.67/0.88        | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 0.67/0.88        | ((k8_tmap_1 @ sk_A @ sk_A)
% 0.67/0.88            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.67/0.88        | ~ (m1_pre_topc @ sk_A @ sk_A))),
% 0.67/0.88      inference('sup-', [status(thm)], ['148', '154'])).
% 0.67/0.88  thf('156', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('157', plain, ((v2_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('158', plain,
% 0.67/0.88      (((v2_struct_0 @ sk_A)
% 0.67/0.88        | (v2_struct_0 @ sk_A)
% 0.67/0.88        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 0.67/0.88        | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 0.67/0.88        | ((k8_tmap_1 @ sk_A @ sk_A)
% 0.67/0.88            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.67/0.88        | ~ (m1_pre_topc @ sk_A @ sk_A))),
% 0.67/0.88      inference('demod', [status(thm)], ['155', '156', '157'])).
% 0.67/0.88  thf('159', plain,
% 0.67/0.88      ((~ (m1_pre_topc @ sk_A @ sk_A)
% 0.67/0.88        | ((k8_tmap_1 @ sk_A @ sk_A)
% 0.67/0.88            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.67/0.88        | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 0.67/0.88        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 0.67/0.88        | (v2_struct_0 @ sk_A))),
% 0.67/0.88      inference('simplify', [status(thm)], ['158'])).
% 0.67/0.88  thf('160', plain,
% 0.67/0.88      ((~ (l1_pre_topc @ sk_A)
% 0.67/0.88        | (v2_struct_0 @ sk_A)
% 0.67/0.88        | ~ (v2_pre_topc @ sk_A)
% 0.67/0.88        | (v2_struct_0 @ sk_A)
% 0.67/0.88        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 0.67/0.88        | ((k8_tmap_1 @ sk_A @ sk_A)
% 0.67/0.88            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.67/0.88        | ~ (m1_pre_topc @ sk_A @ sk_A))),
% 0.67/0.88      inference('sup-', [status(thm)], ['144', '159'])).
% 0.67/0.88  thf('161', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('162', plain, ((v2_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('163', plain,
% 0.67/0.88      (((v2_struct_0 @ sk_A)
% 0.67/0.88        | (v2_struct_0 @ sk_A)
% 0.67/0.88        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 0.67/0.88        | ((k8_tmap_1 @ sk_A @ sk_A)
% 0.67/0.88            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.67/0.88        | ~ (m1_pre_topc @ sk_A @ sk_A))),
% 0.67/0.88      inference('demod', [status(thm)], ['160', '161', '162'])).
% 0.67/0.88  thf('164', plain,
% 0.67/0.88      ((~ (m1_pre_topc @ sk_A @ sk_A)
% 0.67/0.88        | ((k8_tmap_1 @ sk_A @ sk_A)
% 0.67/0.88            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.67/0.88        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 0.67/0.88        | (v2_struct_0 @ sk_A))),
% 0.67/0.88      inference('simplify', [status(thm)], ['163'])).
% 0.67/0.88  thf('165', plain,
% 0.67/0.88      ((~ (l1_pre_topc @ sk_A)
% 0.67/0.88        | (v2_struct_0 @ sk_A)
% 0.67/0.88        | ~ (v2_pre_topc @ sk_A)
% 0.67/0.88        | (v2_struct_0 @ sk_A)
% 0.67/0.88        | ((k8_tmap_1 @ sk_A @ sk_A)
% 0.67/0.88            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.67/0.88        | ~ (m1_pre_topc @ sk_A @ sk_A))),
% 0.67/0.88      inference('sup-', [status(thm)], ['140', '164'])).
% 0.67/0.88  thf('166', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('167', plain, ((v2_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('168', plain,
% 0.67/0.88      (((v2_struct_0 @ sk_A)
% 0.67/0.88        | (v2_struct_0 @ sk_A)
% 0.67/0.88        | ((k8_tmap_1 @ sk_A @ sk_A)
% 0.67/0.88            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.67/0.88        | ~ (m1_pre_topc @ sk_A @ sk_A))),
% 0.67/0.88      inference('demod', [status(thm)], ['165', '166', '167'])).
% 0.67/0.88  thf('169', plain,
% 0.67/0.88      ((~ (m1_pre_topc @ sk_A @ sk_A)
% 0.67/0.88        | ((k8_tmap_1 @ sk_A @ sk_A)
% 0.67/0.88            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.67/0.88        | (v2_struct_0 @ sk_A))),
% 0.67/0.88      inference('simplify', [status(thm)], ['168'])).
% 0.67/0.88  thf('170', plain, (~ (v2_struct_0 @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('171', plain,
% 0.67/0.88      ((((k8_tmap_1 @ sk_A @ sk_A) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.67/0.88        | ~ (m1_pre_topc @ sk_A @ sk_A))),
% 0.67/0.88      inference('clc', [status(thm)], ['169', '170'])).
% 0.67/0.88  thf('172', plain,
% 0.67/0.88      ((~ (l1_pre_topc @ sk_A)
% 0.67/0.88        | ((k8_tmap_1 @ sk_A @ sk_A)
% 0.67/0.88            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))))),
% 0.67/0.88      inference('sup-', [status(thm)], ['136', '171'])).
% 0.67/0.88  thf('173', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('174', plain,
% 0.67/0.88      (((k8_tmap_1 @ sk_A @ sk_A) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))),
% 0.67/0.88      inference('demod', [status(thm)], ['172', '173'])).
% 0.67/0.88  thf('175', plain,
% 0.67/0.88      ((m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.88      inference('demod', [status(thm)], ['122', '123', '124'])).
% 0.67/0.88  thf('176', plain,
% 0.67/0.88      (![X27 : $i, X28 : $i]:
% 0.67/0.88         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.67/0.88          | ((u1_struct_0 @ (k6_tmap_1 @ X28 @ X27)) = (u1_struct_0 @ X28))
% 0.67/0.88          | ~ (l1_pre_topc @ X28)
% 0.67/0.88          | ~ (v2_pre_topc @ X28)
% 0.67/0.88          | (v2_struct_0 @ X28))),
% 0.67/0.88      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.67/0.88  thf('177', plain,
% 0.67/0.88      (((v2_struct_0 @ sk_A)
% 0.67/0.88        | ~ (v2_pre_topc @ sk_A)
% 0.67/0.88        | ~ (l1_pre_topc @ sk_A)
% 0.67/0.88        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.67/0.88            = (u1_struct_0 @ sk_A)))),
% 0.67/0.88      inference('sup-', [status(thm)], ['175', '176'])).
% 0.67/0.88  thf('178', plain, ((v2_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('179', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('180', plain,
% 0.67/0.88      (((v2_struct_0 @ sk_A)
% 0.67/0.88        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.67/0.88            = (u1_struct_0 @ sk_A)))),
% 0.67/0.88      inference('demod', [status(thm)], ['177', '178', '179'])).
% 0.67/0.88  thf('181', plain, (~ (v2_struct_0 @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('182', plain,
% 0.67/0.88      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.67/0.88         = (u1_struct_0 @ sk_A))),
% 0.67/0.88      inference('clc', [status(thm)], ['180', '181'])).
% 0.67/0.88  thf('183', plain,
% 0.67/0.88      (((k8_tmap_1 @ sk_A @ sk_A) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))),
% 0.67/0.88      inference('demod', [status(thm)], ['172', '173'])).
% 0.67/0.88  thf('184', plain,
% 0.67/0.88      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_A)) = (u1_struct_0 @ sk_A))),
% 0.67/0.88      inference('demod', [status(thm)], ['182', '183'])).
% 0.67/0.88  thf('185', plain, ((v2_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('186', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('187', plain,
% 0.67/0.88      (((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.67/0.88         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.67/0.88        | (v2_struct_0 @ sk_A))),
% 0.67/0.88      inference('demod', [status(thm)],
% 0.67/0.88                ['127', '135', '174', '184', '185', '186'])).
% 0.67/0.88  thf('188', plain, (~ (v2_struct_0 @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('189', plain,
% 0.67/0.88      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.67/0.88        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.67/0.88      inference('clc', [status(thm)], ['187', '188'])).
% 0.67/0.88  thf('190', plain,
% 0.67/0.88      ((m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.88      inference('demod', [status(thm)], ['122', '123', '124'])).
% 0.67/0.88  thf('191', plain,
% 0.67/0.88      (![X21 : $i, X22 : $i]:
% 0.67/0.88         (~ (l1_pre_topc @ X21)
% 0.67/0.88          | ~ (v2_pre_topc @ X21)
% 0.67/0.88          | (v2_struct_0 @ X21)
% 0.67/0.88          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.67/0.88          | (m1_subset_1 @ (k7_tmap_1 @ X21 @ X22) @ 
% 0.67/0.88             (k1_zfmisc_1 @ 
% 0.67/0.88              (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ 
% 0.67/0.88               (u1_struct_0 @ (k6_tmap_1 @ X21 @ X22))))))),
% 0.67/0.88      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.67/0.88  thf('192', plain,
% 0.67/0.88      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)) @ 
% 0.67/0.88         (k1_zfmisc_1 @ 
% 0.67/0.88          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))))))
% 0.67/0.88        | (v2_struct_0 @ sk_A)
% 0.67/0.88        | ~ (v2_pre_topc @ sk_A)
% 0.67/0.88        | ~ (l1_pre_topc @ sk_A))),
% 0.67/0.88      inference('sup-', [status(thm)], ['190', '191'])).
% 0.67/0.88  thf('193', plain,
% 0.67/0.88      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))
% 0.67/0.88         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.88      inference('clc', [status(thm)], ['133', '134'])).
% 0.67/0.88  thf('194', plain,
% 0.67/0.88      (((k8_tmap_1 @ sk_A @ sk_A) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))),
% 0.67/0.88      inference('demod', [status(thm)], ['172', '173'])).
% 0.67/0.88  thf('195', plain,
% 0.67/0.88      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_A)) = (u1_struct_0 @ sk_A))),
% 0.67/0.88      inference('demod', [status(thm)], ['182', '183'])).
% 0.67/0.88  thf('196', plain, ((v2_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('197', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('198', plain,
% 0.67/0.88      (((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.67/0.88         (k1_zfmisc_1 @ 
% 0.67/0.88          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.67/0.88        | (v2_struct_0 @ sk_A))),
% 0.67/0.88      inference('demod', [status(thm)],
% 0.67/0.88                ['192', '193', '194', '195', '196', '197'])).
% 0.67/0.88  thf('199', plain, (~ (v2_struct_0 @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('200', plain,
% 0.67/0.88      ((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.67/0.88        (k1_zfmisc_1 @ 
% 0.67/0.88         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 0.67/0.88      inference('clc', [status(thm)], ['198', '199'])).
% 0.67/0.88  thf('201', plain,
% 0.67/0.88      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.67/0.88      inference('demod', [status(thm)], ['29', '63'])).
% 0.67/0.88  thf('202', plain,
% 0.67/0.88      (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88         (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.67/0.88        | (v1_tsep_1 @ sk_B @ sk_A))),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('203', plain,
% 0.67/0.88      (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88         (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))
% 0.67/0.88         <= (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))),
% 0.67/0.88      inference('split', [status(esa)], ['202'])).
% 0.67/0.88  thf('204', plain,
% 0.67/0.88      (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88         (u1_struct_0 @ sk_A)))
% 0.67/0.88         <= (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))),
% 0.67/0.88      inference('sup+', [status(thm)], ['201', '203'])).
% 0.67/0.88  thf('205', plain,
% 0.67/0.88      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.67/0.88         (k1_zfmisc_1 @ 
% 0.67/0.88          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))
% 0.67/0.88        | (v1_tsep_1 @ sk_B @ sk_A))),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('206', plain,
% 0.67/0.88      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.67/0.88         (k1_zfmisc_1 @ 
% 0.67/0.88          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))))
% 0.67/0.88         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.67/0.88               (k1_zfmisc_1 @ 
% 0.67/0.88                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.67/0.88      inference('split', [status(esa)], ['205'])).
% 0.67/0.88  thf(d12_tmap_1, axiom,
% 0.67/0.88    (![A:$i]:
% 0.67/0.88     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.67/0.88       ( ![B:$i]:
% 0.67/0.88         ( ( m1_pre_topc @ B @ A ) =>
% 0.67/0.88           ( ![C:$i]:
% 0.67/0.88             ( ( ( v1_funct_1 @ C ) & 
% 0.67/0.88                 ( v1_funct_2 @
% 0.67/0.88                   C @ ( u1_struct_0 @ A ) @ 
% 0.67/0.88                   ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 0.67/0.88                 ( m1_subset_1 @
% 0.67/0.88                   C @ 
% 0.67/0.88                   ( k1_zfmisc_1 @
% 0.67/0.88                     ( k2_zfmisc_1 @
% 0.67/0.88                       ( u1_struct_0 @ A ) @ 
% 0.67/0.88                       ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) =>
% 0.67/0.88               ( ( ( C ) = ( k9_tmap_1 @ A @ B ) ) <=>
% 0.67/0.88                 ( ![D:$i]:
% 0.67/0.88                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.67/0.88                     ( ( ( D ) = ( u1_struct_0 @ B ) ) =>
% 0.67/0.88                       ( r1_funct_2 @
% 0.67/0.88                         ( u1_struct_0 @ A ) @ 
% 0.67/0.88                         ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) @ 
% 0.67/0.88                         ( u1_struct_0 @ A ) @ 
% 0.67/0.88                         ( u1_struct_0 @ ( k6_tmap_1 @ A @ D ) ) @ C @ 
% 0.67/0.88                         ( k7_tmap_1 @ A @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.67/0.88  thf('207', plain,
% 0.67/0.88      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.67/0.88         (~ (m1_pre_topc @ X14 @ X15)
% 0.67/0.88          | ((X16) != (k9_tmap_1 @ X15 @ X14))
% 0.67/0.88          | ((X17) != (u1_struct_0 @ X14))
% 0.67/0.88          | (r1_funct_2 @ (u1_struct_0 @ X15) @ 
% 0.67/0.88             (u1_struct_0 @ (k8_tmap_1 @ X15 @ X14)) @ (u1_struct_0 @ X15) @ 
% 0.67/0.88             (u1_struct_0 @ (k6_tmap_1 @ X15 @ X17)) @ X16 @ 
% 0.67/0.88             (k7_tmap_1 @ X15 @ X17))
% 0.67/0.88          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.67/0.88          | ~ (m1_subset_1 @ X16 @ 
% 0.67/0.88               (k1_zfmisc_1 @ 
% 0.67/0.88                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ 
% 0.67/0.88                 (u1_struct_0 @ (k8_tmap_1 @ X15 @ X14)))))
% 0.67/0.88          | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ X15) @ 
% 0.67/0.88               (u1_struct_0 @ (k8_tmap_1 @ X15 @ X14)))
% 0.67/0.88          | ~ (v1_funct_1 @ X16)
% 0.67/0.88          | ~ (l1_pre_topc @ X15)
% 0.67/0.88          | ~ (v2_pre_topc @ X15)
% 0.67/0.88          | (v2_struct_0 @ X15))),
% 0.67/0.88      inference('cnf', [status(esa)], [d12_tmap_1])).
% 0.67/0.88  thf('208', plain,
% 0.67/0.88      (![X14 : $i, X15 : $i]:
% 0.67/0.88         ((v2_struct_0 @ X15)
% 0.67/0.88          | ~ (v2_pre_topc @ X15)
% 0.67/0.88          | ~ (l1_pre_topc @ X15)
% 0.67/0.88          | ~ (v1_funct_1 @ (k9_tmap_1 @ X15 @ X14))
% 0.67/0.88          | ~ (v1_funct_2 @ (k9_tmap_1 @ X15 @ X14) @ (u1_struct_0 @ X15) @ 
% 0.67/0.88               (u1_struct_0 @ (k8_tmap_1 @ X15 @ X14)))
% 0.67/0.88          | ~ (m1_subset_1 @ (k9_tmap_1 @ X15 @ X14) @ 
% 0.67/0.88               (k1_zfmisc_1 @ 
% 0.67/0.88                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ 
% 0.67/0.88                 (u1_struct_0 @ (k8_tmap_1 @ X15 @ X14)))))
% 0.67/0.88          | ~ (m1_subset_1 @ (u1_struct_0 @ X14) @ 
% 0.67/0.88               (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.67/0.88          | (r1_funct_2 @ (u1_struct_0 @ X15) @ 
% 0.67/0.88             (u1_struct_0 @ (k8_tmap_1 @ X15 @ X14)) @ (u1_struct_0 @ X15) @ 
% 0.67/0.88             (u1_struct_0 @ (k6_tmap_1 @ X15 @ (u1_struct_0 @ X14))) @ 
% 0.67/0.88             (k9_tmap_1 @ X15 @ X14) @ (k7_tmap_1 @ X15 @ (u1_struct_0 @ X14)))
% 0.67/0.88          | ~ (m1_pre_topc @ X14 @ X15))),
% 0.67/0.88      inference('simplify', [status(thm)], ['207'])).
% 0.67/0.88  thf('209', plain,
% 0.67/0.88      (((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.67/0.88         | (r1_funct_2 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88            (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88            (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))) @ 
% 0.67/0.88            (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.67/0.88            (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.67/0.88         | ~ (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.67/0.88              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.67/0.88         | ~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88              (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.67/0.88         | ~ (v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))
% 0.67/0.88         | ~ (l1_pre_topc @ sk_A)
% 0.67/0.88         | ~ (v2_pre_topc @ sk_A)
% 0.67/0.88         | (v2_struct_0 @ sk_A)))
% 0.67/0.88         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.67/0.88               (k1_zfmisc_1 @ 
% 0.67/0.88                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.67/0.88      inference('sup-', [status(thm)], ['206', '208'])).
% 0.67/0.88  thf('210', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('211', plain,
% 0.67/0.88      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.67/0.88      inference('demod', [status(thm)], ['29', '63'])).
% 0.67/0.88  thf('212', plain,
% 0.67/0.88      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.67/0.88      inference('clc', [status(thm)], ['61', '62'])).
% 0.67/0.88  thf('213', plain,
% 0.67/0.88      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.67/0.88      inference('demod', [status(thm)], ['29', '63'])).
% 0.67/0.88  thf('214', plain,
% 0.67/0.88      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.67/0.88         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.88      inference('clc', [status(thm)], ['107', '108'])).
% 0.67/0.88  thf('215', plain,
% 0.67/0.88      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.67/0.88        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.88      inference('demod', [status(thm)], ['20', '21'])).
% 0.67/0.88  thf('216', plain,
% 0.67/0.88      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.67/0.88      inference('demod', [status(thm)], ['29', '63'])).
% 0.67/0.88  thf('217', plain, ((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))),
% 0.67/0.88      inference('clc', [status(thm)], ['10', '11'])).
% 0.67/0.88  thf('218', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('219', plain, ((v2_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('220', plain,
% 0.67/0.88      ((((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88          (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88          (k9_tmap_1 @ sk_A @ sk_B) @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 0.67/0.88         | ~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88              (u1_struct_0 @ sk_A))
% 0.67/0.88         | (v2_struct_0 @ sk_A)))
% 0.67/0.88         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.67/0.88               (k1_zfmisc_1 @ 
% 0.67/0.88                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.67/0.88      inference('demod', [status(thm)],
% 0.67/0.88                ['209', '210', '211', '212', '213', '214', '215', '216', 
% 0.67/0.88                 '217', '218', '219'])).
% 0.67/0.88  thf('221', plain, (~ (v2_struct_0 @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('222', plain,
% 0.67/0.88      (((~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88            (u1_struct_0 @ sk_A))
% 0.67/0.88         | (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88            (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88            (k9_tmap_1 @ sk_A @ sk_B) @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))))
% 0.67/0.88         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.67/0.88               (k1_zfmisc_1 @ 
% 0.67/0.88                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.67/0.88      inference('clc', [status(thm)], ['220', '221'])).
% 0.67/0.88  thf('223', plain,
% 0.67/0.88      (((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88         (k9_tmap_1 @ sk_A @ sk_B) @ (k6_partfun1 @ (u1_struct_0 @ sk_A))))
% 0.67/0.88         <= (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))) & 
% 0.67/0.88             ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.67/0.88               (k1_zfmisc_1 @ 
% 0.67/0.88                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.67/0.88      inference('sup-', [status(thm)], ['204', '222'])).
% 0.67/0.88  thf('224', plain,
% 0.67/0.88      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.67/0.88      inference('demod', [status(thm)], ['29', '63'])).
% 0.67/0.88  thf('225', plain,
% 0.67/0.88      (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88         (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))
% 0.67/0.88         <= (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))),
% 0.67/0.88      inference('split', [status(esa)], ['202'])).
% 0.67/0.88  thf('226', plain,
% 0.67/0.88      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.67/0.88         (k1_zfmisc_1 @ 
% 0.67/0.88          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))))
% 0.67/0.88         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.67/0.88               (k1_zfmisc_1 @ 
% 0.67/0.88                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.67/0.88      inference('split', [status(esa)], ['205'])).
% 0.67/0.88  thf(redefinition_r1_funct_2, axiom,
% 0.67/0.88    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.67/0.88     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 0.67/0.88         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 0.67/0.88         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.67/0.88         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 0.67/0.88         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.67/0.88       ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F ) <=> ( ( E ) = ( F ) ) ) ))).
% 0.67/0.88  thf('227', plain,
% 0.67/0.88      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.67/0.88         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4)))
% 0.67/0.88          | ~ (v1_funct_2 @ X2 @ X3 @ X4)
% 0.67/0.88          | ~ (v1_funct_1 @ X2)
% 0.67/0.88          | (v1_xboole_0 @ X5)
% 0.67/0.88          | (v1_xboole_0 @ X4)
% 0.67/0.88          | ~ (v1_funct_1 @ X6)
% 0.67/0.88          | ~ (v1_funct_2 @ X6 @ X7 @ X5)
% 0.67/0.88          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X5)))
% 0.67/0.88          | ((X2) = (X6))
% 0.67/0.88          | ~ (r1_funct_2 @ X3 @ X4 @ X7 @ X5 @ X2 @ X6))),
% 0.67/0.88      inference('cnf', [status(esa)], [redefinition_r1_funct_2])).
% 0.67/0.88  thf('228', plain,
% 0.67/0.88      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.88          (~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88              (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) @ X2 @ X1 @ 
% 0.67/0.88              (k9_tmap_1 @ sk_A @ sk_B) @ X0)
% 0.67/0.88           | ((k9_tmap_1 @ sk_A @ sk_B) = (X0))
% 0.67/0.88           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.67/0.88           | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 0.67/0.88           | ~ (v1_funct_1 @ X0)
% 0.67/0.88           | (v1_xboole_0 @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.67/0.88           | (v1_xboole_0 @ X1)
% 0.67/0.88           | ~ (v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))
% 0.67/0.88           | ~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.67/0.88                (u1_struct_0 @ sk_A) @ 
% 0.67/0.88                (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))
% 0.67/0.88         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.67/0.88               (k1_zfmisc_1 @ 
% 0.67/0.88                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.67/0.88      inference('sup-', [status(thm)], ['226', '227'])).
% 0.67/0.88  thf('229', plain,
% 0.67/0.88      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.88          (~ (v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))
% 0.67/0.88           | (v1_xboole_0 @ X0)
% 0.67/0.88           | (v1_xboole_0 @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.67/0.88           | ~ (v1_funct_1 @ X1)
% 0.67/0.88           | ~ (v1_funct_2 @ X1 @ X2 @ X0)
% 0.67/0.88           | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.67/0.88           | ((k9_tmap_1 @ sk_A @ sk_B) = (X1))
% 0.67/0.88           | ~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88                (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) @ X2 @ X0 @ 
% 0.67/0.88                (k9_tmap_1 @ sk_A @ sk_B) @ X1)))
% 0.67/0.88         <= (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))) & 
% 0.67/0.88             ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.67/0.88               (k1_zfmisc_1 @ 
% 0.67/0.88                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.67/0.88      inference('sup-', [status(thm)], ['225', '228'])).
% 0.67/0.88  thf('230', plain, ((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))),
% 0.67/0.88      inference('clc', [status(thm)], ['10', '11'])).
% 0.67/0.88  thf('231', plain,
% 0.67/0.88      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.88          ((v1_xboole_0 @ X0)
% 0.67/0.88           | (v1_xboole_0 @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.67/0.88           | ~ (v1_funct_1 @ X1)
% 0.67/0.88           | ~ (v1_funct_2 @ X1 @ X2 @ X0)
% 0.67/0.88           | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.67/0.88           | ((k9_tmap_1 @ sk_A @ sk_B) = (X1))
% 0.67/0.88           | ~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88                (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) @ X2 @ X0 @ 
% 0.67/0.88                (k9_tmap_1 @ sk_A @ sk_B) @ X1)))
% 0.67/0.88         <= (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))) & 
% 0.67/0.88             ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.67/0.88               (k1_zfmisc_1 @ 
% 0.67/0.88                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.67/0.88      inference('demod', [status(thm)], ['229', '230'])).
% 0.67/0.88  thf('232', plain,
% 0.67/0.88      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.88          (~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ X2 @ 
% 0.67/0.88              X1 @ (k9_tmap_1 @ sk_A @ sk_B) @ X0)
% 0.67/0.88           | ((k9_tmap_1 @ sk_A @ sk_B) = (X0))
% 0.67/0.88           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.67/0.88           | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 0.67/0.88           | ~ (v1_funct_1 @ X0)
% 0.67/0.88           | (v1_xboole_0 @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.67/0.88           | (v1_xboole_0 @ X1)))
% 0.67/0.88         <= (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))) & 
% 0.67/0.88             ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.67/0.88               (k1_zfmisc_1 @ 
% 0.67/0.88                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.67/0.88      inference('sup-', [status(thm)], ['224', '231'])).
% 0.67/0.88  thf('233', plain,
% 0.67/0.88      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.67/0.88      inference('demod', [status(thm)], ['29', '63'])).
% 0.67/0.88  thf('234', plain,
% 0.67/0.88      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.88          (~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ X2 @ 
% 0.67/0.88              X1 @ (k9_tmap_1 @ sk_A @ sk_B) @ X0)
% 0.67/0.88           | ((k9_tmap_1 @ sk_A @ sk_B) = (X0))
% 0.67/0.88           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.67/0.88           | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 0.67/0.88           | ~ (v1_funct_1 @ X0)
% 0.67/0.88           | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.67/0.88           | (v1_xboole_0 @ X1)))
% 0.67/0.88         <= (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))) & 
% 0.67/0.88             ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.67/0.88               (k1_zfmisc_1 @ 
% 0.67/0.88                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.67/0.88      inference('demod', [status(thm)], ['232', '233'])).
% 0.67/0.88  thf('235', plain,
% 0.67/0.88      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.67/0.88         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.67/0.88         | ~ (v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 0.67/0.88         | ~ (v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.67/0.88              (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.67/0.88         | ~ (m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.67/0.88              (k1_zfmisc_1 @ 
% 0.67/0.88               (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.67/0.88         | ((k9_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))))
% 0.67/0.88         <= (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))) & 
% 0.67/0.88             ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.67/0.88               (k1_zfmisc_1 @ 
% 0.67/0.88                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.67/0.88      inference('sup-', [status(thm)], ['223', '234'])).
% 0.67/0.88  thf('236', plain,
% 0.67/0.88      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.67/0.88        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.88      inference('demod', [status(thm)], ['20', '21'])).
% 0.67/0.88  thf('237', plain,
% 0.67/0.88      (![X21 : $i, X22 : $i]:
% 0.67/0.88         (~ (l1_pre_topc @ X21)
% 0.67/0.88          | ~ (v2_pre_topc @ X21)
% 0.67/0.88          | (v2_struct_0 @ X21)
% 0.67/0.88          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.67/0.88          | (v1_funct_1 @ (k7_tmap_1 @ X21 @ X22)))),
% 0.67/0.88      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.67/0.88  thf('238', plain,
% 0.67/0.88      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.67/0.88        | (v2_struct_0 @ sk_A)
% 0.67/0.88        | ~ (v2_pre_topc @ sk_A)
% 0.67/0.88        | ~ (l1_pre_topc @ sk_A))),
% 0.67/0.88      inference('sup-', [status(thm)], ['236', '237'])).
% 0.67/0.88  thf('239', plain, ((v2_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('240', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('241', plain,
% 0.67/0.88      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.67/0.88        | (v2_struct_0 @ sk_A))),
% 0.67/0.88      inference('demod', [status(thm)], ['238', '239', '240'])).
% 0.67/0.88  thf('242', plain, (~ (v2_struct_0 @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('243', plain, ((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.67/0.88      inference('clc', [status(thm)], ['241', '242'])).
% 0.67/0.88  thf('244', plain,
% 0.67/0.88      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.67/0.88         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.88      inference('clc', [status(thm)], ['107', '108'])).
% 0.67/0.88  thf('245', plain, ((v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.88      inference('demod', [status(thm)], ['243', '244'])).
% 0.67/0.88  thf('246', plain,
% 0.67/0.88      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.67/0.88         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.67/0.88         | ~ (v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.67/0.88              (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.67/0.88         | ~ (m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.67/0.88              (k1_zfmisc_1 @ 
% 0.67/0.88               (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.67/0.88         | ((k9_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))))
% 0.67/0.88         <= (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))) & 
% 0.67/0.88             ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.67/0.88               (k1_zfmisc_1 @ 
% 0.67/0.88                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.67/0.88      inference('demod', [status(thm)], ['235', '245'])).
% 0.67/0.88  thf('247', plain,
% 0.67/0.88      (((((k9_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 0.67/0.88         | ~ (m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.67/0.88              (k1_zfmisc_1 @ 
% 0.67/0.88               (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.67/0.88         | ~ (v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.67/0.88              (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.67/0.88         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.67/0.88         <= (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))) & 
% 0.67/0.88             ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.67/0.88               (k1_zfmisc_1 @ 
% 0.67/0.88                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.67/0.88      inference('simplify', [status(thm)], ['246'])).
% 0.67/0.88  thf('248', plain,
% 0.67/0.88      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.67/0.88         | ~ (v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.67/0.88              (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.67/0.88         | ((k9_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))))
% 0.67/0.88         <= (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))) & 
% 0.67/0.88             ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.67/0.88               (k1_zfmisc_1 @ 
% 0.67/0.88                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.67/0.88      inference('sup-', [status(thm)], ['200', '247'])).
% 0.67/0.88  thf('249', plain,
% 0.67/0.88      (((((k9_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 0.67/0.88         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.67/0.88         <= (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))) & 
% 0.67/0.88             ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.67/0.88               (k1_zfmisc_1 @ 
% 0.67/0.88                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.67/0.88      inference('sup-', [status(thm)], ['189', '248'])).
% 0.67/0.88  thf('250', plain,
% 0.67/0.88      ((~ (v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.67/0.88           (k8_tmap_1 @ sk_A @ sk_B)))
% 0.67/0.88         <= (~
% 0.67/0.88             ((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.67/0.88               (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.67/0.88      inference('split', [status(esa)], ['0'])).
% 0.67/0.88  thf('251', plain,
% 0.67/0.88      (((~ (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 0.67/0.88            (k8_tmap_1 @ sk_A @ sk_B))
% 0.67/0.88         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.67/0.88         <= (~
% 0.67/0.88             ((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.67/0.88               (k8_tmap_1 @ sk_A @ sk_B))) & 
% 0.67/0.88             ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))) & 
% 0.67/0.88             ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.67/0.88               (k1_zfmisc_1 @ 
% 0.67/0.88                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.67/0.88      inference('sup-', [status(thm)], ['249', '250'])).
% 0.67/0.88  thf('252', plain,
% 0.67/0.88      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.67/0.88         (k1_zfmisc_1 @ 
% 0.67/0.88          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))))),
% 0.67/0.88      inference('sat_resolution*', [status(thm)], ['86'])).
% 0.67/0.88  thf('253', plain,
% 0.67/0.88      (((~ (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 0.67/0.88            (k8_tmap_1 @ sk_A @ sk_B))
% 0.67/0.88         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.67/0.88         <= (~
% 0.67/0.88             ((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.67/0.88               (k8_tmap_1 @ sk_A @ sk_B))) & 
% 0.67/0.88             ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))),
% 0.67/0.88      inference('simpl_trail', [status(thm)], ['251', '252'])).
% 0.67/0.88  thf('254', plain,
% 0.67/0.88      (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88         (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.67/0.88      inference('sat_resolution*', [status(thm)], ['73'])).
% 0.67/0.88  thf('255', plain,
% 0.67/0.88      (((~ (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 0.67/0.88            (k8_tmap_1 @ sk_A @ sk_B))
% 0.67/0.88         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.67/0.88         <= (~
% 0.67/0.88             ((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.67/0.88               (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.67/0.88      inference('simpl_trail', [status(thm)], ['253', '254'])).
% 0.67/0.88  thf('256', plain,
% 0.67/0.88      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.67/0.88         <= (~
% 0.67/0.88             ((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.67/0.88               (k8_tmap_1 @ sk_A @ sk_B))) & 
% 0.67/0.88             ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.67/0.88      inference('sup-', [status(thm)], ['114', '255'])).
% 0.67/0.88  thf(fc2_struct_0, axiom,
% 0.67/0.88    (![A:$i]:
% 0.67/0.88     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.67/0.88       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.67/0.88  thf('257', plain,
% 0.67/0.88      (![X1 : $i]:
% 0.67/0.88         (~ (v1_xboole_0 @ (u1_struct_0 @ X1))
% 0.67/0.88          | ~ (l1_struct_0 @ X1)
% 0.67/0.88          | (v2_struct_0 @ X1))),
% 0.67/0.88      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.67/0.88  thf('258', plain,
% 0.67/0.88      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.67/0.88         <= (~
% 0.67/0.88             ((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.67/0.88               (k8_tmap_1 @ sk_A @ sk_B))) & 
% 0.67/0.88             ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.67/0.88      inference('sup-', [status(thm)], ['256', '257'])).
% 0.67/0.88  thf('259', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf(dt_l1_pre_topc, axiom,
% 0.67/0.88    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.67/0.88  thf('260', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.67/0.88      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.67/0.88  thf('261', plain, ((l1_struct_0 @ sk_A)),
% 0.67/0.88      inference('sup-', [status(thm)], ['259', '260'])).
% 0.67/0.88  thf('262', plain,
% 0.67/0.88      (((v2_struct_0 @ sk_A))
% 0.67/0.88         <= (~
% 0.67/0.88             ((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.67/0.88               (k8_tmap_1 @ sk_A @ sk_B))) & 
% 0.67/0.88             ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.67/0.88      inference('demod', [status(thm)], ['258', '261'])).
% 0.67/0.88  thf('263', plain, (~ (v2_struct_0 @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('264', plain,
% 0.67/0.88      (((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.67/0.88         (k8_tmap_1 @ sk_A @ sk_B))) | 
% 0.67/0.88       ~ ((v1_tsep_1 @ sk_B @ sk_A))),
% 0.67/0.88      inference('sup-', [status(thm)], ['262', '263'])).
% 0.67/0.88  thf('265', plain,
% 0.67/0.88      (((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.67/0.88         (k8_tmap_1 @ sk_A @ sk_B))
% 0.67/0.88        | (v1_tsep_1 @ sk_B @ sk_A))),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('266', plain,
% 0.67/0.88      (((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.67/0.88         (k8_tmap_1 @ sk_A @ sk_B))) | 
% 0.67/0.88       ((v1_tsep_1 @ sk_B @ sk_A))),
% 0.67/0.88      inference('split', [status(esa)], ['265'])).
% 0.67/0.88  thf('267', plain,
% 0.67/0.88      (((((k9_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 0.67/0.88         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.67/0.88         <= (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))) & 
% 0.67/0.88             ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.67/0.88               (k1_zfmisc_1 @ 
% 0.67/0.88                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.67/0.88      inference('sup-', [status(thm)], ['189', '248'])).
% 0.67/0.88  thf('268', plain,
% 0.67/0.88      (((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.67/0.88         (k8_tmap_1 @ sk_A @ sk_B)))
% 0.67/0.88         <= (((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.67/0.88               (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.67/0.88      inference('split', [status(esa)], ['265'])).
% 0.67/0.88  thf('269', plain,
% 0.67/0.88      ((((v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 0.67/0.88          (k8_tmap_1 @ sk_A @ sk_B))
% 0.67/0.88         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.67/0.88         <= (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))) & 
% 0.67/0.88             ((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.67/0.88               (k8_tmap_1 @ sk_A @ sk_B))) & 
% 0.67/0.88             ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.67/0.88               (k1_zfmisc_1 @ 
% 0.67/0.88                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.67/0.88      inference('sup+', [status(thm)], ['267', '268'])).
% 0.67/0.88  thf('270', plain,
% 0.67/0.88      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.67/0.88         (k1_zfmisc_1 @ 
% 0.67/0.88          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))))),
% 0.67/0.88      inference('sat_resolution*', [status(thm)], ['86'])).
% 0.67/0.88  thf('271', plain,
% 0.67/0.88      ((((v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 0.67/0.88          (k8_tmap_1 @ sk_A @ sk_B))
% 0.67/0.88         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.67/0.88         <= (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))) & 
% 0.67/0.88             ((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.67/0.88               (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.67/0.88      inference('simpl_trail', [status(thm)], ['269', '270'])).
% 0.67/0.88  thf('272', plain,
% 0.67/0.88      (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88         (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.67/0.88      inference('sat_resolution*', [status(thm)], ['73'])).
% 0.67/0.88  thf('273', plain,
% 0.67/0.88      ((((v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 0.67/0.88          (k8_tmap_1 @ sk_A @ sk_B))
% 0.67/0.88         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.67/0.88         <= (((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.67/0.88               (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.67/0.88      inference('simpl_trail', [status(thm)], ['271', '272'])).
% 0.67/0.88  thf('274', plain,
% 0.67/0.88      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.67/0.88         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.88      inference('clc', [status(thm)], ['107', '108'])).
% 0.67/0.88  thf('275', plain,
% 0.67/0.88      (![X29 : $i, X30 : $i]:
% 0.67/0.88         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.67/0.88          | ~ (v1_funct_1 @ (k7_tmap_1 @ X30 @ X29))
% 0.67/0.88          | ~ (v1_funct_2 @ (k7_tmap_1 @ X30 @ X29) @ (u1_struct_0 @ X30) @ 
% 0.67/0.88               (u1_struct_0 @ (k6_tmap_1 @ X30 @ X29)))
% 0.67/0.88          | ~ (v5_pre_topc @ (k7_tmap_1 @ X30 @ X29) @ X30 @ 
% 0.67/0.88               (k6_tmap_1 @ X30 @ X29))
% 0.67/0.88          | ~ (m1_subset_1 @ (k7_tmap_1 @ X30 @ X29) @ 
% 0.67/0.88               (k1_zfmisc_1 @ 
% 0.67/0.88                (k2_zfmisc_1 @ (u1_struct_0 @ X30) @ 
% 0.67/0.88                 (u1_struct_0 @ (k6_tmap_1 @ X30 @ X29)))))
% 0.67/0.88          | (v3_pre_topc @ X29 @ X30)
% 0.67/0.88          | ~ (l1_pre_topc @ X30)
% 0.67/0.88          | ~ (v2_pre_topc @ X30)
% 0.67/0.88          | (v2_struct_0 @ X30))),
% 0.67/0.88      inference('cnf', [status(esa)], [t113_tmap_1])).
% 0.67/0.88  thf('276', plain,
% 0.67/0.88      ((~ (m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.67/0.88           (k1_zfmisc_1 @ 
% 0.67/0.88            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.67/0.88             (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))))
% 0.67/0.88        | (v2_struct_0 @ sk_A)
% 0.67/0.88        | ~ (v2_pre_topc @ sk_A)
% 0.67/0.88        | ~ (l1_pre_topc @ sk_A)
% 0.67/0.88        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.67/0.88        | ~ (v5_pre_topc @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_A @ 
% 0.67/0.88             (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.67/0.88        | ~ (v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.67/0.88             (u1_struct_0 @ sk_A) @ 
% 0.67/0.88             (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))
% 0.67/0.88        | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.67/0.88        | ~ (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.67/0.88             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.67/0.88      inference('sup-', [status(thm)], ['274', '275'])).
% 0.67/0.88  thf('277', plain,
% 0.67/0.88      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.67/0.88      inference('clc', [status(thm)], ['61', '62'])).
% 0.67/0.88  thf('278', plain,
% 0.67/0.88      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.67/0.88      inference('demod', [status(thm)], ['29', '63'])).
% 0.67/0.88  thf('279', plain,
% 0.67/0.88      ((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.67/0.88        (k1_zfmisc_1 @ 
% 0.67/0.88         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 0.67/0.88      inference('clc', [status(thm)], ['198', '199'])).
% 0.67/0.88  thf('280', plain, ((v2_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('281', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('282', plain,
% 0.67/0.88      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.67/0.88         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.88      inference('clc', [status(thm)], ['107', '108'])).
% 0.67/0.88  thf('283', plain,
% 0.67/0.88      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.67/0.88      inference('clc', [status(thm)], ['61', '62'])).
% 0.67/0.88  thf('284', plain,
% 0.67/0.88      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.67/0.88         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.88      inference('clc', [status(thm)], ['107', '108'])).
% 0.67/0.88  thf('285', plain,
% 0.67/0.88      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.67/0.88      inference('clc', [status(thm)], ['61', '62'])).
% 0.67/0.88  thf('286', plain,
% 0.67/0.88      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.67/0.88      inference('demod', [status(thm)], ['29', '63'])).
% 0.67/0.88  thf('287', plain,
% 0.67/0.88      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.67/0.88        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.67/0.88      inference('clc', [status(thm)], ['187', '188'])).
% 0.67/0.88  thf('288', plain,
% 0.67/0.88      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.67/0.88         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.88      inference('clc', [status(thm)], ['107', '108'])).
% 0.67/0.88  thf('289', plain, ((v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.88      inference('demod', [status(thm)], ['243', '244'])).
% 0.67/0.88  thf('290', plain,
% 0.67/0.88      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.67/0.88        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.88      inference('demod', [status(thm)], ['20', '21'])).
% 0.67/0.88  thf('291', plain,
% 0.67/0.88      (((v2_struct_0 @ sk_A)
% 0.67/0.88        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.67/0.88        | ~ (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 0.67/0.88             (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.67/0.88      inference('demod', [status(thm)],
% 0.67/0.88                ['276', '277', '278', '279', '280', '281', '282', '283', 
% 0.67/0.88                 '284', '285', '286', '287', '288', '289', '290'])).
% 0.67/0.88  thf('292', plain, (~ (v2_struct_0 @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('293', plain,
% 0.67/0.88      ((~ (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 0.67/0.88           (k8_tmap_1 @ sk_A @ sk_B))
% 0.67/0.88        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.67/0.88      inference('clc', [status(thm)], ['291', '292'])).
% 0.67/0.88  thf('294', plain,
% 0.67/0.88      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.67/0.88         | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)))
% 0.67/0.88         <= (((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.67/0.88               (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.67/0.88      inference('sup-', [status(thm)], ['273', '293'])).
% 0.67/0.88  thf('295', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('296', plain,
% 0.67/0.88      (![X18 : $i, X19 : $i]:
% 0.67/0.88         (~ (m1_pre_topc @ X18 @ X19)
% 0.67/0.88          | ((sk_C @ X18 @ X19) = (u1_struct_0 @ X18))
% 0.67/0.88          | (v1_tsep_1 @ X18 @ X19)
% 0.67/0.88          | ~ (l1_pre_topc @ X19))),
% 0.67/0.88      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.67/0.88  thf('297', plain,
% 0.67/0.88      ((~ (l1_pre_topc @ sk_A)
% 0.67/0.88        | (v1_tsep_1 @ sk_B @ sk_A)
% 0.67/0.88        | ((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))),
% 0.67/0.88      inference('sup-', [status(thm)], ['295', '296'])).
% 0.67/0.88  thf('298', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('299', plain,
% 0.67/0.88      (((v1_tsep_1 @ sk_B @ sk_A)
% 0.67/0.88        | ((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))),
% 0.67/0.88      inference('demod', [status(thm)], ['297', '298'])).
% 0.67/0.88  thf('300', plain,
% 0.67/0.88      ((~ (v1_tsep_1 @ sk_B @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.67/0.88      inference('split', [status(esa)], ['0'])).
% 0.67/0.88  thf('301', plain,
% 0.67/0.88      ((((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))
% 0.67/0.88         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.67/0.88      inference('sup-', [status(thm)], ['299', '300'])).
% 0.67/0.88  thf('302', plain,
% 0.67/0.88      (![X18 : $i, X19 : $i]:
% 0.67/0.88         (~ (m1_pre_topc @ X18 @ X19)
% 0.67/0.88          | ~ (v3_pre_topc @ (sk_C @ X18 @ X19) @ X19)
% 0.67/0.88          | (v1_tsep_1 @ X18 @ X19)
% 0.67/0.88          | ~ (l1_pre_topc @ X19))),
% 0.67/0.88      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.67/0.88  thf('303', plain,
% 0.67/0.88      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.67/0.88         | ~ (l1_pre_topc @ sk_A)
% 0.67/0.88         | (v1_tsep_1 @ sk_B @ sk_A)
% 0.67/0.88         | ~ (m1_pre_topc @ sk_B @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.67/0.88      inference('sup-', [status(thm)], ['301', '302'])).
% 0.67/0.88  thf('304', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('305', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('306', plain,
% 0.67/0.88      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.67/0.88         | (v1_tsep_1 @ sk_B @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.67/0.88      inference('demod', [status(thm)], ['303', '304', '305'])).
% 0.67/0.88  thf('307', plain,
% 0.67/0.88      ((~ (v1_tsep_1 @ sk_B @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.67/0.88      inference('split', [status(esa)], ['0'])).
% 0.67/0.88  thf('308', plain,
% 0.67/0.88      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))
% 0.67/0.88         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.67/0.88      inference('clc', [status(thm)], ['306', '307'])).
% 0.67/0.88  thf('309', plain,
% 0.67/0.88      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.67/0.88         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)) & 
% 0.67/0.88             ((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.67/0.88               (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.67/0.88      inference('sup-', [status(thm)], ['294', '308'])).
% 0.67/0.88  thf('310', plain,
% 0.67/0.88      (![X1 : $i]:
% 0.67/0.88         (~ (v1_xboole_0 @ (u1_struct_0 @ X1))
% 0.67/0.88          | ~ (l1_struct_0 @ X1)
% 0.67/0.88          | (v2_struct_0 @ X1))),
% 0.67/0.88      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.67/0.88  thf('311', plain,
% 0.67/0.88      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.67/0.88         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)) & 
% 0.67/0.88             ((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.67/0.88               (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.67/0.88      inference('sup-', [status(thm)], ['309', '310'])).
% 0.67/0.88  thf('312', plain, ((l1_struct_0 @ sk_A)),
% 0.67/0.88      inference('sup-', [status(thm)], ['259', '260'])).
% 0.67/0.88  thf('313', plain,
% 0.67/0.88      (((v2_struct_0 @ sk_A))
% 0.67/0.88         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)) & 
% 0.67/0.88             ((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.67/0.88               (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.67/0.88      inference('demod', [status(thm)], ['311', '312'])).
% 0.67/0.88  thf('314', plain, (~ (v2_struct_0 @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('315', plain,
% 0.67/0.88      (~
% 0.67/0.88       ((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.67/0.88         (k8_tmap_1 @ sk_A @ sk_B))) | 
% 0.67/0.88       ((v1_tsep_1 @ sk_B @ sk_A))),
% 0.67/0.88      inference('sup-', [status(thm)], ['313', '314'])).
% 0.67/0.88  thf('316', plain, ($false),
% 0.67/0.88      inference('sat_resolution*', [status(thm)],
% 0.67/0.88                ['1', '4', '14', '73', '86', '264', '266', '315'])).
% 0.67/0.88  
% 0.67/0.88  % SZS output end Refutation
% 0.67/0.88  
% 0.67/0.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
