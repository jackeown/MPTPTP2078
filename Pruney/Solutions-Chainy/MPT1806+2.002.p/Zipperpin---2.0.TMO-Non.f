%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.q2uCFwkiwd

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:02 EST 2020

% Result     : Timeout 59.50s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :  423 (39940 expanded)
%              Number of leaves         :   43 (11497 expanded)
%              Depth                    :   50
%              Number of atoms          : 4641 (1033842 expanded)
%              Number of equality atoms :  145 (6480 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k9_tmap_1_type,type,(
    k9_tmap_1: $i > $i > $i )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k8_tmap_1_type,type,(
    k8_tmap_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(k7_tmap_1_type,type,(
    k7_tmap_1: $i > $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

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

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_pre_topc @ X33 @ X34 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X33 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('3',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('6',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X28 @ X27 ) )
        = ( u1_struct_0 @ X28 ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('11',plain,(
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

thf('12',plain,(
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
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
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

thf('16',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('17',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ( v2_pre_topc @ ( k8_tmap_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('25',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('33',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['13','14','22','30','38','39','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8','9','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['44','45'])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('47',plain,(
    ! [X35: $i] :
      ( ( m1_pre_topc @ X35 @ X35 )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('48',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_pre_topc @ X33 @ X34 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X33 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['46','50'])).

thf('52',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('53',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('54',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf(dt_k7_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) )
        & ( v1_funct_2 @ ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) )
        & ( m1_subset_1 @ ( k7_tmap_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) )).

thf('55',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( m1_subset_1 @ ( k7_tmap_1 @ X21 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X21 @ X22 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('56',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf(d10_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k7_tmap_1 @ A @ B )
            = ( k6_partfun1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('58',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( ( k7_tmap_1 @ X9 @ X8 )
        = ( k6_partfun1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_tmap_1])).

thf('59',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X35: $i] :
      ( ( m1_pre_topc @ X35 @ X35 )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('66',plain,(
    ! [X35: $i] :
      ( ( m1_pre_topc @ X35 @ X35 )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('67',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X35: $i] :
      ( ( m1_pre_topc @ X35 @ X35 )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('71',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ( v2_pre_topc @ ( k8_tmap_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X35: $i] :
      ( ( m1_pre_topc @ X35 @ X35 )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('75',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('79',plain,(
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
    inference(simplify,[status(thm)],['11'])).

thf('80',plain,
    ( ~ ( m1_pre_topc @ sk_A @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ~ ( m1_pre_topc @ sk_A @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    | ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_pre_topc @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['77','83'])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    | ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_pre_topc @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,
    ( ~ ( m1_pre_topc @ sk_A @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    | ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_pre_topc @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['73','88'])).

thf('90',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    | ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_pre_topc @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,
    ( ~ ( m1_pre_topc @ sk_A @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_pre_topc @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['69','93'])).

thf('95',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_pre_topc @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('98',plain,
    ( ~ ( m1_pre_topc @ sk_A @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_pre_topc @ sk_A @ sk_A ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_A )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['65','100'])).

thf('102',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_A )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X35: $i] :
      ( ( m1_pre_topc @ X35 @ X35 )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('109',plain,(
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
    inference(simplify,[status(thm)],['11'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ( ( k8_tmap_1 @ X0 @ X0 )
        = ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ~ ( v2_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ~ ( v1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ~ ( v2_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ~ ( l1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ( ( k8_tmap_1 @ X0 @ X0 )
        = ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ( ( k8_tmap_1 @ X0 @ X0 )
        = ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ~ ( v2_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['107','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ~ ( l1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ( ( k8_tmap_1 @ X0 @ X0 )
        = ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ( ( k8_tmap_1 @ X0 @ X0 )
        = ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['106','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( k8_tmap_1 @ X0 @ X0 ) )
      | ( ( k8_tmap_1 @ X0 @ X0 )
        = ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ( ( k8_tmap_1 @ X0 @ X0 )
        = ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['105','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( ( k8_tmap_1 @ X0 @ X0 )
        = ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k8_tmap_1 @ X0 @ X0 )
        = ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['104','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( ( k8_tmap_1 @ X0 @ X0 )
        = ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('121',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X28 @ X27 ) )
        = ( u1_struct_0 @ X28 ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('122',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['122','123','124'])).

thf('126',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_A ) )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['119','127'])).

thf('129',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_A ) )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['128','129','130'])).

thf('132',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['131','132'])).

thf('134',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['56','64','103','133','134','135'])).

thf('137',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['136','137'])).

thf('139',plain,(
    m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['136','137'])).

thf(reflexivity_r1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ~ ( v1_xboole_0 @ B )
        & ~ ( v1_xboole_0 @ D )
        & ( v1_funct_1 @ E )
        & ( v1_funct_2 @ E @ A @ B )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( v1_funct_2 @ F @ C @ D )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( r1_funct_2 @ A @ B @ C @ D @ E @ E ) ) )).

thf('140',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r1_funct_2 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) )
      | ~ ( v1_funct_2 @ X6 @ X2 @ X3 )
      | ~ ( v1_funct_1 @ X6 )
      | ( v1_xboole_0 @ X5 )
      | ( v1_xboole_0 @ X3 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_funct_2 @ X7 @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r1_funct_2])).

thf('141',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X1 @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ X1 @ X0 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('143',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v1_funct_1 @ ( k7_tmap_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('144',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('146',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( ( k7_tmap_1 @ X9 @ X8 )
        = ( k6_partfun1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_tmap_1])).

thf('147',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['147','148','149'])).

thf('151',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['150','151'])).

thf('153',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ( v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['144','152','153','154'])).

thf('156',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X1 @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ X1 @ X0 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['141','157'])).

thf('159',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('160',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v1_funct_2 @ ( k7_tmap_1 @ X21 @ X22 ) @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('161',plain,
    ( ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('163',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_A )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('164',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_A ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['131','132'])).

thf('165',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,
    ( ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['161','162','163','164','165','166'])).

thf('168',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X1 @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ X1 @ X0 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['158','169'])).

thf('171',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['138','170'])).

thf('172',plain,(
    v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['155','156'])).

thf('173',plain,(
    v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['167','168'])).

thf('174',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['171','172','173'])).

thf('175',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['174'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('177',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X28 @ X27 ) )
        = ( u1_struct_0 @ X28 ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('178',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['178'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('181',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( m1_subset_1 @ ( k7_tmap_1 @ X21 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X21 @ X22 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('182',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k7_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k7_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['182'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['179','183'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k7_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['184'])).

thf('186',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['44','45'])).

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

thf('187',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( m1_subset_1 @ ( sk_D_1 @ X16 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( X16
        = ( k9_tmap_1 @ X15 @ X14 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X15 @ X14 ) ) ) ) )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X15 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d12_tmap_1])).

thf('188',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
      | ( X0
        = ( k9_tmap_1 @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('192',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( X0
        = ( k9_tmap_1 @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['188','189','190','191','192'])).

thf('194',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_D_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['185','193'])).

thf('195',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('198',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('199',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('200',plain,(
    v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['167','168'])).

thf('201',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('202',plain,(
    v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['155','156'])).

thf('203',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['194','195','196','197','198','199','200','201','202'])).

thf('204',plain,
    ( ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['203'])).

thf('205',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['204','205'])).

thf('207',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( ( k7_tmap_1 @ X9 @ X8 )
        = ( k6_partfun1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_tmap_1])).

thf('208',plain,
    ( ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k7_tmap_1 @ sk_A @ ( sk_D_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['206','207'])).

thf('209',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,
    ( ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( k7_tmap_1 @ sk_A @ ( sk_D_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['208','209','210'])).

thf('212',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,
    ( ( ( k7_tmap_1 @ sk_A @ ( sk_D_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['211','212'])).

thf('214',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k7_tmap_1 @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['184'])).

thf('215',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('216',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( ( sk_D_1 @ X16 @ X14 @ X15 )
        = ( u1_struct_0 @ X14 ) )
      | ( X16
        = ( k9_tmap_1 @ X15 @ X14 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X15 @ X14 ) ) ) ) )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X15 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d12_tmap_1])).

thf('217',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
      | ( X0
        = ( k9_tmap_1 @ sk_A @ sk_B ) )
      | ( ( sk_D_1 @ X0 @ sk_B @ sk_A )
        = ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['215','216'])).

thf('218',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('221',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( X0
        = ( k9_tmap_1 @ sk_A @ sk_B ) )
      | ( ( sk_D_1 @ X0 @ sk_B @ sk_A )
        = ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['217','218','219','220','221'])).

thf('223',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( ( sk_D_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) )
    | ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['214','222'])).

thf('224',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('227',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('228',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('229',plain,(
    v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['167','168'])).

thf('230',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('231',plain,(
    v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['155','156'])).

thf('232',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['223','224','225','226','227','228','229','230','231'])).

thf('233',plain,
    ( ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( ( sk_D_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['232'])).

thf('234',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,
    ( ( ( sk_D_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['233','234'])).

thf('236',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ~ ( r1_funct_2 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X15 @ X14 ) ) @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X15 @ ( sk_D_1 @ X16 @ X14 @ X15 ) ) ) @ X16 @ ( k7_tmap_1 @ X15 @ ( sk_D_1 @ X16 @ X14 @ X15 ) ) )
      | ( X16
        = ( k9_tmap_1 @ X15 @ X14 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X15 @ X14 ) ) ) ) )
      | ~ ( v1_funct_2 @ X16 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X15 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d12_tmap_1])).

thf('237',plain,
    ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k7_tmap_1 @ sk_A @ ( sk_D_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['235','236'])).

thf('238',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('239',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('240',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('241',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,(
    v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['155','156'])).

thf('244',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('245',plain,(
    v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['167','168'])).

thf('246',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('247',plain,(
    m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['136','137'])).

thf('248',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,
    ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k7_tmap_1 @ sk_A @ ( sk_D_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['237','238','239','240','241','242','243','244','245','246','247','248'])).

thf('250',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k7_tmap_1 @ sk_A @ ( sk_D_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['249'])).

thf('251',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,
    ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k7_tmap_1 @ sk_A @ ( sk_D_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_A ) ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['250','251'])).

thf('253',plain,
    ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['213','252'])).

thf('254',plain,
    ( ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['253'])).

thf('255',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['175','254'])).

thf('256',plain,
    ( ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('257',plain,
    ( ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['256'])).

thf('258',plain,
    ( ~ ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('259',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(split,[status(esa)],['258'])).

thf('260',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('261',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
   <= ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['258'])).

thf('262',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['260','261'])).

thf('263',plain,(
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

thf('264',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ( v1_funct_1 @ ( k9_tmap_1 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_tmap_1])).

thf('265',plain,
    ( ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['263','264'])).

thf('266',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('267',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('268',plain,
    ( ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['265','266','267'])).

thf('269',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('270',plain,(
    v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['268','269'])).

thf('271',plain,
    ( ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
   <= ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['258'])).

thf('272',plain,(
    v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['270','271'])).

thf('273',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('274',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ( v1_funct_2 @ ( k9_tmap_1 @ X25 @ X26 ) @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_tmap_1])).

thf('275',plain,
    ( ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['273','274'])).

thf('276',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('277',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('278',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('279',plain,
    ( ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['275','276','277','278'])).

thf('280',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('281',plain,(
    v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['279','280'])).

thf('282',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('283',plain,
    ( ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
   <= ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['258'])).

thf('284',plain,
    ( ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['282','283'])).

thf('285',plain,(
    v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['281','284'])).

thf('286',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('287',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ( m1_subset_1 @ ( k9_tmap_1 @ X25 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X25 @ X26 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_tmap_1])).

thf('288',plain,
    ( ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['286','287'])).

thf('289',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('290',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('291',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('292',plain,
    ( ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['288','289','290','291'])).

thf('293',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('294',plain,(
    m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['292','293'])).

thf('295',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('296',plain,
    ( ~ ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
   <= ~ ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(split,[status(esa)],['258'])).

thf('297',plain,
    ( ~ ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ~ ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['295','296'])).

thf('298',plain,(
    m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['294','297'])).

thf('299',plain,
    ( ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('300',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['299'])).

thf('301',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('302',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ~ ( v1_tsep_1 @ X18 @ X19 )
      | ( X20
       != ( u1_struct_0 @ X18 ) )
      | ( v3_pre_topc @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('303',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X18 ) @ X19 )
      | ~ ( v1_tsep_1 @ X18 @ X19 )
      | ~ ( m1_pre_topc @ X18 @ X19 ) ) ),
    inference(simplify,[status(thm)],['302'])).

thf('304',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['301','303'])).

thf('305',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('306',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('307',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['304','305','306'])).

thf('308',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['300','307'])).

thf('309',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('310',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( v3_pre_topc @ X29 @ X30 )
      | ( v5_pre_topc @ ( k7_tmap_1 @ X30 @ X29 ) @ X30 @ ( k6_tmap_1 @ X30 @ X29 ) )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t113_tmap_1])).

thf('311',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['309','310'])).

thf('312',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('313',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('314',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['150','151'])).

thf('315',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('316',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['311','312','313','314','315'])).

thf('317',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('318',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['316','317'])).

thf('319',plain,
    ( ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['308','318'])).

thf('320',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) )
      = ( k9_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['175','254'])).

thf('321',plain,
    ( ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['258'])).

thf('322',plain,
    ( ( ~ ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['320','321'])).

thf('323',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      & ( v1_tsep_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['319','322'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('324',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('325',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      & ( v1_tsep_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['323','324'])).

thf('326',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('327',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('328',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['326','327'])).

thf('329',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      & ( v1_tsep_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['325','328'])).

thf('330',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('331',plain,
    ( ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['329','330'])).

thf('332',plain,
    ( ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['256'])).

thf('333',plain,(
    v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['259','262','272','285','298','331','332'])).

thf('334',plain,(
    v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['257','333'])).

thf('335',plain,
    ( ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['255','334'])).

thf('336',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['150','151'])).

thf('337',plain,(
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

thf('338',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ~ ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['336','337'])).

thf('339',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('340',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('341',plain,(
    m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['136','137'])).

thf('342',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('343',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('344',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['150','151'])).

thf('345',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('346',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['150','151'])).

thf('347',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('348',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('349',plain,(
    v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['167','168'])).

thf('350',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['150','151'])).

thf('351',plain,(
    v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['155','156'])).

thf('352',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('353',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ~ ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['338','339','340','341','342','343','344','345','346','347','348','349','350','351','352'])).

thf('354',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('355',plain,
    ( ~ ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['353','354'])).

thf('356',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['335','355'])).

thf('357',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('358',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( ( sk_C @ X18 @ X19 )
        = ( u1_struct_0 @ X18 ) )
      | ( v1_tsep_1 @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('359',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['357','358'])).

thf('360',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('361',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['359','360'])).

thf('362',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['258'])).

thf('363',plain,
    ( ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['361','362'])).

thf('364',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ~ ( v3_pre_topc @ ( sk_C @ X18 @ X19 ) @ X19 )
      | ( v1_tsep_1 @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('365',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['363','364'])).

thf('366',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('367',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('368',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['365','366','367'])).

thf('369',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['258'])).

thf('370',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['368','369'])).

thf('371',plain,(
    ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['259','262','272','285','298','331'])).

thf('372',plain,(
    ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['370','371'])).

thf('373',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['356','372'])).

thf('374',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('375',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['373','374'])).

thf('376',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['326','327'])).

thf('377',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['375','376'])).

thf('378',plain,(
    $false ),
    inference(demod,[status(thm)],['0','377'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.q2uCFwkiwd
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:16:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 59.50/59.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 59.50/59.72  % Solved by: fo/fo7.sh
% 59.50/59.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 59.50/59.72  % done 11140 iterations in 59.257s
% 59.50/59.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 59.50/59.72  % SZS output start Refutation
% 59.50/59.72  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 59.50/59.72  thf(k9_tmap_1_type, type, k9_tmap_1: $i > $i > $i).
% 59.50/59.72  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 59.50/59.72  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 59.50/59.72  thf(sk_A_type, type, sk_A: $i).
% 59.50/59.72  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 59.50/59.72  thf(k8_tmap_1_type, type, k8_tmap_1: $i > $i > $i).
% 59.50/59.72  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 59.50/59.72  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 59.50/59.72  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 59.50/59.72  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 59.50/59.72  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 59.50/59.72  thf(k7_tmap_1_type, type, k7_tmap_1: $i > $i > $i).
% 59.50/59.72  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 59.50/59.72  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 59.50/59.72  thf(sk_B_type, type, sk_B: $i).
% 59.50/59.72  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 59.50/59.72  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 59.50/59.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 59.50/59.72  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 59.50/59.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 59.50/59.72  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 59.50/59.72  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 59.50/59.72  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 59.50/59.72  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 59.50/59.72  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 59.50/59.72  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 59.50/59.72  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 59.50/59.72  thf(t122_tmap_1, conjecture,
% 59.50/59.72    (![A:$i]:
% 59.50/59.72     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 59.50/59.72       ( ![B:$i]:
% 59.50/59.72         ( ( m1_pre_topc @ B @ A ) =>
% 59.50/59.72           ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 59.50/59.72             ( ( v1_funct_1 @ ( k9_tmap_1 @ A @ B ) ) & 
% 59.50/59.72               ( v1_funct_2 @
% 59.50/59.72                 ( k9_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 59.50/59.72                 ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 59.50/59.72               ( v5_pre_topc @
% 59.50/59.72                 ( k9_tmap_1 @ A @ B ) @ A @ ( k8_tmap_1 @ A @ B ) ) & 
% 59.50/59.72               ( m1_subset_1 @
% 59.50/59.72                 ( k9_tmap_1 @ A @ B ) @ 
% 59.50/59.72                 ( k1_zfmisc_1 @
% 59.50/59.72                   ( k2_zfmisc_1 @
% 59.50/59.72                     ( u1_struct_0 @ A ) @ 
% 59.50/59.72                     ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) ))).
% 59.50/59.72  thf(zf_stmt_0, negated_conjecture,
% 59.50/59.72    (~( ![A:$i]:
% 59.50/59.72        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 59.50/59.72            ( l1_pre_topc @ A ) ) =>
% 59.50/59.72          ( ![B:$i]:
% 59.50/59.72            ( ( m1_pre_topc @ B @ A ) =>
% 59.50/59.72              ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 59.50/59.72                ( ( v1_funct_1 @ ( k9_tmap_1 @ A @ B ) ) & 
% 59.50/59.72                  ( v1_funct_2 @
% 59.50/59.72                    ( k9_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 59.50/59.72                    ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 59.50/59.72                  ( v5_pre_topc @
% 59.50/59.72                    ( k9_tmap_1 @ A @ B ) @ A @ ( k8_tmap_1 @ A @ B ) ) & 
% 59.50/59.72                  ( m1_subset_1 @
% 59.50/59.72                    ( k9_tmap_1 @ A @ B ) @ 
% 59.50/59.72                    ( k1_zfmisc_1 @
% 59.50/59.72                      ( k2_zfmisc_1 @
% 59.50/59.72                        ( u1_struct_0 @ A ) @ 
% 59.50/59.72                        ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) ) )),
% 59.50/59.72    inference('cnf.neg', [status(esa)], [t122_tmap_1])).
% 59.50/59.72  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('1', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf(t1_tsep_1, axiom,
% 59.50/59.72    (![A:$i]:
% 59.50/59.72     ( ( l1_pre_topc @ A ) =>
% 59.50/59.72       ( ![B:$i]:
% 59.50/59.72         ( ( m1_pre_topc @ B @ A ) =>
% 59.50/59.72           ( m1_subset_1 @
% 59.50/59.72             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 59.50/59.72  thf('2', plain,
% 59.50/59.72      (![X33 : $i, X34 : $i]:
% 59.50/59.72         (~ (m1_pre_topc @ X33 @ X34)
% 59.50/59.72          | (m1_subset_1 @ (u1_struct_0 @ X33) @ 
% 59.50/59.72             (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 59.50/59.72          | ~ (l1_pre_topc @ X34))),
% 59.50/59.72      inference('cnf', [status(esa)], [t1_tsep_1])).
% 59.50/59.72  thf('3', plain,
% 59.50/59.72      ((~ (l1_pre_topc @ sk_A)
% 59.50/59.72        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 59.50/59.72           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 59.50/59.72      inference('sup-', [status(thm)], ['1', '2'])).
% 59.50/59.72  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('5', plain,
% 59.50/59.72      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 59.50/59.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 59.50/59.72      inference('demod', [status(thm)], ['3', '4'])).
% 59.50/59.72  thf(t104_tmap_1, axiom,
% 59.50/59.72    (![A:$i]:
% 59.50/59.72     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 59.50/59.72       ( ![B:$i]:
% 59.50/59.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 59.50/59.72           ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 59.50/59.72             ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 59.50/59.72  thf('6', plain,
% 59.50/59.72      (![X27 : $i, X28 : $i]:
% 59.50/59.72         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 59.50/59.72          | ((u1_struct_0 @ (k6_tmap_1 @ X28 @ X27)) = (u1_struct_0 @ X28))
% 59.50/59.72          | ~ (l1_pre_topc @ X28)
% 59.50/59.72          | ~ (v2_pre_topc @ X28)
% 59.50/59.72          | (v2_struct_0 @ X28))),
% 59.50/59.72      inference('cnf', [status(esa)], [t104_tmap_1])).
% 59.50/59.72  thf('7', plain,
% 59.50/59.72      (((v2_struct_0 @ sk_A)
% 59.50/59.72        | ~ (v2_pre_topc @ sk_A)
% 59.50/59.72        | ~ (l1_pre_topc @ sk_A)
% 59.50/59.72        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 59.50/59.72            = (u1_struct_0 @ sk_A)))),
% 59.50/59.72      inference('sup-', [status(thm)], ['5', '6'])).
% 59.50/59.72  thf('8', plain, ((v2_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('10', plain,
% 59.50/59.72      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 59.50/59.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 59.50/59.72      inference('demod', [status(thm)], ['3', '4'])).
% 59.50/59.72  thf(d11_tmap_1, axiom,
% 59.50/59.72    (![A:$i]:
% 59.50/59.72     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 59.50/59.72       ( ![B:$i]:
% 59.50/59.72         ( ( m1_pre_topc @ B @ A ) =>
% 59.50/59.72           ( ![C:$i]:
% 59.50/59.72             ( ( ( v1_pre_topc @ C ) & ( v2_pre_topc @ C ) & 
% 59.50/59.72                 ( l1_pre_topc @ C ) ) =>
% 59.50/59.72               ( ( ( C ) = ( k8_tmap_1 @ A @ B ) ) <=>
% 59.50/59.72                 ( ![D:$i]:
% 59.50/59.72                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 59.50/59.72                     ( ( ( D ) = ( u1_struct_0 @ B ) ) =>
% 59.50/59.72                       ( ( C ) = ( k6_tmap_1 @ A @ D ) ) ) ) ) ) ) ) ) ) ))).
% 59.50/59.72  thf('11', plain,
% 59.50/59.72      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 59.50/59.72         (~ (m1_pre_topc @ X10 @ X11)
% 59.50/59.72          | ((X12) != (k8_tmap_1 @ X11 @ X10))
% 59.50/59.72          | ((X13) != (u1_struct_0 @ X10))
% 59.50/59.72          | ((X12) = (k6_tmap_1 @ X11 @ X13))
% 59.50/59.72          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 59.50/59.72          | ~ (l1_pre_topc @ X12)
% 59.50/59.72          | ~ (v2_pre_topc @ X12)
% 59.50/59.72          | ~ (v1_pre_topc @ X12)
% 59.50/59.72          | ~ (l1_pre_topc @ X11)
% 59.50/59.72          | ~ (v2_pre_topc @ X11)
% 59.50/59.72          | (v2_struct_0 @ X11))),
% 59.50/59.72      inference('cnf', [status(esa)], [d11_tmap_1])).
% 59.50/59.72  thf('12', plain,
% 59.50/59.72      (![X10 : $i, X11 : $i]:
% 59.50/59.72         ((v2_struct_0 @ X11)
% 59.50/59.72          | ~ (v2_pre_topc @ X11)
% 59.50/59.72          | ~ (l1_pre_topc @ X11)
% 59.50/59.72          | ~ (v1_pre_topc @ (k8_tmap_1 @ X11 @ X10))
% 59.50/59.72          | ~ (v2_pre_topc @ (k8_tmap_1 @ X11 @ X10))
% 59.50/59.72          | ~ (l1_pre_topc @ (k8_tmap_1 @ X11 @ X10))
% 59.50/59.72          | ~ (m1_subset_1 @ (u1_struct_0 @ X10) @ 
% 59.50/59.72               (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 59.50/59.72          | ((k8_tmap_1 @ X11 @ X10) = (k6_tmap_1 @ X11 @ (u1_struct_0 @ X10)))
% 59.50/59.72          | ~ (m1_pre_topc @ X10 @ X11))),
% 59.50/59.72      inference('simplify', [status(thm)], ['11'])).
% 59.50/59.72  thf('13', plain,
% 59.50/59.72      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 59.50/59.72        | ((k8_tmap_1 @ sk_A @ sk_B)
% 59.50/59.72            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 59.50/59.72        | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 59.50/59.72        | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 59.50/59.72        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 59.50/59.72        | ~ (l1_pre_topc @ sk_A)
% 59.50/59.72        | ~ (v2_pre_topc @ sk_A)
% 59.50/59.72        | (v2_struct_0 @ sk_A))),
% 59.50/59.72      inference('sup-', [status(thm)], ['10', '12'])).
% 59.50/59.72  thf('14', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('15', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf(dt_k8_tmap_1, axiom,
% 59.50/59.72    (![A:$i,B:$i]:
% 59.50/59.72     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 59.50/59.72         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 59.50/59.72       ( ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 59.50/59.72         ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 59.50/59.72         ( l1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ))).
% 59.50/59.72  thf('16', plain,
% 59.50/59.72      (![X23 : $i, X24 : $i]:
% 59.50/59.72         (~ (l1_pre_topc @ X23)
% 59.50/59.72          | ~ (v2_pre_topc @ X23)
% 59.50/59.72          | (v2_struct_0 @ X23)
% 59.50/59.72          | ~ (m1_pre_topc @ X24 @ X23)
% 59.50/59.72          | (l1_pre_topc @ (k8_tmap_1 @ X23 @ X24)))),
% 59.50/59.72      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 59.50/59.72  thf('17', plain,
% 59.50/59.72      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 59.50/59.72        | (v2_struct_0 @ sk_A)
% 59.50/59.72        | ~ (v2_pre_topc @ sk_A)
% 59.50/59.72        | ~ (l1_pre_topc @ sk_A))),
% 59.50/59.72      inference('sup-', [status(thm)], ['15', '16'])).
% 59.50/59.72  thf('18', plain, ((v2_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('20', plain,
% 59.50/59.72      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 59.50/59.72      inference('demod', [status(thm)], ['17', '18', '19'])).
% 59.50/59.72  thf('21', plain, (~ (v2_struct_0 @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('22', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 59.50/59.72      inference('clc', [status(thm)], ['20', '21'])).
% 59.50/59.72  thf('23', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('24', plain,
% 59.50/59.72      (![X23 : $i, X24 : $i]:
% 59.50/59.72         (~ (l1_pre_topc @ X23)
% 59.50/59.72          | ~ (v2_pre_topc @ X23)
% 59.50/59.72          | (v2_struct_0 @ X23)
% 59.50/59.72          | ~ (m1_pre_topc @ X24 @ X23)
% 59.50/59.72          | (v2_pre_topc @ (k8_tmap_1 @ X23 @ X24)))),
% 59.50/59.72      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 59.50/59.72  thf('25', plain,
% 59.50/59.72      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 59.50/59.72        | (v2_struct_0 @ sk_A)
% 59.50/59.72        | ~ (v2_pre_topc @ sk_A)
% 59.50/59.72        | ~ (l1_pre_topc @ sk_A))),
% 59.50/59.72      inference('sup-', [status(thm)], ['23', '24'])).
% 59.50/59.72  thf('26', plain, ((v2_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('28', plain,
% 59.50/59.72      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 59.50/59.72      inference('demod', [status(thm)], ['25', '26', '27'])).
% 59.50/59.72  thf('29', plain, (~ (v2_struct_0 @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('30', plain, ((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 59.50/59.72      inference('clc', [status(thm)], ['28', '29'])).
% 59.50/59.72  thf('31', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('32', plain,
% 59.50/59.72      (![X23 : $i, X24 : $i]:
% 59.50/59.72         (~ (l1_pre_topc @ X23)
% 59.50/59.72          | ~ (v2_pre_topc @ X23)
% 59.50/59.72          | (v2_struct_0 @ X23)
% 59.50/59.72          | ~ (m1_pre_topc @ X24 @ X23)
% 59.50/59.72          | (v1_pre_topc @ (k8_tmap_1 @ X23 @ X24)))),
% 59.50/59.72      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 59.50/59.72  thf('33', plain,
% 59.50/59.72      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 59.50/59.72        | (v2_struct_0 @ sk_A)
% 59.50/59.72        | ~ (v2_pre_topc @ sk_A)
% 59.50/59.72        | ~ (l1_pre_topc @ sk_A))),
% 59.50/59.72      inference('sup-', [status(thm)], ['31', '32'])).
% 59.50/59.72  thf('34', plain, ((v2_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('36', plain,
% 59.50/59.72      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 59.50/59.72      inference('demod', [status(thm)], ['33', '34', '35'])).
% 59.50/59.72  thf('37', plain, (~ (v2_struct_0 @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('38', plain, ((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 59.50/59.72      inference('clc', [status(thm)], ['36', '37'])).
% 59.50/59.72  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('40', plain, ((v2_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('41', plain,
% 59.50/59.72      ((((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 59.50/59.72        | (v2_struct_0 @ sk_A))),
% 59.50/59.72      inference('demod', [status(thm)],
% 59.50/59.72                ['13', '14', '22', '30', '38', '39', '40'])).
% 59.50/59.72  thf('42', plain, (~ (v2_struct_0 @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('43', plain,
% 59.50/59.72      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 59.50/59.72      inference('clc', [status(thm)], ['41', '42'])).
% 59.50/59.72  thf('44', plain,
% 59.50/59.72      (((v2_struct_0 @ sk_A)
% 59.50/59.72        | ((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))),
% 59.50/59.72      inference('demod', [status(thm)], ['7', '8', '9', '43'])).
% 59.50/59.72  thf('45', plain, (~ (v2_struct_0 @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('46', plain,
% 59.50/59.72      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 59.50/59.72      inference('clc', [status(thm)], ['44', '45'])).
% 59.50/59.72  thf(t2_tsep_1, axiom,
% 59.50/59.72    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 59.50/59.72  thf('47', plain,
% 59.50/59.72      (![X35 : $i]: ((m1_pre_topc @ X35 @ X35) | ~ (l1_pre_topc @ X35))),
% 59.50/59.72      inference('cnf', [status(esa)], [t2_tsep_1])).
% 59.50/59.72  thf('48', plain,
% 59.50/59.72      (![X33 : $i, X34 : $i]:
% 59.50/59.72         (~ (m1_pre_topc @ X33 @ X34)
% 59.50/59.72          | (m1_subset_1 @ (u1_struct_0 @ X33) @ 
% 59.50/59.72             (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 59.50/59.72          | ~ (l1_pre_topc @ X34))),
% 59.50/59.72      inference('cnf', [status(esa)], [t1_tsep_1])).
% 59.50/59.72  thf('49', plain,
% 59.50/59.72      (![X0 : $i]:
% 59.50/59.72         (~ (l1_pre_topc @ X0)
% 59.50/59.72          | ~ (l1_pre_topc @ X0)
% 59.50/59.72          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 59.50/59.72             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 59.50/59.72      inference('sup-', [status(thm)], ['47', '48'])).
% 59.50/59.72  thf('50', plain,
% 59.50/59.72      (![X0 : $i]:
% 59.50/59.72         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 59.50/59.72           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 59.50/59.72          | ~ (l1_pre_topc @ X0))),
% 59.50/59.72      inference('simplify', [status(thm)], ['49'])).
% 59.50/59.72  thf('51', plain,
% 59.50/59.72      (((m1_subset_1 @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) @ 
% 59.50/59.72         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 59.50/59.72        | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)))),
% 59.50/59.72      inference('sup+', [status(thm)], ['46', '50'])).
% 59.50/59.72  thf('52', plain,
% 59.50/59.72      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 59.50/59.72      inference('clc', [status(thm)], ['44', '45'])).
% 59.50/59.72  thf('53', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 59.50/59.72      inference('clc', [status(thm)], ['20', '21'])).
% 59.50/59.72  thf('54', plain,
% 59.50/59.72      ((m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 59.50/59.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 59.50/59.72      inference('demod', [status(thm)], ['51', '52', '53'])).
% 59.50/59.72  thf(dt_k7_tmap_1, axiom,
% 59.50/59.72    (![A:$i,B:$i]:
% 59.50/59.72     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 59.50/59.72         ( l1_pre_topc @ A ) & 
% 59.50/59.72         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 59.50/59.72       ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) ) & 
% 59.50/59.72         ( v1_funct_2 @
% 59.50/59.72           ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 59.50/59.72           ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 59.50/59.72         ( m1_subset_1 @
% 59.50/59.72           ( k7_tmap_1 @ A @ B ) @ 
% 59.50/59.72           ( k1_zfmisc_1 @
% 59.50/59.72             ( k2_zfmisc_1 @
% 59.50/59.72               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ))).
% 59.50/59.72  thf('55', plain,
% 59.50/59.72      (![X21 : $i, X22 : $i]:
% 59.50/59.72         (~ (l1_pre_topc @ X21)
% 59.50/59.72          | ~ (v2_pre_topc @ X21)
% 59.50/59.72          | (v2_struct_0 @ X21)
% 59.50/59.72          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 59.50/59.72          | (m1_subset_1 @ (k7_tmap_1 @ X21 @ X22) @ 
% 59.50/59.72             (k1_zfmisc_1 @ 
% 59.50/59.72              (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ 
% 59.50/59.72               (u1_struct_0 @ (k6_tmap_1 @ X21 @ X22))))))),
% 59.50/59.72      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 59.50/59.72  thf('56', plain,
% 59.50/59.72      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)) @ 
% 59.50/59.72         (k1_zfmisc_1 @ 
% 59.50/59.72          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 59.50/59.72           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))))))
% 59.50/59.72        | (v2_struct_0 @ sk_A)
% 59.50/59.72        | ~ (v2_pre_topc @ sk_A)
% 59.50/59.72        | ~ (l1_pre_topc @ sk_A))),
% 59.50/59.72      inference('sup-', [status(thm)], ['54', '55'])).
% 59.50/59.72  thf('57', plain,
% 59.50/59.72      ((m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 59.50/59.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 59.50/59.72      inference('demod', [status(thm)], ['51', '52', '53'])).
% 59.50/59.72  thf(d10_tmap_1, axiom,
% 59.50/59.72    (![A:$i]:
% 59.50/59.72     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 59.50/59.72       ( ![B:$i]:
% 59.50/59.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 59.50/59.72           ( ( k7_tmap_1 @ A @ B ) = ( k6_partfun1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 59.50/59.72  thf('58', plain,
% 59.50/59.72      (![X8 : $i, X9 : $i]:
% 59.50/59.72         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 59.50/59.72          | ((k7_tmap_1 @ X9 @ X8) = (k6_partfun1 @ (u1_struct_0 @ X9)))
% 59.50/59.72          | ~ (l1_pre_topc @ X9)
% 59.50/59.72          | ~ (v2_pre_topc @ X9)
% 59.50/59.72          | (v2_struct_0 @ X9))),
% 59.50/59.72      inference('cnf', [status(esa)], [d10_tmap_1])).
% 59.50/59.72  thf('59', plain,
% 59.50/59.72      (((v2_struct_0 @ sk_A)
% 59.50/59.72        | ~ (v2_pre_topc @ sk_A)
% 59.50/59.72        | ~ (l1_pre_topc @ sk_A)
% 59.50/59.72        | ((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))
% 59.50/59.72            = (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 59.50/59.72      inference('sup-', [status(thm)], ['57', '58'])).
% 59.50/59.72  thf('60', plain, ((v2_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('62', plain,
% 59.50/59.72      (((v2_struct_0 @ sk_A)
% 59.50/59.72        | ((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))
% 59.50/59.72            = (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 59.50/59.72      inference('demod', [status(thm)], ['59', '60', '61'])).
% 59.50/59.72  thf('63', plain, (~ (v2_struct_0 @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('64', plain,
% 59.50/59.72      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))
% 59.50/59.72         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 59.50/59.72      inference('clc', [status(thm)], ['62', '63'])).
% 59.50/59.72  thf('65', plain,
% 59.50/59.72      (![X35 : $i]: ((m1_pre_topc @ X35 @ X35) | ~ (l1_pre_topc @ X35))),
% 59.50/59.72      inference('cnf', [status(esa)], [t2_tsep_1])).
% 59.50/59.72  thf('66', plain,
% 59.50/59.72      (![X35 : $i]: ((m1_pre_topc @ X35 @ X35) | ~ (l1_pre_topc @ X35))),
% 59.50/59.72      inference('cnf', [status(esa)], [t2_tsep_1])).
% 59.50/59.72  thf('67', plain,
% 59.50/59.72      (![X23 : $i, X24 : $i]:
% 59.50/59.72         (~ (l1_pre_topc @ X23)
% 59.50/59.72          | ~ (v2_pre_topc @ X23)
% 59.50/59.72          | (v2_struct_0 @ X23)
% 59.50/59.72          | ~ (m1_pre_topc @ X24 @ X23)
% 59.50/59.72          | (v1_pre_topc @ (k8_tmap_1 @ X23 @ X24)))),
% 59.50/59.72      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 59.50/59.72  thf('68', plain,
% 59.50/59.72      (![X0 : $i]:
% 59.50/59.72         (~ (l1_pre_topc @ X0)
% 59.50/59.72          | (v1_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 59.50/59.72          | (v2_struct_0 @ X0)
% 59.50/59.72          | ~ (v2_pre_topc @ X0)
% 59.50/59.72          | ~ (l1_pre_topc @ X0))),
% 59.50/59.72      inference('sup-', [status(thm)], ['66', '67'])).
% 59.50/59.72  thf('69', plain,
% 59.50/59.72      (![X0 : $i]:
% 59.50/59.72         (~ (v2_pre_topc @ X0)
% 59.50/59.72          | (v2_struct_0 @ X0)
% 59.50/59.72          | (v1_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 59.50/59.72          | ~ (l1_pre_topc @ X0))),
% 59.50/59.72      inference('simplify', [status(thm)], ['68'])).
% 59.50/59.72  thf('70', plain,
% 59.50/59.72      (![X35 : $i]: ((m1_pre_topc @ X35 @ X35) | ~ (l1_pre_topc @ X35))),
% 59.50/59.72      inference('cnf', [status(esa)], [t2_tsep_1])).
% 59.50/59.72  thf('71', plain,
% 59.50/59.72      (![X23 : $i, X24 : $i]:
% 59.50/59.72         (~ (l1_pre_topc @ X23)
% 59.50/59.72          | ~ (v2_pre_topc @ X23)
% 59.50/59.72          | (v2_struct_0 @ X23)
% 59.50/59.72          | ~ (m1_pre_topc @ X24 @ X23)
% 59.50/59.72          | (v2_pre_topc @ (k8_tmap_1 @ X23 @ X24)))),
% 59.50/59.72      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 59.50/59.72  thf('72', plain,
% 59.50/59.72      (![X0 : $i]:
% 59.50/59.72         (~ (l1_pre_topc @ X0)
% 59.50/59.72          | (v2_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 59.50/59.72          | (v2_struct_0 @ X0)
% 59.50/59.72          | ~ (v2_pre_topc @ X0)
% 59.50/59.72          | ~ (l1_pre_topc @ X0))),
% 59.50/59.72      inference('sup-', [status(thm)], ['70', '71'])).
% 59.50/59.72  thf('73', plain,
% 59.50/59.72      (![X0 : $i]:
% 59.50/59.72         (~ (v2_pre_topc @ X0)
% 59.50/59.72          | (v2_struct_0 @ X0)
% 59.50/59.72          | (v2_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 59.50/59.72          | ~ (l1_pre_topc @ X0))),
% 59.50/59.72      inference('simplify', [status(thm)], ['72'])).
% 59.50/59.72  thf('74', plain,
% 59.50/59.72      (![X35 : $i]: ((m1_pre_topc @ X35 @ X35) | ~ (l1_pre_topc @ X35))),
% 59.50/59.72      inference('cnf', [status(esa)], [t2_tsep_1])).
% 59.50/59.72  thf('75', plain,
% 59.50/59.72      (![X23 : $i, X24 : $i]:
% 59.50/59.72         (~ (l1_pre_topc @ X23)
% 59.50/59.72          | ~ (v2_pre_topc @ X23)
% 59.50/59.72          | (v2_struct_0 @ X23)
% 59.50/59.72          | ~ (m1_pre_topc @ X24 @ X23)
% 59.50/59.72          | (l1_pre_topc @ (k8_tmap_1 @ X23 @ X24)))),
% 59.50/59.72      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 59.50/59.72  thf('76', plain,
% 59.50/59.72      (![X0 : $i]:
% 59.50/59.72         (~ (l1_pre_topc @ X0)
% 59.50/59.72          | (l1_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 59.50/59.72          | (v2_struct_0 @ X0)
% 59.50/59.72          | ~ (v2_pre_topc @ X0)
% 59.50/59.72          | ~ (l1_pre_topc @ X0))),
% 59.50/59.72      inference('sup-', [status(thm)], ['74', '75'])).
% 59.50/59.72  thf('77', plain,
% 59.50/59.72      (![X0 : $i]:
% 59.50/59.72         (~ (v2_pre_topc @ X0)
% 59.50/59.72          | (v2_struct_0 @ X0)
% 59.50/59.72          | (l1_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 59.50/59.72          | ~ (l1_pre_topc @ X0))),
% 59.50/59.72      inference('simplify', [status(thm)], ['76'])).
% 59.50/59.72  thf('78', plain,
% 59.50/59.72      ((m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 59.50/59.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 59.50/59.72      inference('demod', [status(thm)], ['51', '52', '53'])).
% 59.50/59.72  thf('79', plain,
% 59.50/59.72      (![X10 : $i, X11 : $i]:
% 59.50/59.72         ((v2_struct_0 @ X11)
% 59.50/59.72          | ~ (v2_pre_topc @ X11)
% 59.50/59.72          | ~ (l1_pre_topc @ X11)
% 59.50/59.72          | ~ (v1_pre_topc @ (k8_tmap_1 @ X11 @ X10))
% 59.50/59.72          | ~ (v2_pre_topc @ (k8_tmap_1 @ X11 @ X10))
% 59.50/59.72          | ~ (l1_pre_topc @ (k8_tmap_1 @ X11 @ X10))
% 59.50/59.72          | ~ (m1_subset_1 @ (u1_struct_0 @ X10) @ 
% 59.50/59.72               (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 59.50/59.72          | ((k8_tmap_1 @ X11 @ X10) = (k6_tmap_1 @ X11 @ (u1_struct_0 @ X10)))
% 59.50/59.72          | ~ (m1_pre_topc @ X10 @ X11))),
% 59.50/59.72      inference('simplify', [status(thm)], ['11'])).
% 59.50/59.72  thf('80', plain,
% 59.50/59.72      ((~ (m1_pre_topc @ sk_A @ sk_A)
% 59.50/59.72        | ((k8_tmap_1 @ sk_A @ sk_A)
% 59.50/59.72            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 59.50/59.72        | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 59.50/59.72        | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 59.50/59.72        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 59.50/59.72        | ~ (l1_pre_topc @ sk_A)
% 59.50/59.72        | ~ (v2_pre_topc @ sk_A)
% 59.50/59.72        | (v2_struct_0 @ sk_A))),
% 59.50/59.72      inference('sup-', [status(thm)], ['78', '79'])).
% 59.50/59.72  thf('81', plain, ((l1_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('82', plain, ((v2_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('83', plain,
% 59.50/59.72      ((~ (m1_pre_topc @ sk_A @ sk_A)
% 59.50/59.72        | ((k8_tmap_1 @ sk_A @ sk_A)
% 59.50/59.72            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 59.50/59.72        | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 59.50/59.72        | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 59.50/59.72        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 59.50/59.72        | (v2_struct_0 @ sk_A))),
% 59.50/59.72      inference('demod', [status(thm)], ['80', '81', '82'])).
% 59.50/59.72  thf('84', plain,
% 59.50/59.72      ((~ (l1_pre_topc @ sk_A)
% 59.50/59.72        | (v2_struct_0 @ sk_A)
% 59.50/59.72        | ~ (v2_pre_topc @ sk_A)
% 59.50/59.72        | (v2_struct_0 @ sk_A)
% 59.50/59.72        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 59.50/59.72        | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 59.50/59.72        | ((k8_tmap_1 @ sk_A @ sk_A)
% 59.50/59.72            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 59.50/59.72        | ~ (m1_pre_topc @ sk_A @ sk_A))),
% 59.50/59.72      inference('sup-', [status(thm)], ['77', '83'])).
% 59.50/59.72  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('86', plain, ((v2_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('87', plain,
% 59.50/59.72      (((v2_struct_0 @ sk_A)
% 59.50/59.72        | (v2_struct_0 @ sk_A)
% 59.50/59.72        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 59.50/59.72        | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 59.50/59.72        | ((k8_tmap_1 @ sk_A @ sk_A)
% 59.50/59.72            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 59.50/59.72        | ~ (m1_pre_topc @ sk_A @ sk_A))),
% 59.50/59.72      inference('demod', [status(thm)], ['84', '85', '86'])).
% 59.50/59.72  thf('88', plain,
% 59.50/59.72      ((~ (m1_pre_topc @ sk_A @ sk_A)
% 59.50/59.72        | ((k8_tmap_1 @ sk_A @ sk_A)
% 59.50/59.72            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 59.50/59.72        | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 59.50/59.72        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 59.50/59.72        | (v2_struct_0 @ sk_A))),
% 59.50/59.72      inference('simplify', [status(thm)], ['87'])).
% 59.50/59.72  thf('89', plain,
% 59.50/59.72      ((~ (l1_pre_topc @ sk_A)
% 59.50/59.72        | (v2_struct_0 @ sk_A)
% 59.50/59.72        | ~ (v2_pre_topc @ sk_A)
% 59.50/59.72        | (v2_struct_0 @ sk_A)
% 59.50/59.72        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 59.50/59.72        | ((k8_tmap_1 @ sk_A @ sk_A)
% 59.50/59.72            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 59.50/59.72        | ~ (m1_pre_topc @ sk_A @ sk_A))),
% 59.50/59.72      inference('sup-', [status(thm)], ['73', '88'])).
% 59.50/59.72  thf('90', plain, ((l1_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('91', plain, ((v2_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('92', plain,
% 59.50/59.72      (((v2_struct_0 @ sk_A)
% 59.50/59.72        | (v2_struct_0 @ sk_A)
% 59.50/59.72        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 59.50/59.72        | ((k8_tmap_1 @ sk_A @ sk_A)
% 59.50/59.72            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 59.50/59.72        | ~ (m1_pre_topc @ sk_A @ sk_A))),
% 59.50/59.72      inference('demod', [status(thm)], ['89', '90', '91'])).
% 59.50/59.72  thf('93', plain,
% 59.50/59.72      ((~ (m1_pre_topc @ sk_A @ sk_A)
% 59.50/59.72        | ((k8_tmap_1 @ sk_A @ sk_A)
% 59.50/59.72            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 59.50/59.72        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_A))
% 59.50/59.72        | (v2_struct_0 @ sk_A))),
% 59.50/59.72      inference('simplify', [status(thm)], ['92'])).
% 59.50/59.72  thf('94', plain,
% 59.50/59.72      ((~ (l1_pre_topc @ sk_A)
% 59.50/59.72        | (v2_struct_0 @ sk_A)
% 59.50/59.72        | ~ (v2_pre_topc @ sk_A)
% 59.50/59.72        | (v2_struct_0 @ sk_A)
% 59.50/59.72        | ((k8_tmap_1 @ sk_A @ sk_A)
% 59.50/59.72            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 59.50/59.72        | ~ (m1_pre_topc @ sk_A @ sk_A))),
% 59.50/59.72      inference('sup-', [status(thm)], ['69', '93'])).
% 59.50/59.72  thf('95', plain, ((l1_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('96', plain, ((v2_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('97', plain,
% 59.50/59.72      (((v2_struct_0 @ sk_A)
% 59.50/59.72        | (v2_struct_0 @ sk_A)
% 59.50/59.72        | ((k8_tmap_1 @ sk_A @ sk_A)
% 59.50/59.72            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 59.50/59.72        | ~ (m1_pre_topc @ sk_A @ sk_A))),
% 59.50/59.72      inference('demod', [status(thm)], ['94', '95', '96'])).
% 59.50/59.72  thf('98', plain,
% 59.50/59.72      ((~ (m1_pre_topc @ sk_A @ sk_A)
% 59.50/59.72        | ((k8_tmap_1 @ sk_A @ sk_A)
% 59.50/59.72            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 59.50/59.72        | (v2_struct_0 @ sk_A))),
% 59.50/59.72      inference('simplify', [status(thm)], ['97'])).
% 59.50/59.72  thf('99', plain, (~ (v2_struct_0 @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('100', plain,
% 59.50/59.72      ((((k8_tmap_1 @ sk_A @ sk_A) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 59.50/59.72        | ~ (m1_pre_topc @ sk_A @ sk_A))),
% 59.50/59.72      inference('clc', [status(thm)], ['98', '99'])).
% 59.50/59.72  thf('101', plain,
% 59.50/59.72      ((~ (l1_pre_topc @ sk_A)
% 59.50/59.72        | ((k8_tmap_1 @ sk_A @ sk_A)
% 59.50/59.72            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))))),
% 59.50/59.72      inference('sup-', [status(thm)], ['65', '100'])).
% 59.50/59.72  thf('102', plain, ((l1_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('103', plain,
% 59.50/59.72      (((k8_tmap_1 @ sk_A @ sk_A) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))),
% 59.50/59.72      inference('demod', [status(thm)], ['101', '102'])).
% 59.50/59.72  thf('104', plain,
% 59.50/59.72      (![X35 : $i]: ((m1_pre_topc @ X35 @ X35) | ~ (l1_pre_topc @ X35))),
% 59.50/59.72      inference('cnf', [status(esa)], [t2_tsep_1])).
% 59.50/59.72  thf('105', plain,
% 59.50/59.72      (![X0 : $i]:
% 59.50/59.72         (~ (v2_pre_topc @ X0)
% 59.50/59.72          | (v2_struct_0 @ X0)
% 59.50/59.72          | (l1_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 59.50/59.72          | ~ (l1_pre_topc @ X0))),
% 59.50/59.72      inference('simplify', [status(thm)], ['76'])).
% 59.50/59.72  thf('106', plain,
% 59.50/59.72      (![X0 : $i]:
% 59.50/59.72         (~ (v2_pre_topc @ X0)
% 59.50/59.72          | (v2_struct_0 @ X0)
% 59.50/59.72          | (v2_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 59.50/59.72          | ~ (l1_pre_topc @ X0))),
% 59.50/59.72      inference('simplify', [status(thm)], ['72'])).
% 59.50/59.72  thf('107', plain,
% 59.50/59.72      (![X0 : $i]:
% 59.50/59.72         (~ (v2_pre_topc @ X0)
% 59.50/59.72          | (v2_struct_0 @ X0)
% 59.50/59.72          | (v1_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 59.50/59.72          | ~ (l1_pre_topc @ X0))),
% 59.50/59.72      inference('simplify', [status(thm)], ['68'])).
% 59.50/59.72  thf('108', plain,
% 59.50/59.72      (![X0 : $i]:
% 59.50/59.72         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 59.50/59.72           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 59.50/59.72          | ~ (l1_pre_topc @ X0))),
% 59.50/59.72      inference('simplify', [status(thm)], ['49'])).
% 59.50/59.72  thf('109', plain,
% 59.50/59.72      (![X10 : $i, X11 : $i]:
% 59.50/59.72         ((v2_struct_0 @ X11)
% 59.50/59.72          | ~ (v2_pre_topc @ X11)
% 59.50/59.72          | ~ (l1_pre_topc @ X11)
% 59.50/59.72          | ~ (v1_pre_topc @ (k8_tmap_1 @ X11 @ X10))
% 59.50/59.72          | ~ (v2_pre_topc @ (k8_tmap_1 @ X11 @ X10))
% 59.50/59.72          | ~ (l1_pre_topc @ (k8_tmap_1 @ X11 @ X10))
% 59.50/59.72          | ~ (m1_subset_1 @ (u1_struct_0 @ X10) @ 
% 59.50/59.72               (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 59.50/59.72          | ((k8_tmap_1 @ X11 @ X10) = (k6_tmap_1 @ X11 @ (u1_struct_0 @ X10)))
% 59.50/59.72          | ~ (m1_pre_topc @ X10 @ X11))),
% 59.50/59.72      inference('simplify', [status(thm)], ['11'])).
% 59.50/59.72  thf('110', plain,
% 59.50/59.72      (![X0 : $i]:
% 59.50/59.72         (~ (l1_pre_topc @ X0)
% 59.50/59.72          | ~ (m1_pre_topc @ X0 @ X0)
% 59.50/59.72          | ((k8_tmap_1 @ X0 @ X0) = (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 59.50/59.72          | ~ (l1_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 59.50/59.72          | ~ (v2_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 59.50/59.72          | ~ (v1_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 59.50/59.72          | ~ (l1_pre_topc @ X0)
% 59.50/59.72          | ~ (v2_pre_topc @ X0)
% 59.50/59.72          | (v2_struct_0 @ X0))),
% 59.50/59.72      inference('sup-', [status(thm)], ['108', '109'])).
% 59.50/59.72  thf('111', plain,
% 59.50/59.72      (![X0 : $i]:
% 59.50/59.72         ((v2_struct_0 @ X0)
% 59.50/59.72          | ~ (v2_pre_topc @ X0)
% 59.50/59.72          | ~ (v1_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 59.50/59.72          | ~ (v2_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 59.50/59.72          | ~ (l1_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 59.50/59.72          | ((k8_tmap_1 @ X0 @ X0) = (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 59.50/59.72          | ~ (m1_pre_topc @ X0 @ X0)
% 59.50/59.72          | ~ (l1_pre_topc @ X0))),
% 59.50/59.72      inference('simplify', [status(thm)], ['110'])).
% 59.50/59.72  thf('112', plain,
% 59.50/59.72      (![X0 : $i]:
% 59.50/59.72         (~ (l1_pre_topc @ X0)
% 59.50/59.72          | (v2_struct_0 @ X0)
% 59.50/59.72          | ~ (v2_pre_topc @ X0)
% 59.50/59.72          | ~ (l1_pre_topc @ X0)
% 59.50/59.72          | ~ (m1_pre_topc @ X0 @ X0)
% 59.50/59.72          | ((k8_tmap_1 @ X0 @ X0) = (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 59.50/59.72          | ~ (l1_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 59.50/59.72          | ~ (v2_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 59.50/59.72          | ~ (v2_pre_topc @ X0)
% 59.50/59.72          | (v2_struct_0 @ X0))),
% 59.50/59.72      inference('sup-', [status(thm)], ['107', '111'])).
% 59.50/59.72  thf('113', plain,
% 59.50/59.72      (![X0 : $i]:
% 59.50/59.72         (~ (v2_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 59.50/59.72          | ~ (l1_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 59.50/59.72          | ((k8_tmap_1 @ X0 @ X0) = (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 59.50/59.72          | ~ (m1_pre_topc @ X0 @ X0)
% 59.50/59.72          | ~ (v2_pre_topc @ X0)
% 59.50/59.72          | (v2_struct_0 @ X0)
% 59.50/59.72          | ~ (l1_pre_topc @ X0))),
% 59.50/59.72      inference('simplify', [status(thm)], ['112'])).
% 59.50/59.72  thf('114', plain,
% 59.50/59.72      (![X0 : $i]:
% 59.50/59.72         (~ (l1_pre_topc @ X0)
% 59.50/59.72          | (v2_struct_0 @ X0)
% 59.50/59.72          | ~ (v2_pre_topc @ X0)
% 59.50/59.72          | ~ (l1_pre_topc @ X0)
% 59.50/59.72          | (v2_struct_0 @ X0)
% 59.50/59.72          | ~ (v2_pre_topc @ X0)
% 59.50/59.72          | ~ (m1_pre_topc @ X0 @ X0)
% 59.50/59.72          | ((k8_tmap_1 @ X0 @ X0) = (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 59.50/59.72          | ~ (l1_pre_topc @ (k8_tmap_1 @ X0 @ X0)))),
% 59.50/59.72      inference('sup-', [status(thm)], ['106', '113'])).
% 59.50/59.72  thf('115', plain,
% 59.50/59.72      (![X0 : $i]:
% 59.50/59.72         (~ (l1_pre_topc @ (k8_tmap_1 @ X0 @ X0))
% 59.50/59.72          | ((k8_tmap_1 @ X0 @ X0) = (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 59.50/59.72          | ~ (m1_pre_topc @ X0 @ X0)
% 59.50/59.72          | ~ (v2_pre_topc @ X0)
% 59.50/59.72          | (v2_struct_0 @ X0)
% 59.50/59.72          | ~ (l1_pre_topc @ X0))),
% 59.50/59.72      inference('simplify', [status(thm)], ['114'])).
% 59.50/59.72  thf('116', plain,
% 59.50/59.72      (![X0 : $i]:
% 59.50/59.72         (~ (l1_pre_topc @ X0)
% 59.50/59.72          | (v2_struct_0 @ X0)
% 59.50/59.72          | ~ (v2_pre_topc @ X0)
% 59.50/59.72          | ~ (l1_pre_topc @ X0)
% 59.50/59.72          | (v2_struct_0 @ X0)
% 59.50/59.72          | ~ (v2_pre_topc @ X0)
% 59.50/59.72          | ~ (m1_pre_topc @ X0 @ X0)
% 59.50/59.72          | ((k8_tmap_1 @ X0 @ X0) = (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0))))),
% 59.50/59.72      inference('sup-', [status(thm)], ['105', '115'])).
% 59.50/59.72  thf('117', plain,
% 59.50/59.72      (![X0 : $i]:
% 59.50/59.72         (((k8_tmap_1 @ X0 @ X0) = (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 59.50/59.72          | ~ (m1_pre_topc @ X0 @ X0)
% 59.50/59.72          | ~ (v2_pre_topc @ X0)
% 59.50/59.72          | (v2_struct_0 @ X0)
% 59.50/59.72          | ~ (l1_pre_topc @ X0))),
% 59.50/59.72      inference('simplify', [status(thm)], ['116'])).
% 59.50/59.72  thf('118', plain,
% 59.50/59.72      (![X0 : $i]:
% 59.50/59.72         (~ (l1_pre_topc @ X0)
% 59.50/59.72          | ~ (l1_pre_topc @ X0)
% 59.50/59.72          | (v2_struct_0 @ X0)
% 59.50/59.72          | ~ (v2_pre_topc @ X0)
% 59.50/59.72          | ((k8_tmap_1 @ X0 @ X0) = (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0))))),
% 59.50/59.72      inference('sup-', [status(thm)], ['104', '117'])).
% 59.50/59.72  thf('119', plain,
% 59.50/59.72      (![X0 : $i]:
% 59.50/59.72         (((k8_tmap_1 @ X0 @ X0) = (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 59.50/59.72          | ~ (v2_pre_topc @ X0)
% 59.50/59.72          | (v2_struct_0 @ X0)
% 59.50/59.72          | ~ (l1_pre_topc @ X0))),
% 59.50/59.72      inference('simplify', [status(thm)], ['118'])).
% 59.50/59.72  thf('120', plain,
% 59.50/59.72      ((m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 59.50/59.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 59.50/59.72      inference('demod', [status(thm)], ['51', '52', '53'])).
% 59.50/59.72  thf('121', plain,
% 59.50/59.72      (![X27 : $i, X28 : $i]:
% 59.50/59.72         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 59.50/59.72          | ((u1_struct_0 @ (k6_tmap_1 @ X28 @ X27)) = (u1_struct_0 @ X28))
% 59.50/59.72          | ~ (l1_pre_topc @ X28)
% 59.50/59.72          | ~ (v2_pre_topc @ X28)
% 59.50/59.72          | (v2_struct_0 @ X28))),
% 59.50/59.72      inference('cnf', [status(esa)], [t104_tmap_1])).
% 59.50/59.72  thf('122', plain,
% 59.50/59.72      (((v2_struct_0 @ sk_A)
% 59.50/59.72        | ~ (v2_pre_topc @ sk_A)
% 59.50/59.72        | ~ (l1_pre_topc @ sk_A)
% 59.50/59.72        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 59.50/59.72            = (u1_struct_0 @ sk_A)))),
% 59.50/59.72      inference('sup-', [status(thm)], ['120', '121'])).
% 59.50/59.72  thf('123', plain, ((v2_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('124', plain, ((l1_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('125', plain,
% 59.50/59.72      (((v2_struct_0 @ sk_A)
% 59.50/59.72        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 59.50/59.72            = (u1_struct_0 @ sk_A)))),
% 59.50/59.72      inference('demod', [status(thm)], ['122', '123', '124'])).
% 59.50/59.72  thf('126', plain, (~ (v2_struct_0 @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('127', plain,
% 59.50/59.72      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 59.50/59.72         = (u1_struct_0 @ sk_A))),
% 59.50/59.72      inference('clc', [status(thm)], ['125', '126'])).
% 59.50/59.72  thf('128', plain,
% 59.50/59.72      ((((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_A)) = (u1_struct_0 @ sk_A))
% 59.50/59.72        | ~ (l1_pre_topc @ sk_A)
% 59.50/59.72        | (v2_struct_0 @ sk_A)
% 59.50/59.72        | ~ (v2_pre_topc @ sk_A))),
% 59.50/59.72      inference('sup+', [status(thm)], ['119', '127'])).
% 59.50/59.72  thf('129', plain, ((l1_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('130', plain, ((v2_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('131', plain,
% 59.50/59.72      ((((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_A)) = (u1_struct_0 @ sk_A))
% 59.50/59.72        | (v2_struct_0 @ sk_A))),
% 59.50/59.72      inference('demod', [status(thm)], ['128', '129', '130'])).
% 59.50/59.72  thf('132', plain, (~ (v2_struct_0 @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('133', plain,
% 59.50/59.72      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_A)) = (u1_struct_0 @ sk_A))),
% 59.50/59.72      inference('clc', [status(thm)], ['131', '132'])).
% 59.50/59.72  thf('134', plain, ((v2_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('135', plain, ((l1_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('136', plain,
% 59.50/59.72      (((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 59.50/59.72         (k1_zfmisc_1 @ 
% 59.50/59.72          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 59.50/59.72        | (v2_struct_0 @ sk_A))),
% 59.50/59.72      inference('demod', [status(thm)],
% 59.50/59.72                ['56', '64', '103', '133', '134', '135'])).
% 59.50/59.72  thf('137', plain, (~ (v2_struct_0 @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('138', plain,
% 59.50/59.72      ((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 59.50/59.72        (k1_zfmisc_1 @ 
% 59.50/59.72         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 59.50/59.72      inference('clc', [status(thm)], ['136', '137'])).
% 59.50/59.72  thf('139', plain,
% 59.50/59.72      ((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 59.50/59.72        (k1_zfmisc_1 @ 
% 59.50/59.72         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 59.50/59.72      inference('clc', [status(thm)], ['136', '137'])).
% 59.50/59.72  thf(reflexivity_r1_funct_2, axiom,
% 59.50/59.72    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 59.50/59.72     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 59.50/59.72         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 59.50/59.72         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 59.50/59.72         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 59.50/59.72         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 59.50/59.72       ( r1_funct_2 @ A @ B @ C @ D @ E @ E ) ))).
% 59.50/59.72  thf('140', plain,
% 59.50/59.72      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 59.50/59.72         ((r1_funct_2 @ X2 @ X3 @ X4 @ X5 @ X6 @ X6)
% 59.50/59.72          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3)))
% 59.50/59.72          | ~ (v1_funct_2 @ X6 @ X2 @ X3)
% 59.50/59.72          | ~ (v1_funct_1 @ X6)
% 59.50/59.72          | (v1_xboole_0 @ X5)
% 59.50/59.72          | (v1_xboole_0 @ X3)
% 59.50/59.72          | ~ (v1_funct_1 @ X7)
% 59.50/59.72          | ~ (v1_funct_2 @ X7 @ X4 @ X5)
% 59.50/59.72          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 59.50/59.72      inference('cnf', [status(esa)], [reflexivity_r1_funct_2])).
% 59.50/59.72  thf('141', plain,
% 59.50/59.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 59.50/59.72         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 59.50/59.72          | ~ (v1_funct_2 @ X2 @ X1 @ X0)
% 59.50/59.72          | ~ (v1_funct_1 @ X2)
% 59.50/59.72          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 59.50/59.72          | (v1_xboole_0 @ X0)
% 59.50/59.72          | ~ (v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 59.50/59.72          | ~ (v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 59.50/59.72               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 59.50/59.72          | (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ X1 @ 
% 59.50/59.72             X0 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 59.50/59.72             (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 59.50/59.72      inference('sup-', [status(thm)], ['139', '140'])).
% 59.50/59.72  thf('142', plain,
% 59.50/59.72      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 59.50/59.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 59.50/59.72      inference('demod', [status(thm)], ['3', '4'])).
% 59.50/59.72  thf('143', plain,
% 59.50/59.72      (![X21 : $i, X22 : $i]:
% 59.50/59.72         (~ (l1_pre_topc @ X21)
% 59.50/59.72          | ~ (v2_pre_topc @ X21)
% 59.50/59.72          | (v2_struct_0 @ X21)
% 59.50/59.72          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 59.50/59.72          | (v1_funct_1 @ (k7_tmap_1 @ X21 @ X22)))),
% 59.50/59.72      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 59.50/59.72  thf('144', plain,
% 59.50/59.72      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 59.50/59.72        | (v2_struct_0 @ sk_A)
% 59.50/59.72        | ~ (v2_pre_topc @ sk_A)
% 59.50/59.72        | ~ (l1_pre_topc @ sk_A))),
% 59.50/59.72      inference('sup-', [status(thm)], ['142', '143'])).
% 59.50/59.72  thf('145', plain,
% 59.50/59.72      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 59.50/59.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 59.50/59.72      inference('demod', [status(thm)], ['3', '4'])).
% 59.50/59.72  thf('146', plain,
% 59.50/59.72      (![X8 : $i, X9 : $i]:
% 59.50/59.72         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 59.50/59.72          | ((k7_tmap_1 @ X9 @ X8) = (k6_partfun1 @ (u1_struct_0 @ X9)))
% 59.50/59.72          | ~ (l1_pre_topc @ X9)
% 59.50/59.72          | ~ (v2_pre_topc @ X9)
% 59.50/59.72          | (v2_struct_0 @ X9))),
% 59.50/59.72      inference('cnf', [status(esa)], [d10_tmap_1])).
% 59.50/59.72  thf('147', plain,
% 59.50/59.72      (((v2_struct_0 @ sk_A)
% 59.50/59.72        | ~ (v2_pre_topc @ sk_A)
% 59.50/59.72        | ~ (l1_pre_topc @ sk_A)
% 59.50/59.72        | ((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 59.50/59.72            = (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 59.50/59.72      inference('sup-', [status(thm)], ['145', '146'])).
% 59.50/59.72  thf('148', plain, ((v2_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('149', plain, ((l1_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('150', plain,
% 59.50/59.72      (((v2_struct_0 @ sk_A)
% 59.50/59.72        | ((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 59.50/59.72            = (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 59.50/59.72      inference('demod', [status(thm)], ['147', '148', '149'])).
% 59.50/59.72  thf('151', plain, (~ (v2_struct_0 @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('152', plain,
% 59.50/59.72      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 59.50/59.72         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 59.50/59.72      inference('clc', [status(thm)], ['150', '151'])).
% 59.50/59.72  thf('153', plain, ((v2_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('154', plain, ((l1_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('155', plain,
% 59.50/59.72      (((v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 59.50/59.72        | (v2_struct_0 @ sk_A))),
% 59.50/59.72      inference('demod', [status(thm)], ['144', '152', '153', '154'])).
% 59.50/59.72  thf('156', plain, (~ (v2_struct_0 @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('157', plain, ((v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 59.50/59.72      inference('clc', [status(thm)], ['155', '156'])).
% 59.50/59.72  thf('158', plain,
% 59.50/59.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 59.50/59.72         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 59.50/59.72          | ~ (v1_funct_2 @ X2 @ X1 @ X0)
% 59.50/59.72          | ~ (v1_funct_1 @ X2)
% 59.50/59.72          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 59.50/59.72          | (v1_xboole_0 @ X0)
% 59.50/59.72          | ~ (v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 59.50/59.72               (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 59.50/59.72          | (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ X1 @ 
% 59.50/59.72             X0 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 59.50/59.72             (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 59.50/59.72      inference('demod', [status(thm)], ['141', '157'])).
% 59.50/59.72  thf('159', plain,
% 59.50/59.72      ((m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 59.50/59.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 59.50/59.72      inference('demod', [status(thm)], ['51', '52', '53'])).
% 59.50/59.72  thf('160', plain,
% 59.50/59.72      (![X21 : $i, X22 : $i]:
% 59.50/59.72         (~ (l1_pre_topc @ X21)
% 59.50/59.72          | ~ (v2_pre_topc @ X21)
% 59.50/59.72          | (v2_struct_0 @ X21)
% 59.50/59.72          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 59.50/59.72          | (v1_funct_2 @ (k7_tmap_1 @ X21 @ X22) @ (u1_struct_0 @ X21) @ 
% 59.50/59.72             (u1_struct_0 @ (k6_tmap_1 @ X21 @ X22))))),
% 59.50/59.72      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 59.50/59.72  thf('161', plain,
% 59.50/59.72      (((v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)) @ 
% 59.50/59.72         (u1_struct_0 @ sk_A) @ 
% 59.50/59.72         (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))))
% 59.50/59.72        | (v2_struct_0 @ sk_A)
% 59.50/59.72        | ~ (v2_pre_topc @ sk_A)
% 59.50/59.72        | ~ (l1_pre_topc @ sk_A))),
% 59.50/59.72      inference('sup-', [status(thm)], ['159', '160'])).
% 59.50/59.72  thf('162', plain,
% 59.50/59.72      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))
% 59.50/59.72         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 59.50/59.72      inference('clc', [status(thm)], ['62', '63'])).
% 59.50/59.72  thf('163', plain,
% 59.50/59.72      (((k8_tmap_1 @ sk_A @ sk_A) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))),
% 59.50/59.72      inference('demod', [status(thm)], ['101', '102'])).
% 59.50/59.72  thf('164', plain,
% 59.50/59.72      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_A)) = (u1_struct_0 @ sk_A))),
% 59.50/59.72      inference('clc', [status(thm)], ['131', '132'])).
% 59.50/59.72  thf('165', plain, ((v2_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('166', plain, ((l1_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('167', plain,
% 59.50/59.72      (((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 59.50/59.72         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 59.50/59.72        | (v2_struct_0 @ sk_A))),
% 59.50/59.72      inference('demod', [status(thm)],
% 59.50/59.72                ['161', '162', '163', '164', '165', '166'])).
% 59.50/59.72  thf('168', plain, (~ (v2_struct_0 @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('169', plain,
% 59.50/59.72      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 59.50/59.72        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 59.50/59.72      inference('clc', [status(thm)], ['167', '168'])).
% 59.50/59.72  thf('170', plain,
% 59.50/59.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 59.50/59.72         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 59.50/59.72          | ~ (v1_funct_2 @ X2 @ X1 @ X0)
% 59.50/59.72          | ~ (v1_funct_1 @ X2)
% 59.50/59.72          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 59.50/59.72          | (v1_xboole_0 @ X0)
% 59.50/59.72          | (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ X1 @ 
% 59.50/59.72             X0 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 59.50/59.72             (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 59.50/59.72      inference('demod', [status(thm)], ['158', '169'])).
% 59.50/59.72  thf('171', plain,
% 59.50/59.72      (((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 59.50/59.72         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 59.50/59.72         (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 59.50/59.72         (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 59.50/59.72        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 59.50/59.72        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 59.50/59.72        | ~ (v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 59.50/59.72        | ~ (v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 59.50/59.72             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))),
% 59.50/59.72      inference('sup-', [status(thm)], ['138', '170'])).
% 59.50/59.72  thf('172', plain, ((v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 59.50/59.72      inference('clc', [status(thm)], ['155', '156'])).
% 59.50/59.72  thf('173', plain,
% 59.50/59.72      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 59.50/59.72        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 59.50/59.72      inference('clc', [status(thm)], ['167', '168'])).
% 59.50/59.72  thf('174', plain,
% 59.50/59.72      (((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 59.50/59.72         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 59.50/59.72         (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 59.50/59.72         (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 59.50/59.72        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 59.50/59.72        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 59.50/59.72      inference('demod', [status(thm)], ['171', '172', '173'])).
% 59.50/59.72  thf('175', plain,
% 59.50/59.72      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 59.50/59.72        | (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 59.50/59.72           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 59.50/59.72           (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 59.50/59.72           (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 59.50/59.72      inference('simplify', [status(thm)], ['174'])).
% 59.50/59.72  thf('176', plain,
% 59.50/59.72      (![X0 : $i]:
% 59.50/59.72         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 59.50/59.72           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 59.50/59.72          | ~ (l1_pre_topc @ X0))),
% 59.50/59.72      inference('simplify', [status(thm)], ['49'])).
% 59.50/59.72  thf('177', plain,
% 59.50/59.72      (![X27 : $i, X28 : $i]:
% 59.50/59.72         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 59.50/59.72          | ((u1_struct_0 @ (k6_tmap_1 @ X28 @ X27)) = (u1_struct_0 @ X28))
% 59.50/59.72          | ~ (l1_pre_topc @ X28)
% 59.50/59.72          | ~ (v2_pre_topc @ X28)
% 59.50/59.72          | (v2_struct_0 @ X28))),
% 59.50/59.72      inference('cnf', [status(esa)], [t104_tmap_1])).
% 59.50/59.72  thf('178', plain,
% 59.50/59.72      (![X0 : $i]:
% 59.50/59.72         (~ (l1_pre_topc @ X0)
% 59.50/59.72          | (v2_struct_0 @ X0)
% 59.50/59.72          | ~ (v2_pre_topc @ X0)
% 59.50/59.72          | ~ (l1_pre_topc @ X0)
% 59.50/59.72          | ((u1_struct_0 @ (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 59.50/59.72              = (u1_struct_0 @ X0)))),
% 59.50/59.72      inference('sup-', [status(thm)], ['176', '177'])).
% 59.50/59.72  thf('179', plain,
% 59.50/59.72      (![X0 : $i]:
% 59.50/59.72         (((u1_struct_0 @ (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0)))
% 59.50/59.72            = (u1_struct_0 @ X0))
% 59.50/59.72          | ~ (v2_pre_topc @ X0)
% 59.50/59.72          | (v2_struct_0 @ X0)
% 59.50/59.72          | ~ (l1_pre_topc @ X0))),
% 59.50/59.72      inference('simplify', [status(thm)], ['178'])).
% 59.50/59.72  thf('180', plain,
% 59.50/59.72      (![X0 : $i]:
% 59.50/59.72         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 59.50/59.72           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 59.50/59.72          | ~ (l1_pre_topc @ X0))),
% 59.50/59.72      inference('simplify', [status(thm)], ['49'])).
% 59.50/59.72  thf('181', plain,
% 59.50/59.72      (![X21 : $i, X22 : $i]:
% 59.50/59.72         (~ (l1_pre_topc @ X21)
% 59.50/59.72          | ~ (v2_pre_topc @ X21)
% 59.50/59.72          | (v2_struct_0 @ X21)
% 59.50/59.72          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 59.50/59.72          | (m1_subset_1 @ (k7_tmap_1 @ X21 @ X22) @ 
% 59.50/59.72             (k1_zfmisc_1 @ 
% 59.50/59.72              (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ 
% 59.50/59.72               (u1_struct_0 @ (k6_tmap_1 @ X21 @ X22))))))),
% 59.50/59.72      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 59.50/59.72  thf('182', plain,
% 59.50/59.72      (![X0 : $i]:
% 59.50/59.72         (~ (l1_pre_topc @ X0)
% 59.50/59.72          | (m1_subset_1 @ (k7_tmap_1 @ X0 @ (u1_struct_0 @ X0)) @ 
% 59.50/59.72             (k1_zfmisc_1 @ 
% 59.50/59.72              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ 
% 59.50/59.72               (u1_struct_0 @ (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0))))))
% 59.50/59.72          | (v2_struct_0 @ X0)
% 59.50/59.72          | ~ (v2_pre_topc @ X0)
% 59.50/59.72          | ~ (l1_pre_topc @ X0))),
% 59.50/59.72      inference('sup-', [status(thm)], ['180', '181'])).
% 59.50/59.72  thf('183', plain,
% 59.50/59.72      (![X0 : $i]:
% 59.50/59.72         (~ (v2_pre_topc @ X0)
% 59.50/59.72          | (v2_struct_0 @ X0)
% 59.50/59.72          | (m1_subset_1 @ (k7_tmap_1 @ X0 @ (u1_struct_0 @ X0)) @ 
% 59.50/59.72             (k1_zfmisc_1 @ 
% 59.50/59.72              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ 
% 59.50/59.72               (u1_struct_0 @ (k6_tmap_1 @ X0 @ (u1_struct_0 @ X0))))))
% 59.50/59.72          | ~ (l1_pre_topc @ X0))),
% 59.50/59.72      inference('simplify', [status(thm)], ['182'])).
% 59.50/59.72  thf('184', plain,
% 59.50/59.72      (![X0 : $i]:
% 59.50/59.72         ((m1_subset_1 @ (k7_tmap_1 @ X0 @ (u1_struct_0 @ X0)) @ 
% 59.50/59.72           (k1_zfmisc_1 @ 
% 59.50/59.72            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0))))
% 59.50/59.72          | ~ (l1_pre_topc @ X0)
% 59.50/59.72          | (v2_struct_0 @ X0)
% 59.50/59.72          | ~ (v2_pre_topc @ X0)
% 59.50/59.72          | ~ (l1_pre_topc @ X0)
% 59.50/59.72          | (v2_struct_0 @ X0)
% 59.50/59.72          | ~ (v2_pre_topc @ X0))),
% 59.50/59.72      inference('sup+', [status(thm)], ['179', '183'])).
% 59.50/59.72  thf('185', plain,
% 59.50/59.72      (![X0 : $i]:
% 59.50/59.72         (~ (v2_pre_topc @ X0)
% 59.50/59.72          | (v2_struct_0 @ X0)
% 59.50/59.72          | ~ (l1_pre_topc @ X0)
% 59.50/59.72          | (m1_subset_1 @ (k7_tmap_1 @ X0 @ (u1_struct_0 @ X0)) @ 
% 59.50/59.72             (k1_zfmisc_1 @ 
% 59.50/59.72              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)))))),
% 59.50/59.72      inference('simplify', [status(thm)], ['184'])).
% 59.50/59.72  thf('186', plain,
% 59.50/59.72      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 59.50/59.72      inference('clc', [status(thm)], ['44', '45'])).
% 59.50/59.72  thf(d12_tmap_1, axiom,
% 59.50/59.72    (![A:$i]:
% 59.50/59.72     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 59.50/59.72       ( ![B:$i]:
% 59.50/59.72         ( ( m1_pre_topc @ B @ A ) =>
% 59.50/59.72           ( ![C:$i]:
% 59.50/59.72             ( ( ( v1_funct_1 @ C ) & 
% 59.50/59.72                 ( v1_funct_2 @
% 59.50/59.72                   C @ ( u1_struct_0 @ A ) @ 
% 59.50/59.72                   ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 59.50/59.72                 ( m1_subset_1 @
% 59.50/59.72                   C @ 
% 59.50/59.72                   ( k1_zfmisc_1 @
% 59.50/59.72                     ( k2_zfmisc_1 @
% 59.50/59.72                       ( u1_struct_0 @ A ) @ 
% 59.50/59.72                       ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) =>
% 59.50/59.72               ( ( ( C ) = ( k9_tmap_1 @ A @ B ) ) <=>
% 59.50/59.72                 ( ![D:$i]:
% 59.50/59.72                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 59.50/59.72                     ( ( ( D ) = ( u1_struct_0 @ B ) ) =>
% 59.50/59.72                       ( r1_funct_2 @
% 59.50/59.72                         ( u1_struct_0 @ A ) @ 
% 59.50/59.72                         ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) @ 
% 59.50/59.72                         ( u1_struct_0 @ A ) @ 
% 59.50/59.72                         ( u1_struct_0 @ ( k6_tmap_1 @ A @ D ) ) @ C @ 
% 59.50/59.72                         ( k7_tmap_1 @ A @ D ) ) ) ) ) ) ) ) ) ) ))).
% 59.50/59.72  thf('187', plain,
% 59.50/59.72      (![X14 : $i, X15 : $i, X16 : $i]:
% 59.50/59.72         (~ (m1_pre_topc @ X14 @ X15)
% 59.50/59.72          | (m1_subset_1 @ (sk_D_1 @ X16 @ X14 @ X15) @ 
% 59.50/59.72             (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 59.50/59.72          | ((X16) = (k9_tmap_1 @ X15 @ X14))
% 59.50/59.72          | ~ (m1_subset_1 @ X16 @ 
% 59.50/59.72               (k1_zfmisc_1 @ 
% 59.50/59.72                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ 
% 59.50/59.72                 (u1_struct_0 @ (k8_tmap_1 @ X15 @ X14)))))
% 59.50/59.72          | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ X15) @ 
% 59.50/59.72               (u1_struct_0 @ (k8_tmap_1 @ X15 @ X14)))
% 59.50/59.72          | ~ (v1_funct_1 @ X16)
% 59.50/59.72          | ~ (l1_pre_topc @ X15)
% 59.50/59.72          | ~ (v2_pre_topc @ X15)
% 59.50/59.72          | (v2_struct_0 @ X15))),
% 59.50/59.72      inference('cnf', [status(esa)], [d12_tmap_1])).
% 59.50/59.72  thf('188', plain,
% 59.50/59.72      (![X0 : $i]:
% 59.50/59.72         (~ (m1_subset_1 @ X0 @ 
% 59.50/59.72             (k1_zfmisc_1 @ 
% 59.50/59.72              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 59.50/59.72          | (v2_struct_0 @ sk_A)
% 59.50/59.72          | ~ (v2_pre_topc @ sk_A)
% 59.50/59.72          | ~ (l1_pre_topc @ sk_A)
% 59.50/59.72          | ~ (v1_funct_1 @ X0)
% 59.50/59.72          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ 
% 59.50/59.72               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 59.50/59.72          | ((X0) = (k9_tmap_1 @ sk_A @ sk_B))
% 59.50/59.72          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ 
% 59.50/59.72             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 59.50/59.72          | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 59.50/59.72      inference('sup-', [status(thm)], ['186', '187'])).
% 59.50/59.72  thf('189', plain, ((v2_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('190', plain, ((l1_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('191', plain,
% 59.50/59.72      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 59.50/59.72      inference('clc', [status(thm)], ['44', '45'])).
% 59.50/59.72  thf('192', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('193', plain,
% 59.50/59.72      (![X0 : $i]:
% 59.50/59.72         (~ (m1_subset_1 @ X0 @ 
% 59.50/59.72             (k1_zfmisc_1 @ 
% 59.50/59.72              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 59.50/59.72          | (v2_struct_0 @ sk_A)
% 59.50/59.72          | ~ (v1_funct_1 @ X0)
% 59.50/59.72          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 59.50/59.72          | ((X0) = (k9_tmap_1 @ sk_A @ sk_B))
% 59.50/59.72          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ 
% 59.50/59.72             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 59.50/59.72      inference('demod', [status(thm)], ['188', '189', '190', '191', '192'])).
% 59.50/59.72  thf('194', plain,
% 59.50/59.72      ((~ (l1_pre_topc @ sk_A)
% 59.50/59.72        | (v2_struct_0 @ sk_A)
% 59.50/59.72        | ~ (v2_pre_topc @ sk_A)
% 59.50/59.72        | (m1_subset_1 @ 
% 59.50/59.72           (sk_D_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_A) @ 
% 59.50/59.72           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 59.50/59.72        | ((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))
% 59.50/59.72            = (k9_tmap_1 @ sk_A @ sk_B))
% 59.50/59.72        | ~ (v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)) @ 
% 59.50/59.72             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 59.50/59.72        | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 59.50/59.72        | (v2_struct_0 @ sk_A))),
% 59.50/59.72      inference('sup-', [status(thm)], ['185', '193'])).
% 59.50/59.72  thf('195', plain, ((l1_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('196', plain, ((v2_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('197', plain,
% 59.50/59.72      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))
% 59.50/59.72         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 59.50/59.72      inference('clc', [status(thm)], ['62', '63'])).
% 59.50/59.72  thf('198', plain,
% 59.50/59.72      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))
% 59.50/59.72         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 59.50/59.72      inference('clc', [status(thm)], ['62', '63'])).
% 59.50/59.72  thf('199', plain,
% 59.50/59.72      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))
% 59.50/59.72         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 59.50/59.72      inference('clc', [status(thm)], ['62', '63'])).
% 59.50/59.72  thf('200', plain,
% 59.50/59.72      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 59.50/59.72        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 59.50/59.72      inference('clc', [status(thm)], ['167', '168'])).
% 59.50/59.72  thf('201', plain,
% 59.50/59.72      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))
% 59.50/59.72         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 59.50/59.72      inference('clc', [status(thm)], ['62', '63'])).
% 59.50/59.72  thf('202', plain, ((v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 59.50/59.72      inference('clc', [status(thm)], ['155', '156'])).
% 59.50/59.72  thf('203', plain,
% 59.50/59.72      (((v2_struct_0 @ sk_A)
% 59.50/59.72        | (m1_subset_1 @ 
% 59.50/59.72           (sk_D_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_A) @ 
% 59.50/59.72           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 59.50/59.72        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 59.50/59.72        | (v2_struct_0 @ sk_A))),
% 59.50/59.72      inference('demod', [status(thm)],
% 59.50/59.72                ['194', '195', '196', '197', '198', '199', '200', '201', '202'])).
% 59.50/59.72  thf('204', plain,
% 59.50/59.72      ((((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 59.50/59.72        | (m1_subset_1 @ 
% 59.50/59.72           (sk_D_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_A) @ 
% 59.50/59.72           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 59.50/59.72        | (v2_struct_0 @ sk_A))),
% 59.50/59.72      inference('simplify', [status(thm)], ['203'])).
% 59.50/59.72  thf('205', plain, (~ (v2_struct_0 @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('206', plain,
% 59.50/59.72      (((m1_subset_1 @ 
% 59.50/59.72         (sk_D_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_A) @ 
% 59.50/59.72         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 59.50/59.72        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B)))),
% 59.50/59.72      inference('clc', [status(thm)], ['204', '205'])).
% 59.50/59.72  thf('207', plain,
% 59.50/59.72      (![X8 : $i, X9 : $i]:
% 59.50/59.72         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 59.50/59.72          | ((k7_tmap_1 @ X9 @ X8) = (k6_partfun1 @ (u1_struct_0 @ X9)))
% 59.50/59.72          | ~ (l1_pre_topc @ X9)
% 59.50/59.72          | ~ (v2_pre_topc @ X9)
% 59.50/59.72          | (v2_struct_0 @ X9))),
% 59.50/59.72      inference('cnf', [status(esa)], [d10_tmap_1])).
% 59.50/59.72  thf('208', plain,
% 59.50/59.72      ((((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 59.50/59.72        | (v2_struct_0 @ sk_A)
% 59.50/59.72        | ~ (v2_pre_topc @ sk_A)
% 59.50/59.72        | ~ (l1_pre_topc @ sk_A)
% 59.50/59.72        | ((k7_tmap_1 @ sk_A @ 
% 59.50/59.72            (sk_D_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_A))
% 59.50/59.72            = (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 59.50/59.72      inference('sup-', [status(thm)], ['206', '207'])).
% 59.50/59.72  thf('209', plain, ((v2_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('210', plain, ((l1_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('211', plain,
% 59.50/59.72      ((((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 59.50/59.72        | (v2_struct_0 @ sk_A)
% 59.50/59.72        | ((k7_tmap_1 @ sk_A @ 
% 59.50/59.72            (sk_D_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_A))
% 59.50/59.72            = (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 59.50/59.72      inference('demod', [status(thm)], ['208', '209', '210'])).
% 59.50/59.72  thf('212', plain, (~ (v2_struct_0 @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('213', plain,
% 59.50/59.72      ((((k7_tmap_1 @ sk_A @ 
% 59.50/59.72          (sk_D_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_A))
% 59.50/59.72          = (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 59.50/59.72        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B)))),
% 59.50/59.72      inference('clc', [status(thm)], ['211', '212'])).
% 59.50/59.72  thf('214', plain,
% 59.50/59.72      (![X0 : $i]:
% 59.50/59.72         (~ (v2_pre_topc @ X0)
% 59.50/59.72          | (v2_struct_0 @ X0)
% 59.50/59.72          | ~ (l1_pre_topc @ X0)
% 59.50/59.72          | (m1_subset_1 @ (k7_tmap_1 @ X0 @ (u1_struct_0 @ X0)) @ 
% 59.50/59.72             (k1_zfmisc_1 @ 
% 59.50/59.72              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)))))),
% 59.50/59.72      inference('simplify', [status(thm)], ['184'])).
% 59.50/59.72  thf('215', plain,
% 59.50/59.72      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 59.50/59.72      inference('clc', [status(thm)], ['44', '45'])).
% 59.50/59.72  thf('216', plain,
% 59.50/59.72      (![X14 : $i, X15 : $i, X16 : $i]:
% 59.50/59.72         (~ (m1_pre_topc @ X14 @ X15)
% 59.50/59.72          | ((sk_D_1 @ X16 @ X14 @ X15) = (u1_struct_0 @ X14))
% 59.50/59.72          | ((X16) = (k9_tmap_1 @ X15 @ X14))
% 59.50/59.72          | ~ (m1_subset_1 @ X16 @ 
% 59.50/59.72               (k1_zfmisc_1 @ 
% 59.50/59.72                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ 
% 59.50/59.72                 (u1_struct_0 @ (k8_tmap_1 @ X15 @ X14)))))
% 59.50/59.72          | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ X15) @ 
% 59.50/59.72               (u1_struct_0 @ (k8_tmap_1 @ X15 @ X14)))
% 59.50/59.72          | ~ (v1_funct_1 @ X16)
% 59.50/59.72          | ~ (l1_pre_topc @ X15)
% 59.50/59.72          | ~ (v2_pre_topc @ X15)
% 59.50/59.72          | (v2_struct_0 @ X15))),
% 59.50/59.72      inference('cnf', [status(esa)], [d12_tmap_1])).
% 59.50/59.72  thf('217', plain,
% 59.50/59.72      (![X0 : $i]:
% 59.50/59.72         (~ (m1_subset_1 @ X0 @ 
% 59.50/59.72             (k1_zfmisc_1 @ 
% 59.50/59.72              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 59.50/59.72          | (v2_struct_0 @ sk_A)
% 59.50/59.72          | ~ (v2_pre_topc @ sk_A)
% 59.50/59.72          | ~ (l1_pre_topc @ sk_A)
% 59.50/59.72          | ~ (v1_funct_1 @ X0)
% 59.50/59.72          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ 
% 59.50/59.72               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 59.50/59.72          | ((X0) = (k9_tmap_1 @ sk_A @ sk_B))
% 59.50/59.72          | ((sk_D_1 @ X0 @ sk_B @ sk_A) = (u1_struct_0 @ sk_B))
% 59.50/59.72          | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 59.50/59.72      inference('sup-', [status(thm)], ['215', '216'])).
% 59.50/59.72  thf('218', plain, ((v2_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('219', plain, ((l1_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('220', plain,
% 59.50/59.72      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 59.50/59.72      inference('clc', [status(thm)], ['44', '45'])).
% 59.50/59.72  thf('221', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('222', plain,
% 59.50/59.72      (![X0 : $i]:
% 59.50/59.72         (~ (m1_subset_1 @ X0 @ 
% 59.50/59.72             (k1_zfmisc_1 @ 
% 59.50/59.72              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 59.50/59.72          | (v2_struct_0 @ sk_A)
% 59.50/59.72          | ~ (v1_funct_1 @ X0)
% 59.50/59.72          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 59.50/59.72          | ((X0) = (k9_tmap_1 @ sk_A @ sk_B))
% 59.50/59.72          | ((sk_D_1 @ X0 @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))),
% 59.50/59.72      inference('demod', [status(thm)], ['217', '218', '219', '220', '221'])).
% 59.50/59.72  thf('223', plain,
% 59.50/59.72      ((~ (l1_pre_topc @ sk_A)
% 59.50/59.72        | (v2_struct_0 @ sk_A)
% 59.50/59.72        | ~ (v2_pre_topc @ sk_A)
% 59.50/59.72        | ((sk_D_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_A)
% 59.50/59.72            = (u1_struct_0 @ sk_B))
% 59.50/59.72        | ((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))
% 59.50/59.72            = (k9_tmap_1 @ sk_A @ sk_B))
% 59.50/59.72        | ~ (v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)) @ 
% 59.50/59.72             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 59.50/59.72        | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 59.50/59.72        | (v2_struct_0 @ sk_A))),
% 59.50/59.72      inference('sup-', [status(thm)], ['214', '222'])).
% 59.50/59.72  thf('224', plain, ((l1_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('225', plain, ((v2_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('226', plain,
% 59.50/59.72      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))
% 59.50/59.72         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 59.50/59.72      inference('clc', [status(thm)], ['62', '63'])).
% 59.50/59.72  thf('227', plain,
% 59.50/59.72      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))
% 59.50/59.72         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 59.50/59.72      inference('clc', [status(thm)], ['62', '63'])).
% 59.50/59.72  thf('228', plain,
% 59.50/59.72      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))
% 59.50/59.72         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 59.50/59.72      inference('clc', [status(thm)], ['62', '63'])).
% 59.50/59.72  thf('229', plain,
% 59.50/59.72      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 59.50/59.72        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 59.50/59.72      inference('clc', [status(thm)], ['167', '168'])).
% 59.50/59.72  thf('230', plain,
% 59.50/59.72      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_A))
% 59.50/59.72         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 59.50/59.72      inference('clc', [status(thm)], ['62', '63'])).
% 59.50/59.72  thf('231', plain, ((v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 59.50/59.72      inference('clc', [status(thm)], ['155', '156'])).
% 59.50/59.72  thf('232', plain,
% 59.50/59.72      (((v2_struct_0 @ sk_A)
% 59.50/59.72        | ((sk_D_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_A)
% 59.50/59.72            = (u1_struct_0 @ sk_B))
% 59.50/59.72        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 59.50/59.72        | (v2_struct_0 @ sk_A))),
% 59.50/59.72      inference('demod', [status(thm)],
% 59.50/59.72                ['223', '224', '225', '226', '227', '228', '229', '230', '231'])).
% 59.50/59.72  thf('233', plain,
% 59.50/59.72      ((((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 59.50/59.72        | ((sk_D_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_A)
% 59.50/59.72            = (u1_struct_0 @ sk_B))
% 59.50/59.72        | (v2_struct_0 @ sk_A))),
% 59.50/59.72      inference('simplify', [status(thm)], ['232'])).
% 59.50/59.72  thf('234', plain, (~ (v2_struct_0 @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('235', plain,
% 59.50/59.72      ((((sk_D_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_A)
% 59.50/59.72          = (u1_struct_0 @ sk_B))
% 59.50/59.72        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B)))),
% 59.50/59.72      inference('clc', [status(thm)], ['233', '234'])).
% 59.50/59.72  thf('236', plain,
% 59.50/59.72      (![X14 : $i, X15 : $i, X16 : $i]:
% 59.50/59.72         (~ (m1_pre_topc @ X14 @ X15)
% 59.50/59.72          | ~ (r1_funct_2 @ (u1_struct_0 @ X15) @ 
% 59.50/59.72               (u1_struct_0 @ (k8_tmap_1 @ X15 @ X14)) @ (u1_struct_0 @ X15) @ 
% 59.50/59.72               (u1_struct_0 @ (k6_tmap_1 @ X15 @ (sk_D_1 @ X16 @ X14 @ X15))) @ 
% 59.50/59.72               X16 @ (k7_tmap_1 @ X15 @ (sk_D_1 @ X16 @ X14 @ X15)))
% 59.50/59.72          | ((X16) = (k9_tmap_1 @ X15 @ X14))
% 59.50/59.72          | ~ (m1_subset_1 @ X16 @ 
% 59.50/59.72               (k1_zfmisc_1 @ 
% 59.50/59.72                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ 
% 59.50/59.72                 (u1_struct_0 @ (k8_tmap_1 @ X15 @ X14)))))
% 59.50/59.72          | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ X15) @ 
% 59.50/59.72               (u1_struct_0 @ (k8_tmap_1 @ X15 @ X14)))
% 59.50/59.72          | ~ (v1_funct_1 @ X16)
% 59.50/59.72          | ~ (l1_pre_topc @ X15)
% 59.50/59.72          | ~ (v2_pre_topc @ X15)
% 59.50/59.72          | (v2_struct_0 @ X15))),
% 59.50/59.72      inference('cnf', [status(esa)], [d12_tmap_1])).
% 59.50/59.72  thf('237', plain,
% 59.50/59.72      ((~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ 
% 59.50/59.72           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) @ (u1_struct_0 @ sk_A) @ 
% 59.50/59.72           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))) @ 
% 59.50/59.72           (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 59.50/59.72           (k7_tmap_1 @ sk_A @ 
% 59.50/59.72            (sk_D_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_A)))
% 59.50/59.72        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 59.50/59.72        | (v2_struct_0 @ sk_A)
% 59.50/59.72        | ~ (v2_pre_topc @ sk_A)
% 59.50/59.72        | ~ (l1_pre_topc @ sk_A)
% 59.50/59.72        | ~ (v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 59.50/59.72        | ~ (v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 59.50/59.72             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 59.50/59.72        | ~ (m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 59.50/59.72             (k1_zfmisc_1 @ 
% 59.50/59.72              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 59.50/59.72               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))
% 59.50/59.72        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 59.50/59.72        | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 59.50/59.72      inference('sup-', [status(thm)], ['235', '236'])).
% 59.50/59.72  thf('238', plain,
% 59.50/59.72      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 59.50/59.72      inference('clc', [status(thm)], ['44', '45'])).
% 59.50/59.72  thf('239', plain,
% 59.50/59.72      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 59.50/59.72      inference('clc', [status(thm)], ['41', '42'])).
% 59.50/59.72  thf('240', plain,
% 59.50/59.72      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 59.50/59.72      inference('clc', [status(thm)], ['44', '45'])).
% 59.50/59.72  thf('241', plain, ((v2_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('242', plain, ((l1_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('243', plain, ((v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 59.50/59.72      inference('clc', [status(thm)], ['155', '156'])).
% 59.50/59.72  thf('244', plain,
% 59.50/59.72      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 59.50/59.72      inference('clc', [status(thm)], ['44', '45'])).
% 59.50/59.72  thf('245', plain,
% 59.50/59.72      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 59.50/59.72        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 59.50/59.72      inference('clc', [status(thm)], ['167', '168'])).
% 59.50/59.72  thf('246', plain,
% 59.50/59.72      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 59.50/59.72      inference('clc', [status(thm)], ['44', '45'])).
% 59.50/59.72  thf('247', plain,
% 59.50/59.72      ((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 59.50/59.72        (k1_zfmisc_1 @ 
% 59.50/59.72         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 59.50/59.72      inference('clc', [status(thm)], ['136', '137'])).
% 59.50/59.72  thf('248', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('249', plain,
% 59.50/59.72      ((~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 59.50/59.72           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 59.50/59.72           (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 59.50/59.72           (k7_tmap_1 @ sk_A @ 
% 59.50/59.72            (sk_D_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_A)))
% 59.50/59.72        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 59.50/59.72        | (v2_struct_0 @ sk_A)
% 59.50/59.72        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B)))),
% 59.50/59.72      inference('demod', [status(thm)],
% 59.50/59.72                ['237', '238', '239', '240', '241', '242', '243', '244', 
% 59.50/59.72                 '245', '246', '247', '248'])).
% 59.50/59.72  thf('250', plain,
% 59.50/59.72      (((v2_struct_0 @ sk_A)
% 59.50/59.72        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 59.50/59.72        | ~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 59.50/59.72             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 59.50/59.72             (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 59.50/59.72             (k7_tmap_1 @ sk_A @ 
% 59.50/59.72              (sk_D_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_A))))),
% 59.50/59.72      inference('simplify', [status(thm)], ['249'])).
% 59.50/59.72  thf('251', plain, (~ (v2_struct_0 @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('252', plain,
% 59.50/59.72      ((~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 59.50/59.72           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 59.50/59.72           (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 59.50/59.72           (k7_tmap_1 @ sk_A @ 
% 59.50/59.72            (sk_D_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_A)))
% 59.50/59.72        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B)))),
% 59.50/59.72      inference('clc', [status(thm)], ['250', '251'])).
% 59.50/59.72  thf('253', plain,
% 59.50/59.72      ((~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 59.50/59.72           (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 59.50/59.72           (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 59.50/59.72           (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 59.50/59.72        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 59.50/59.72        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B)))),
% 59.50/59.72      inference('sup-', [status(thm)], ['213', '252'])).
% 59.50/59.72  thf('254', plain,
% 59.50/59.72      ((((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B))
% 59.50/59.72        | ~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 59.50/59.72             (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 59.50/59.72             (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 59.50/59.72             (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 59.50/59.72      inference('simplify', [status(thm)], ['253'])).
% 59.50/59.72  thf('255', plain,
% 59.50/59.72      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 59.50/59.72        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B)))),
% 59.50/59.72      inference('sup-', [status(thm)], ['175', '254'])).
% 59.50/59.72  thf('256', plain,
% 59.50/59.72      (((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 59.50/59.72         (k8_tmap_1 @ sk_A @ sk_B))
% 59.50/59.72        | (v1_tsep_1 @ sk_B @ sk_A))),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('257', plain,
% 59.50/59.72      (((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 59.50/59.72         (k8_tmap_1 @ sk_A @ sk_B)))
% 59.50/59.72         <= (((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 59.50/59.72               (k8_tmap_1 @ sk_A @ sk_B))))),
% 59.50/59.72      inference('split', [status(esa)], ['256'])).
% 59.50/59.72  thf('258', plain,
% 59.50/59.72      ((~ (m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 59.50/59.72           (k1_zfmisc_1 @ 
% 59.50/59.72            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 59.50/59.72             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))
% 59.50/59.72        | ~ (v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 59.50/59.72             (k8_tmap_1 @ sk_A @ sk_B))
% 59.50/59.72        | ~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 59.50/59.72             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 59.50/59.72        | ~ (v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))
% 59.50/59.72        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 59.50/59.72        | ~ (v1_tsep_1 @ sk_B @ sk_A))),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('259', plain,
% 59.50/59.72      (~ ((v1_tsep_1 @ sk_B @ sk_A)) | 
% 59.50/59.72       ~
% 59.50/59.72       ((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 59.50/59.72         (k8_tmap_1 @ sk_A @ sk_B))) | 
% 59.50/59.72       ~ ((m1_pre_topc @ sk_B @ sk_A)) | 
% 59.50/59.72       ~ ((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))) | 
% 59.50/59.72       ~
% 59.50/59.72       ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 59.50/59.72         (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))) | 
% 59.50/59.72       ~
% 59.50/59.72       ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 59.50/59.72         (k1_zfmisc_1 @ 
% 59.50/59.72          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 59.50/59.72           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))))),
% 59.50/59.72      inference('split', [status(esa)], ['258'])).
% 59.50/59.72  thf('260', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('261', plain,
% 59.50/59.72      ((~ (m1_pre_topc @ sk_B @ sk_A)) <= (~ ((m1_pre_topc @ sk_B @ sk_A)))),
% 59.50/59.72      inference('split', [status(esa)], ['258'])).
% 59.50/59.72  thf('262', plain, (((m1_pre_topc @ sk_B @ sk_A))),
% 59.50/59.72      inference('sup-', [status(thm)], ['260', '261'])).
% 59.50/59.72  thf('263', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf(dt_k9_tmap_1, axiom,
% 59.50/59.72    (![A:$i,B:$i]:
% 59.50/59.72     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 59.50/59.72         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 59.50/59.72       ( ( v1_funct_1 @ ( k9_tmap_1 @ A @ B ) ) & 
% 59.50/59.72         ( v1_funct_2 @
% 59.50/59.72           ( k9_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 59.50/59.72           ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 59.50/59.72         ( m1_subset_1 @
% 59.50/59.72           ( k9_tmap_1 @ A @ B ) @ 
% 59.50/59.72           ( k1_zfmisc_1 @
% 59.50/59.72             ( k2_zfmisc_1 @
% 59.50/59.72               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ))).
% 59.50/59.72  thf('264', plain,
% 59.50/59.72      (![X25 : $i, X26 : $i]:
% 59.50/59.72         (~ (l1_pre_topc @ X25)
% 59.50/59.72          | ~ (v2_pre_topc @ X25)
% 59.50/59.72          | (v2_struct_0 @ X25)
% 59.50/59.72          | ~ (m1_pre_topc @ X26 @ X25)
% 59.50/59.72          | (v1_funct_1 @ (k9_tmap_1 @ X25 @ X26)))),
% 59.50/59.72      inference('cnf', [status(esa)], [dt_k9_tmap_1])).
% 59.50/59.72  thf('265', plain,
% 59.50/59.72      (((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))
% 59.50/59.72        | (v2_struct_0 @ sk_A)
% 59.50/59.72        | ~ (v2_pre_topc @ sk_A)
% 59.50/59.72        | ~ (l1_pre_topc @ sk_A))),
% 59.50/59.72      inference('sup-', [status(thm)], ['263', '264'])).
% 59.50/59.72  thf('266', plain, ((v2_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('267', plain, ((l1_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('268', plain,
% 59.50/59.72      (((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 59.50/59.72      inference('demod', [status(thm)], ['265', '266', '267'])).
% 59.50/59.72  thf('269', plain, (~ (v2_struct_0 @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('270', plain, ((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))),
% 59.50/59.72      inference('clc', [status(thm)], ['268', '269'])).
% 59.50/59.72  thf('271', plain,
% 59.50/59.72      ((~ (v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B)))
% 59.50/59.72         <= (~ ((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))))),
% 59.50/59.72      inference('split', [status(esa)], ['258'])).
% 59.50/59.72  thf('272', plain, (((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B)))),
% 59.50/59.72      inference('sup-', [status(thm)], ['270', '271'])).
% 59.50/59.72  thf('273', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('274', plain,
% 59.50/59.72      (![X25 : $i, X26 : $i]:
% 59.50/59.72         (~ (l1_pre_topc @ X25)
% 59.50/59.72          | ~ (v2_pre_topc @ X25)
% 59.50/59.72          | (v2_struct_0 @ X25)
% 59.50/59.72          | ~ (m1_pre_topc @ X26 @ X25)
% 59.50/59.72          | (v1_funct_2 @ (k9_tmap_1 @ X25 @ X26) @ (u1_struct_0 @ X25) @ 
% 59.50/59.72             (u1_struct_0 @ (k8_tmap_1 @ X25 @ X26))))),
% 59.50/59.72      inference('cnf', [status(esa)], [dt_k9_tmap_1])).
% 59.50/59.72  thf('275', plain,
% 59.50/59.72      (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 59.50/59.72         (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 59.50/59.72        | (v2_struct_0 @ sk_A)
% 59.50/59.72        | ~ (v2_pre_topc @ sk_A)
% 59.50/59.72        | ~ (l1_pre_topc @ sk_A))),
% 59.50/59.72      inference('sup-', [status(thm)], ['273', '274'])).
% 59.50/59.72  thf('276', plain,
% 59.50/59.72      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 59.50/59.72      inference('clc', [status(thm)], ['44', '45'])).
% 59.50/59.72  thf('277', plain, ((v2_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('278', plain, ((l1_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('279', plain,
% 59.50/59.72      (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 59.50/59.72         (u1_struct_0 @ sk_A))
% 59.50/59.72        | (v2_struct_0 @ sk_A))),
% 59.50/59.72      inference('demod', [status(thm)], ['275', '276', '277', '278'])).
% 59.50/59.72  thf('280', plain, (~ (v2_struct_0 @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('281', plain,
% 59.50/59.72      ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 59.50/59.72        (u1_struct_0 @ sk_A))),
% 59.50/59.72      inference('clc', [status(thm)], ['279', '280'])).
% 59.50/59.72  thf('282', plain,
% 59.50/59.72      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 59.50/59.72      inference('clc', [status(thm)], ['44', '45'])).
% 59.50/59.72  thf('283', plain,
% 59.50/59.72      ((~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 59.50/59.72           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))
% 59.50/59.72         <= (~
% 59.50/59.72             ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 59.50/59.72               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))),
% 59.50/59.72      inference('split', [status(esa)], ['258'])).
% 59.50/59.72  thf('284', plain,
% 59.50/59.72      ((~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 59.50/59.72           (u1_struct_0 @ sk_A)))
% 59.50/59.72         <= (~
% 59.50/59.72             ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 59.50/59.72               (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))),
% 59.50/59.72      inference('sup-', [status(thm)], ['282', '283'])).
% 59.50/59.72  thf('285', plain,
% 59.50/59.72      (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 59.50/59.72         (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))),
% 59.50/59.72      inference('sup-', [status(thm)], ['281', '284'])).
% 59.50/59.72  thf('286', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('287', plain,
% 59.50/59.72      (![X25 : $i, X26 : $i]:
% 59.50/59.72         (~ (l1_pre_topc @ X25)
% 59.50/59.72          | ~ (v2_pre_topc @ X25)
% 59.50/59.72          | (v2_struct_0 @ X25)
% 59.50/59.72          | ~ (m1_pre_topc @ X26 @ X25)
% 59.50/59.72          | (m1_subset_1 @ (k9_tmap_1 @ X25 @ X26) @ 
% 59.50/59.72             (k1_zfmisc_1 @ 
% 59.50/59.72              (k2_zfmisc_1 @ (u1_struct_0 @ X25) @ 
% 59.50/59.72               (u1_struct_0 @ (k8_tmap_1 @ X25 @ X26))))))),
% 59.50/59.72      inference('cnf', [status(esa)], [dt_k9_tmap_1])).
% 59.50/59.72  thf('288', plain,
% 59.50/59.72      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 59.50/59.72         (k1_zfmisc_1 @ 
% 59.50/59.72          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 59.50/59.72           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))
% 59.50/59.72        | (v2_struct_0 @ sk_A)
% 59.50/59.72        | ~ (v2_pre_topc @ sk_A)
% 59.50/59.72        | ~ (l1_pre_topc @ sk_A))),
% 59.50/59.72      inference('sup-', [status(thm)], ['286', '287'])).
% 59.50/59.72  thf('289', plain,
% 59.50/59.72      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 59.50/59.72      inference('clc', [status(thm)], ['44', '45'])).
% 59.50/59.72  thf('290', plain, ((v2_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('291', plain, ((l1_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('292', plain,
% 59.50/59.72      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 59.50/59.72         (k1_zfmisc_1 @ 
% 59.50/59.72          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 59.50/59.72        | (v2_struct_0 @ sk_A))),
% 59.50/59.72      inference('demod', [status(thm)], ['288', '289', '290', '291'])).
% 59.50/59.72  thf('293', plain, (~ (v2_struct_0 @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('294', plain,
% 59.50/59.72      ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 59.50/59.72        (k1_zfmisc_1 @ 
% 59.50/59.72         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 59.50/59.72      inference('clc', [status(thm)], ['292', '293'])).
% 59.50/59.72  thf('295', plain,
% 59.50/59.72      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 59.50/59.72      inference('clc', [status(thm)], ['44', '45'])).
% 59.50/59.72  thf('296', plain,
% 59.50/59.72      ((~ (m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 59.50/59.72           (k1_zfmisc_1 @ 
% 59.50/59.72            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 59.50/59.72             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))))
% 59.50/59.72         <= (~
% 59.50/59.72             ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 59.50/59.72               (k1_zfmisc_1 @ 
% 59.50/59.72                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 59.50/59.72                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 59.50/59.72      inference('split', [status(esa)], ['258'])).
% 59.50/59.72  thf('297', plain,
% 59.50/59.72      ((~ (m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 59.50/59.72           (k1_zfmisc_1 @ 
% 59.50/59.72            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))
% 59.50/59.72         <= (~
% 59.50/59.72             ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 59.50/59.72               (k1_zfmisc_1 @ 
% 59.50/59.72                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 59.50/59.72                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 59.50/59.72      inference('sup-', [status(thm)], ['295', '296'])).
% 59.50/59.72  thf('298', plain,
% 59.50/59.72      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 59.50/59.72         (k1_zfmisc_1 @ 
% 59.50/59.72          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 59.50/59.72           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))))),
% 59.50/59.72      inference('sup-', [status(thm)], ['294', '297'])).
% 59.50/59.72  thf('299', plain,
% 59.50/59.72      (((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B)) | (v1_tsep_1 @ sk_B @ sk_A))),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('300', plain,
% 59.50/59.72      (((v1_tsep_1 @ sk_B @ sk_A)) <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 59.50/59.72      inference('split', [status(esa)], ['299'])).
% 59.50/59.72  thf('301', plain,
% 59.50/59.72      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 59.50/59.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 59.50/59.72      inference('demod', [status(thm)], ['3', '4'])).
% 59.50/59.72  thf(d1_tsep_1, axiom,
% 59.50/59.72    (![A:$i]:
% 59.50/59.72     ( ( l1_pre_topc @ A ) =>
% 59.50/59.72       ( ![B:$i]:
% 59.50/59.72         ( ( m1_pre_topc @ B @ A ) =>
% 59.50/59.72           ( ( v1_tsep_1 @ B @ A ) <=>
% 59.50/59.72             ( ![C:$i]:
% 59.50/59.72               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 59.50/59.72                 ( ( ( C ) = ( u1_struct_0 @ B ) ) => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 59.50/59.72  thf('302', plain,
% 59.50/59.72      (![X18 : $i, X19 : $i, X20 : $i]:
% 59.50/59.72         (~ (m1_pre_topc @ X18 @ X19)
% 59.50/59.72          | ~ (v1_tsep_1 @ X18 @ X19)
% 59.50/59.72          | ((X20) != (u1_struct_0 @ X18))
% 59.50/59.72          | (v3_pre_topc @ X20 @ X19)
% 59.50/59.72          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 59.50/59.72          | ~ (l1_pre_topc @ X19))),
% 59.50/59.72      inference('cnf', [status(esa)], [d1_tsep_1])).
% 59.50/59.72  thf('303', plain,
% 59.50/59.72      (![X18 : $i, X19 : $i]:
% 59.50/59.72         (~ (l1_pre_topc @ X19)
% 59.50/59.72          | ~ (m1_subset_1 @ (u1_struct_0 @ X18) @ 
% 59.50/59.72               (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 59.50/59.72          | (v3_pre_topc @ (u1_struct_0 @ X18) @ X19)
% 59.50/59.72          | ~ (v1_tsep_1 @ X18 @ X19)
% 59.50/59.72          | ~ (m1_pre_topc @ X18 @ X19))),
% 59.50/59.72      inference('simplify', [status(thm)], ['302'])).
% 59.50/59.72  thf('304', plain,
% 59.50/59.72      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 59.50/59.72        | ~ (v1_tsep_1 @ sk_B @ sk_A)
% 59.50/59.72        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 59.50/59.72        | ~ (l1_pre_topc @ sk_A))),
% 59.50/59.72      inference('sup-', [status(thm)], ['301', '303'])).
% 59.50/59.72  thf('305', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('306', plain, ((l1_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('307', plain,
% 59.50/59.72      ((~ (v1_tsep_1 @ sk_B @ sk_A)
% 59.50/59.72        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 59.50/59.72      inference('demod', [status(thm)], ['304', '305', '306'])).
% 59.50/59.72  thf('308', plain,
% 59.50/59.72      (((v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))
% 59.50/59.72         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 59.50/59.72      inference('sup-', [status(thm)], ['300', '307'])).
% 59.50/59.72  thf('309', plain,
% 59.50/59.72      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 59.50/59.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 59.50/59.72      inference('demod', [status(thm)], ['3', '4'])).
% 59.50/59.72  thf(t113_tmap_1, axiom,
% 59.50/59.72    (![A:$i]:
% 59.50/59.72     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 59.50/59.72       ( ![B:$i]:
% 59.50/59.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 59.50/59.72           ( ( v3_pre_topc @ B @ A ) <=>
% 59.50/59.72             ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) ) & 
% 59.50/59.72               ( v1_funct_2 @
% 59.50/59.72                 ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 59.50/59.72                 ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 59.50/59.72               ( v5_pre_topc @
% 59.50/59.72                 ( k7_tmap_1 @ A @ B ) @ A @ ( k6_tmap_1 @ A @ B ) ) & 
% 59.50/59.72               ( m1_subset_1 @
% 59.50/59.72                 ( k7_tmap_1 @ A @ B ) @ 
% 59.50/59.72                 ( k1_zfmisc_1 @
% 59.50/59.72                   ( k2_zfmisc_1 @
% 59.50/59.72                     ( u1_struct_0 @ A ) @ 
% 59.50/59.72                     ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) ))).
% 59.50/59.72  thf('310', plain,
% 59.50/59.72      (![X29 : $i, X30 : $i]:
% 59.50/59.72         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 59.50/59.72          | ~ (v3_pre_topc @ X29 @ X30)
% 59.50/59.72          | (v5_pre_topc @ (k7_tmap_1 @ X30 @ X29) @ X30 @ 
% 59.50/59.72             (k6_tmap_1 @ X30 @ X29))
% 59.50/59.72          | ~ (l1_pre_topc @ X30)
% 59.50/59.72          | ~ (v2_pre_topc @ X30)
% 59.50/59.72          | (v2_struct_0 @ X30))),
% 59.50/59.72      inference('cnf', [status(esa)], [t113_tmap_1])).
% 59.50/59.72  thf('311', plain,
% 59.50/59.72      (((v2_struct_0 @ sk_A)
% 59.50/59.72        | ~ (v2_pre_topc @ sk_A)
% 59.50/59.72        | ~ (l1_pre_topc @ sk_A)
% 59.50/59.72        | (v5_pre_topc @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_A @ 
% 59.50/59.72           (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 59.50/59.72        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 59.50/59.72      inference('sup-', [status(thm)], ['309', '310'])).
% 59.50/59.72  thf('312', plain, ((v2_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('313', plain, ((l1_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('314', plain,
% 59.50/59.72      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 59.50/59.72         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 59.50/59.72      inference('clc', [status(thm)], ['150', '151'])).
% 59.50/59.72  thf('315', plain,
% 59.50/59.72      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 59.50/59.72      inference('clc', [status(thm)], ['41', '42'])).
% 59.50/59.72  thf('316', plain,
% 59.50/59.72      (((v2_struct_0 @ sk_A)
% 59.50/59.72        | (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 59.50/59.72           (k8_tmap_1 @ sk_A @ sk_B))
% 59.50/59.72        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 59.50/59.72      inference('demod', [status(thm)], ['311', '312', '313', '314', '315'])).
% 59.50/59.72  thf('317', plain, (~ (v2_struct_0 @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('318', plain,
% 59.50/59.72      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 59.50/59.72        | (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 59.50/59.72           (k8_tmap_1 @ sk_A @ sk_B)))),
% 59.50/59.72      inference('clc', [status(thm)], ['316', '317'])).
% 59.50/59.72  thf('319', plain,
% 59.50/59.72      (((v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 59.50/59.72         (k8_tmap_1 @ sk_A @ sk_B))) <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 59.50/59.72      inference('sup-', [status(thm)], ['308', '318'])).
% 59.50/59.72  thf('320', plain,
% 59.50/59.72      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 59.50/59.72        | ((k6_partfun1 @ (u1_struct_0 @ sk_A)) = (k9_tmap_1 @ sk_A @ sk_B)))),
% 59.50/59.72      inference('sup-', [status(thm)], ['175', '254'])).
% 59.50/59.72  thf('321', plain,
% 59.50/59.72      ((~ (v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 59.50/59.72           (k8_tmap_1 @ sk_A @ sk_B)))
% 59.50/59.72         <= (~
% 59.50/59.72             ((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 59.50/59.72               (k8_tmap_1 @ sk_A @ sk_B))))),
% 59.50/59.72      inference('split', [status(esa)], ['258'])).
% 59.50/59.72  thf('322', plain,
% 59.50/59.72      (((~ (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 59.50/59.72            (k8_tmap_1 @ sk_A @ sk_B))
% 59.50/59.72         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 59.50/59.72         <= (~
% 59.50/59.72             ((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 59.50/59.72               (k8_tmap_1 @ sk_A @ sk_B))))),
% 59.50/59.72      inference('sup-', [status(thm)], ['320', '321'])).
% 59.50/59.72  thf('323', plain,
% 59.50/59.72      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 59.50/59.72         <= (~
% 59.50/59.72             ((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 59.50/59.72               (k8_tmap_1 @ sk_A @ sk_B))) & 
% 59.50/59.72             ((v1_tsep_1 @ sk_B @ sk_A)))),
% 59.50/59.72      inference('sup-', [status(thm)], ['319', '322'])).
% 59.50/59.72  thf(fc2_struct_0, axiom,
% 59.50/59.72    (![A:$i]:
% 59.50/59.72     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 59.50/59.72       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 59.50/59.72  thf('324', plain,
% 59.50/59.72      (![X1 : $i]:
% 59.50/59.72         (~ (v1_xboole_0 @ (u1_struct_0 @ X1))
% 59.50/59.72          | ~ (l1_struct_0 @ X1)
% 59.50/59.72          | (v2_struct_0 @ X1))),
% 59.50/59.72      inference('cnf', [status(esa)], [fc2_struct_0])).
% 59.50/59.72  thf('325', plain,
% 59.50/59.72      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 59.50/59.72         <= (~
% 59.50/59.72             ((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 59.50/59.72               (k8_tmap_1 @ sk_A @ sk_B))) & 
% 59.50/59.72             ((v1_tsep_1 @ sk_B @ sk_A)))),
% 59.50/59.72      inference('sup-', [status(thm)], ['323', '324'])).
% 59.50/59.72  thf('326', plain, ((l1_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf(dt_l1_pre_topc, axiom,
% 59.50/59.72    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 59.50/59.72  thf('327', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 59.50/59.72      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 59.50/59.72  thf('328', plain, ((l1_struct_0 @ sk_A)),
% 59.50/59.72      inference('sup-', [status(thm)], ['326', '327'])).
% 59.50/59.72  thf('329', plain,
% 59.50/59.72      (((v2_struct_0 @ sk_A))
% 59.50/59.72         <= (~
% 59.50/59.72             ((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 59.50/59.72               (k8_tmap_1 @ sk_A @ sk_B))) & 
% 59.50/59.72             ((v1_tsep_1 @ sk_B @ sk_A)))),
% 59.50/59.72      inference('demod', [status(thm)], ['325', '328'])).
% 59.50/59.72  thf('330', plain, (~ (v2_struct_0 @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('331', plain,
% 59.50/59.72      (((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 59.50/59.72         (k8_tmap_1 @ sk_A @ sk_B))) | 
% 59.50/59.72       ~ ((v1_tsep_1 @ sk_B @ sk_A))),
% 59.50/59.72      inference('sup-', [status(thm)], ['329', '330'])).
% 59.50/59.72  thf('332', plain,
% 59.50/59.72      (((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 59.50/59.72         (k8_tmap_1 @ sk_A @ sk_B))) | 
% 59.50/59.72       ((v1_tsep_1 @ sk_B @ sk_A))),
% 59.50/59.72      inference('split', [status(esa)], ['256'])).
% 59.50/59.72  thf('333', plain,
% 59.50/59.72      (((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 59.50/59.72         (k8_tmap_1 @ sk_A @ sk_B)))),
% 59.50/59.72      inference('sat_resolution*', [status(thm)],
% 59.50/59.72                ['259', '262', '272', '285', '298', '331', '332'])).
% 59.50/59.72  thf('334', plain,
% 59.50/59.72      ((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 59.50/59.72        (k8_tmap_1 @ sk_A @ sk_B))),
% 59.50/59.72      inference('simpl_trail', [status(thm)], ['257', '333'])).
% 59.50/59.72  thf('335', plain,
% 59.50/59.72      (((v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 59.50/59.72         (k8_tmap_1 @ sk_A @ sk_B))
% 59.50/59.72        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 59.50/59.72      inference('sup+', [status(thm)], ['255', '334'])).
% 59.50/59.72  thf('336', plain,
% 59.50/59.72      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 59.50/59.72         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 59.50/59.72      inference('clc', [status(thm)], ['150', '151'])).
% 59.50/59.72  thf('337', plain,
% 59.50/59.72      (![X29 : $i, X30 : $i]:
% 59.50/59.72         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 59.50/59.72          | ~ (v1_funct_1 @ (k7_tmap_1 @ X30 @ X29))
% 59.50/59.72          | ~ (v1_funct_2 @ (k7_tmap_1 @ X30 @ X29) @ (u1_struct_0 @ X30) @ 
% 59.50/59.72               (u1_struct_0 @ (k6_tmap_1 @ X30 @ X29)))
% 59.50/59.72          | ~ (v5_pre_topc @ (k7_tmap_1 @ X30 @ X29) @ X30 @ 
% 59.50/59.72               (k6_tmap_1 @ X30 @ X29))
% 59.50/59.72          | ~ (m1_subset_1 @ (k7_tmap_1 @ X30 @ X29) @ 
% 59.50/59.72               (k1_zfmisc_1 @ 
% 59.50/59.72                (k2_zfmisc_1 @ (u1_struct_0 @ X30) @ 
% 59.50/59.72                 (u1_struct_0 @ (k6_tmap_1 @ X30 @ X29)))))
% 59.50/59.72          | (v3_pre_topc @ X29 @ X30)
% 59.50/59.72          | ~ (l1_pre_topc @ X30)
% 59.50/59.72          | ~ (v2_pre_topc @ X30)
% 59.50/59.72          | (v2_struct_0 @ X30))),
% 59.50/59.72      inference('cnf', [status(esa)], [t113_tmap_1])).
% 59.50/59.72  thf('338', plain,
% 59.50/59.72      ((~ (m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 59.50/59.72           (k1_zfmisc_1 @ 
% 59.50/59.72            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 59.50/59.72             (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))))
% 59.50/59.72        | (v2_struct_0 @ sk_A)
% 59.50/59.72        | ~ (v2_pre_topc @ sk_A)
% 59.50/59.72        | ~ (l1_pre_topc @ sk_A)
% 59.50/59.72        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 59.50/59.72        | ~ (v5_pre_topc @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_A @ 
% 59.50/59.72             (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 59.50/59.72        | ~ (v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 59.50/59.72             (u1_struct_0 @ sk_A) @ 
% 59.50/59.72             (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))
% 59.50/59.72        | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 59.50/59.72        | ~ (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 59.50/59.72             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 59.50/59.72      inference('sup-', [status(thm)], ['336', '337'])).
% 59.50/59.72  thf('339', plain,
% 59.50/59.72      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 59.50/59.72      inference('clc', [status(thm)], ['41', '42'])).
% 59.50/59.72  thf('340', plain,
% 59.50/59.72      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 59.50/59.72      inference('clc', [status(thm)], ['44', '45'])).
% 59.50/59.72  thf('341', plain,
% 59.50/59.72      ((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 59.50/59.72        (k1_zfmisc_1 @ 
% 59.50/59.72         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 59.50/59.72      inference('clc', [status(thm)], ['136', '137'])).
% 59.50/59.72  thf('342', plain, ((v2_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('343', plain, ((l1_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('344', plain,
% 59.50/59.72      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 59.50/59.72         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 59.50/59.72      inference('clc', [status(thm)], ['150', '151'])).
% 59.50/59.72  thf('345', plain,
% 59.50/59.72      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 59.50/59.72      inference('clc', [status(thm)], ['41', '42'])).
% 59.50/59.72  thf('346', plain,
% 59.50/59.72      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 59.50/59.72         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 59.50/59.72      inference('clc', [status(thm)], ['150', '151'])).
% 59.50/59.72  thf('347', plain,
% 59.50/59.72      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 59.50/59.72      inference('clc', [status(thm)], ['41', '42'])).
% 59.50/59.72  thf('348', plain,
% 59.50/59.72      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 59.50/59.72      inference('clc', [status(thm)], ['44', '45'])).
% 59.50/59.72  thf('349', plain,
% 59.50/59.72      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 59.50/59.72        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 59.50/59.72      inference('clc', [status(thm)], ['167', '168'])).
% 59.50/59.72  thf('350', plain,
% 59.50/59.72      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 59.50/59.72         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 59.50/59.72      inference('clc', [status(thm)], ['150', '151'])).
% 59.50/59.72  thf('351', plain, ((v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 59.50/59.72      inference('clc', [status(thm)], ['155', '156'])).
% 59.50/59.72  thf('352', plain,
% 59.50/59.72      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 59.50/59.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 59.50/59.72      inference('demod', [status(thm)], ['3', '4'])).
% 59.50/59.72  thf('353', plain,
% 59.50/59.72      (((v2_struct_0 @ sk_A)
% 59.50/59.72        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 59.50/59.72        | ~ (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 59.50/59.72             (k8_tmap_1 @ sk_A @ sk_B)))),
% 59.50/59.72      inference('demod', [status(thm)],
% 59.50/59.72                ['338', '339', '340', '341', '342', '343', '344', '345', 
% 59.50/59.72                 '346', '347', '348', '349', '350', '351', '352'])).
% 59.50/59.72  thf('354', plain, (~ (v2_struct_0 @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('355', plain,
% 59.50/59.72      ((~ (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 59.50/59.72           (k8_tmap_1 @ sk_A @ sk_B))
% 59.50/59.72        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 59.50/59.72      inference('clc', [status(thm)], ['353', '354'])).
% 59.50/59.72  thf('356', plain,
% 59.50/59.72      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 59.50/59.72        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 59.50/59.72      inference('sup-', [status(thm)], ['335', '355'])).
% 59.50/59.72  thf('357', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('358', plain,
% 59.50/59.72      (![X18 : $i, X19 : $i]:
% 59.50/59.72         (~ (m1_pre_topc @ X18 @ X19)
% 59.50/59.72          | ((sk_C @ X18 @ X19) = (u1_struct_0 @ X18))
% 59.50/59.72          | (v1_tsep_1 @ X18 @ X19)
% 59.50/59.72          | ~ (l1_pre_topc @ X19))),
% 59.50/59.72      inference('cnf', [status(esa)], [d1_tsep_1])).
% 59.50/59.72  thf('359', plain,
% 59.50/59.72      ((~ (l1_pre_topc @ sk_A)
% 59.50/59.72        | (v1_tsep_1 @ sk_B @ sk_A)
% 59.50/59.72        | ((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))),
% 59.50/59.72      inference('sup-', [status(thm)], ['357', '358'])).
% 59.50/59.72  thf('360', plain, ((l1_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('361', plain,
% 59.50/59.72      (((v1_tsep_1 @ sk_B @ sk_A)
% 59.50/59.72        | ((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))),
% 59.50/59.72      inference('demod', [status(thm)], ['359', '360'])).
% 59.50/59.72  thf('362', plain,
% 59.50/59.72      ((~ (v1_tsep_1 @ sk_B @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 59.50/59.72      inference('split', [status(esa)], ['258'])).
% 59.50/59.72  thf('363', plain,
% 59.50/59.72      ((((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))
% 59.50/59.72         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 59.50/59.72      inference('sup-', [status(thm)], ['361', '362'])).
% 59.50/59.72  thf('364', plain,
% 59.50/59.72      (![X18 : $i, X19 : $i]:
% 59.50/59.72         (~ (m1_pre_topc @ X18 @ X19)
% 59.50/59.72          | ~ (v3_pre_topc @ (sk_C @ X18 @ X19) @ X19)
% 59.50/59.72          | (v1_tsep_1 @ X18 @ X19)
% 59.50/59.72          | ~ (l1_pre_topc @ X19))),
% 59.50/59.72      inference('cnf', [status(esa)], [d1_tsep_1])).
% 59.50/59.72  thf('365', plain,
% 59.50/59.72      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 59.50/59.72         | ~ (l1_pre_topc @ sk_A)
% 59.50/59.72         | (v1_tsep_1 @ sk_B @ sk_A)
% 59.50/59.72         | ~ (m1_pre_topc @ sk_B @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 59.50/59.72      inference('sup-', [status(thm)], ['363', '364'])).
% 59.50/59.72  thf('366', plain, ((l1_pre_topc @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('367', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 59.50/59.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 59.50/59.72  thf('368', plain,
% 59.50/59.72      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 59.50/59.72         | (v1_tsep_1 @ sk_B @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 59.50/59.72      inference('demod', [status(thm)], ['365', '366', '367'])).
% 59.50/59.72  thf('369', plain,
% 59.50/59.72      ((~ (v1_tsep_1 @ sk_B @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 59.50/59.72      inference('split', [status(esa)], ['258'])).
% 59.50/59.72  thf('370', plain,
% 59.50/59.72      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))
% 59.50/59.72         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 59.50/59.72      inference('clc', [status(thm)], ['368', '369'])).
% 59.50/59.72  thf('371', plain, (~ ((v1_tsep_1 @ sk_B @ sk_A))),
% 59.50/59.72      inference('sat_resolution*', [status(thm)],
% 59.50/59.72                ['259', '262', '272', '285', '298', '331'])).
% 59.50/59.72  thf('372', plain, (~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)),
% 59.50/59.72      inference('simpl_trail', [status(thm)], ['370', '371'])).
% 59.50/59.72  thf('373', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 59.50/59.72      inference('clc', [status(thm)], ['356', '372'])).
% 59.50/59.72  thf('374', plain,
% 59.50/59.72      (![X1 : $i]:
% 59.50/59.72         (~ (v1_xboole_0 @ (u1_struct_0 @ X1))
% 59.50/59.72          | ~ (l1_struct_0 @ X1)
% 59.50/59.72          | (v2_struct_0 @ X1))),
% 59.50/59.72      inference('cnf', [status(esa)], [fc2_struct_0])).
% 59.50/59.72  thf('375', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 59.50/59.72      inference('sup-', [status(thm)], ['373', '374'])).
% 59.50/59.72  thf('376', plain, ((l1_struct_0 @ sk_A)),
% 59.50/59.72      inference('sup-', [status(thm)], ['326', '327'])).
% 59.50/59.72  thf('377', plain, ((v2_struct_0 @ sk_A)),
% 59.50/59.72      inference('demod', [status(thm)], ['375', '376'])).
% 59.50/59.72  thf('378', plain, ($false), inference('demod', [status(thm)], ['0', '377'])).
% 59.50/59.72  
% 59.50/59.72  % SZS output end Refutation
% 59.50/59.72  
% 59.50/59.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
