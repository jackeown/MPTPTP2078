%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YccVxrKkCr

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:02 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  291 (7822 expanded)
%              Number of leaves         :   41 (2262 expanded)
%              Depth                    :   29
%              Number of atoms          : 3250 (209097 expanded)
%              Number of equality atoms :   73 (1133 expanded)
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

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(k7_tmap_1_type,type,(
    k7_tmap_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k5_tmap_1_type,type,(
    k5_tmap_1: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

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

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
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

thf('2',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ( v1_funct_2 @ ( k9_tmap_1 @ X25 @ X26 ) @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_tmap_1])).

thf('3',plain,
    ( ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_pre_topc @ X32 @ X33 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X32 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

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

thf('9',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( ( u1_struct_0 @ ( k6_tmap_1 @ X29 @ X28 ) )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t104_tmap_1])).

thf('10',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

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

thf('18',plain,(
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
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
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

thf('22',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ( l1_pre_topc @ ( k8_tmap_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('23',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
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
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ( v2_pre_topc @ ( k8_tmap_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('31',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
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
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ( v1_pre_topc @ ( k8_tmap_1 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_tmap_1])).

thf('39',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
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
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['19','20','28','36','44','45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','49'])).

thf('51',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['3','50','51','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(split,[status(esa)],['56'])).

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

thf('58',plain,(
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

thf('59',plain,(
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
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ( ~ ( m1_pre_topc @ sk_B @ sk_A )
      | ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','49'])).

thf('63',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('64',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','49'])).

thf('65',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(d10_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k7_tmap_1 @ A @ B )
            = ( k6_partfun1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('66',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( ( k7_tmap_1 @ X9 @ X8 )
        = ( k6_partfun1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_tmap_1])).

thf('67',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('74',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','49'])).

thf('75',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ( v1_funct_1 @ ( k9_tmap_1 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_tmap_1])).

thf('77',plain,
    ( ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['60','61','62','63','64','72','73','74','82','83','84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['55','87'])).

thf('89',plain,(
    v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('90',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','49'])).

thf('91',plain,
    ( ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(split,[status(esa)],['56'])).

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

thf('92',plain,(
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

thf('93',plain,
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
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
        | ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
        | ( v1_xboole_0 @ X0 )
        | ( v1_xboole_0 @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
        | ~ ( v1_funct_1 @ X1 )
        | ~ ( v1_funct_2 @ X1 @ X2 @ X0 )
        | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
        | ( ( k9_tmap_1 @ sk_A @ sk_B )
          = X1 )
        | ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) @ X2 @ X0 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X1 ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['90','93'])).

thf('95',plain,(
    v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('96',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','49'])).

thf('97',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','49'])).

thf('98',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
        | ( v1_xboole_0 @ X0 )
        | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( v1_funct_1 @ X1 )
        | ~ ( v1_funct_2 @ X1 @ X2 @ X0 )
        | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
        | ( ( k9_tmap_1 @ sk_A @ sk_B )
          = X1 )
        | ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ X2 @ X0 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X1 ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['94','95','96','97'])).

thf('99',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ X2 @ X1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ X0 )
        | ( ( k9_tmap_1 @ sk_A @ sk_B )
          = X0 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
        | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
        | ~ ( v1_funct_1 @ X0 )
        | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
        | ( v1_xboole_0 @ X1 ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['89','98'])).

thf('100',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( ( k9_tmap_1 @ sk_A @ sk_B )
        = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['88','99'])).

thf('101',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(dt_k7_tmap_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) )
        & ( v1_funct_2 @ ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) )
        & ( m1_subset_1 @ ( k7_tmap_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) )).

thf('102',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v1_funct_1 @ ( k7_tmap_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('103',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('110',plain,(
    v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('112',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( m1_subset_1 @ ( k7_tmap_1 @ X21 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X21 @ X22 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('113',plain,
    ( ( m1_subset_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('115',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('116',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','49'])).

thf('117',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['113','114','115','116','117','118'])).

thf('120',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('122',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k9_tmap_1 @ sk_A @ sk_B )
        = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['100','110','121'])).

thf('123',plain,
    ( ( ( ( k9_tmap_1 @ sk_A @ sk_B )
        = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('125',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v1_funct_2 @ ( k7_tmap_1 @ X21 @ X22 ) @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ ( k6_tmap_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_tmap_1])).

thf('126',plain,
    ( ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('128',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('129',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','49'])).

thf('130',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['126','127','128','129','130','131'])).

thf('133',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['132','133'])).

thf('135',plain,
    ( ( ( ( k9_tmap_1 @ sk_A @ sk_B )
        = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['123','134'])).

thf('136',plain,
    ( ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['136'])).

thf('138',plain,
    ( ( ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      & ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ) ),
    inference('sup+',[status(thm)],['135','137'])).

thf('139',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ( m1_subset_1 @ ( k9_tmap_1 @ X25 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ ( k8_tmap_1 @ X25 @ X26 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_tmap_1])).

thf('141',plain,
    ( ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','49'])).

thf('143',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['141','142','143','144'])).

thf('146',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['145','146'])).

thf('148',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','49'])).

thf('149',plain,
    ( ~ ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ~ ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
   <= ~ ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(split,[status(esa)],['149'])).

thf('151',plain,
    ( ~ ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ~ ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['148','150'])).

thf('152',plain,(
    m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['147','151'])).

thf('153',plain,(
    m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['152'])).

thf('154',plain,
    ( ( ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['138','153'])).

thf('155',plain,
    ( ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['155'])).

thf('157',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

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

thf('158',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ~ ( v1_tsep_1 @ X18 @ X19 )
      | ( X20
       != ( u1_struct_0 @ X18 ) )
      | ( v3_pre_topc @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('159',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X18 ) @ X19 )
      | ~ ( v1_tsep_1 @ X18 @ X19 )
      | ~ ( m1_pre_topc @ X18 @ X19 ) ) ),
    inference(simplify,[status(thm)],['158'])).

thf('160',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['157','159'])).

thf('161',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['160','161','162'])).

thf('164',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['156','163'])).

thf('165',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

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

thf('166',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( v3_pre_topc @ X30 @ X31 )
      | ( v5_pre_topc @ ( k7_tmap_1 @ X31 @ X30 ) @ X31 @ ( k6_tmap_1 @ X31 @ X30 ) )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t113_tmap_1])).

thf('167',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('171',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('172',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['167','168','169','170','171'])).

thf('173',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['172','173'])).

thf('175',plain,
    ( ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['164','174'])).

thf('176',plain,
    ( ( ( ( k9_tmap_1 @ sk_A @ sk_B )
        = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['123','134'])).

thf('177',plain,(
    v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('178',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','49'])).

thf('179',plain,
    ( ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference(split,[status(esa)],['56'])).

thf('180',plain,
    ( ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup+',[status(thm)],['178','179'])).

thf('181',plain,
    ( ~ ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
    | ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','49'])).

thf('183',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','49'])).

thf('184',plain,(
    v1_funct_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('185',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,
    ( ~ ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['181','182','183','184','185'])).

thf('187',plain,
    ( ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
      | ~ ( v1_funct_2 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['180','186'])).

thf('188',plain,
    ( ( ~ ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v1_tsep_1 @ sk_B @ sk_A ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['177','187'])).

thf('189',plain,
    ( ( ~ ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_tsep_1 @ sk_B @ sk_A ) )
   <= ( m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['176','188'])).

thf('190',plain,(
    m1_subset_1 @ ( k9_tmap_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['152'])).

thf('191',plain,
    ( ~ ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['189','190'])).

thf('192',plain,
    ( ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['175','191'])).

thf('193',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['155'])).

thf('194',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['192','193'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('195',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('196',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('198',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('199',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['197','198'])).

thf('200',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['196','199'])).

thf('201',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['200','201'])).

thf('203',plain,
    ( ( v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['136'])).

thf('204',plain,(
    v5_pre_topc @ ( k9_tmap_1 @ sk_A @ sk_B ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['202','203'])).

thf('205',plain,
    ( ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['154','204'])).

thf('206',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('207',plain,(
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

thf('208',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ~ ( v5_pre_topc @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_A @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v1_funct_2 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_funct_1 @ ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['206','207'])).

thf('209',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('210',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','49'])).

thf('211',plain,(
    m1_subset_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('212',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('215',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('216',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('217',plain,
    ( ( k8_tmap_1 @ sk_A @ sk_B )
    = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('218',plain,
    ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','49'])).

thf('219',plain,(
    v1_funct_2 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['132','133'])).

thf('220',plain,
    ( ( k7_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
    = ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('221',plain,(
    v1_funct_1 @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('222',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('223',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ~ ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['208','209','210','211','212','213','214','215','216','217','218','219','220','221','222'])).

thf('224',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,
    ( ~ ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['223','224'])).

thf('226',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( ( sk_C @ X18 @ X19 )
        = ( u1_struct_0 @ X18 ) )
      | ( v1_tsep_1 @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('228',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['226','227'])).

thf('229',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['228','229'])).

thf('231',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['149'])).

thf('232',plain,
    ( ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['230','231'])).

thf('233',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ~ ( v3_pre_topc @ ( sk_C @ X18 @ X19 ) @ X19 )
      | ( v1_tsep_1 @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('234',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['232','233'])).

thf('235',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('236',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['234','235','236'])).

thf('238',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['149'])).

thf('239',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['237','238'])).

thf('240',plain,(
    ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['202'])).

thf('241',plain,(
    ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['239','240'])).

thf('242',plain,(
    ~ ( v5_pre_topc @ ( k6_partfun1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['225','241'])).

thf('243',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['205','242'])).

thf('244',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('245',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['243','244'])).

thf('246',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['197','198'])).

thf('247',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['245','246'])).

thf('248',plain,(
    $false ),
    inference(demod,[status(thm)],['0','247'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YccVxrKkCr
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:18:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.46/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.66  % Solved by: fo/fo7.sh
% 0.46/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.66  % done 338 iterations in 0.207s
% 0.46/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.66  % SZS output start Refutation
% 0.46/0.66  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.66  thf(k9_tmap_1_type, type, k9_tmap_1: $i > $i > $i).
% 0.46/0.66  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 0.46/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.66  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.66  thf(k8_tmap_1_type, type, k8_tmap_1: $i > $i > $i).
% 0.46/0.66  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.66  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.46/0.66  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.66  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.46/0.66  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.46/0.66  thf(k7_tmap_1_type, type, k7_tmap_1: $i > $i > $i).
% 0.46/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.66  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.46/0.66  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.46/0.66  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.46/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.66  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.46/0.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.66  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.46/0.66  thf(k5_tmap_1_type, type, k5_tmap_1: $i > $i > $i).
% 0.46/0.66  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.46/0.66  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.46/0.66  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.46/0.66  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 0.46/0.66  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.46/0.66  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.66  thf(t122_tmap_1, conjecture,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( m1_pre_topc @ B @ A ) =>
% 0.46/0.66           ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.46/0.66             ( ( v1_funct_1 @ ( k9_tmap_1 @ A @ B ) ) & 
% 0.46/0.66               ( v1_funct_2 @
% 0.46/0.66                 ( k9_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.46/0.66                 ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 0.46/0.66               ( v5_pre_topc @
% 0.46/0.66                 ( k9_tmap_1 @ A @ B ) @ A @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.46/0.66               ( m1_subset_1 @
% 0.46/0.66                 ( k9_tmap_1 @ A @ B ) @ 
% 0.46/0.66                 ( k1_zfmisc_1 @
% 0.46/0.66                   ( k2_zfmisc_1 @
% 0.46/0.66                     ( u1_struct_0 @ A ) @ 
% 0.46/0.66                     ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.66    (~( ![A:$i]:
% 0.46/0.66        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.46/0.66            ( l1_pre_topc @ A ) ) =>
% 0.46/0.66          ( ![B:$i]:
% 0.46/0.66            ( ( m1_pre_topc @ B @ A ) =>
% 0.46/0.66              ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.46/0.66                ( ( v1_funct_1 @ ( k9_tmap_1 @ A @ B ) ) & 
% 0.46/0.66                  ( v1_funct_2 @
% 0.46/0.66                    ( k9_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.46/0.66                    ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 0.46/0.66                  ( v5_pre_topc @
% 0.46/0.66                    ( k9_tmap_1 @ A @ B ) @ A @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.46/0.66                  ( m1_subset_1 @
% 0.46/0.66                    ( k9_tmap_1 @ A @ B ) @ 
% 0.46/0.66                    ( k1_zfmisc_1 @
% 0.46/0.66                      ( k2_zfmisc_1 @
% 0.46/0.66                        ( u1_struct_0 @ A ) @ 
% 0.46/0.66                        ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) ) )),
% 0.46/0.66    inference('cnf.neg', [status(esa)], [t122_tmap_1])).
% 0.46/0.66  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('1', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(dt_k9_tmap_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.46/0.66         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.46/0.66       ( ( v1_funct_1 @ ( k9_tmap_1 @ A @ B ) ) & 
% 0.46/0.66         ( v1_funct_2 @
% 0.46/0.66           ( k9_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.46/0.66           ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 0.46/0.66         ( m1_subset_1 @
% 0.46/0.66           ( k9_tmap_1 @ A @ B ) @ 
% 0.46/0.66           ( k1_zfmisc_1 @
% 0.46/0.66             ( k2_zfmisc_1 @
% 0.46/0.66               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) ))).
% 0.46/0.66  thf('2', plain,
% 0.46/0.66      (![X25 : $i, X26 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X25)
% 0.46/0.66          | ~ (v2_pre_topc @ X25)
% 0.46/0.66          | (v2_struct_0 @ X25)
% 0.46/0.66          | ~ (m1_pre_topc @ X26 @ X25)
% 0.46/0.66          | (v1_funct_2 @ (k9_tmap_1 @ X25 @ X26) @ (u1_struct_0 @ X25) @ 
% 0.46/0.66             (u1_struct_0 @ (k8_tmap_1 @ X25 @ X26))))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_k9_tmap_1])).
% 0.46/0.66  thf('3', plain,
% 0.46/0.66      (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66         (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.46/0.66        | (v2_struct_0 @ sk_A)
% 0.46/0.66        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.66        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.66  thf('4', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(t1_tsep_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( l1_pre_topc @ A ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( m1_pre_topc @ B @ A ) =>
% 0.46/0.66           ( m1_subset_1 @
% 0.46/0.66             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.46/0.66  thf('5', plain,
% 0.46/0.66      (![X32 : $i, X33 : $i]:
% 0.46/0.66         (~ (m1_pre_topc @ X32 @ X33)
% 0.46/0.66          | (m1_subset_1 @ (u1_struct_0 @ X32) @ 
% 0.46/0.66             (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.46/0.66          | ~ (l1_pre_topc @ X33))),
% 0.46/0.66      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.46/0.66  thf('6', plain,
% 0.46/0.66      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.66        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.66           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['4', '5'])).
% 0.46/0.66  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('8', plain,
% 0.46/0.66      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['6', '7'])).
% 0.46/0.66  thf(t104_tmap_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66           ( ( ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) = ( u1_struct_0 @ A ) ) & 
% 0.46/0.66             ( ( u1_pre_topc @ ( k6_tmap_1 @ A @ B ) ) = ( k5_tmap_1 @ A @ B ) ) ) ) ) ))).
% 0.46/0.66  thf('9', plain,
% 0.46/0.66      (![X28 : $i, X29 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.46/0.66          | ((u1_struct_0 @ (k6_tmap_1 @ X29 @ X28)) = (u1_struct_0 @ X29))
% 0.46/0.66          | ~ (l1_pre_topc @ X29)
% 0.46/0.66          | ~ (v2_pre_topc @ X29)
% 0.46/0.66          | (v2_struct_0 @ X29))),
% 0.46/0.66      inference('cnf', [status(esa)], [t104_tmap_1])).
% 0.46/0.66  thf('10', plain,
% 0.46/0.66      (((v2_struct_0 @ sk_A)
% 0.46/0.66        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.66        | ~ (l1_pre_topc @ sk_A)
% 0.46/0.66        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.46/0.66            = (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['8', '9'])).
% 0.46/0.66  thf('11', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('13', plain,
% 0.46/0.66      (((v2_struct_0 @ sk_A)
% 0.46/0.66        | ((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.46/0.66            = (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.46/0.66  thf('14', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('15', plain,
% 0.46/0.66      (((u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.46/0.66         = (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('clc', [status(thm)], ['13', '14'])).
% 0.46/0.66  thf('16', plain,
% 0.46/0.66      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['6', '7'])).
% 0.46/0.66  thf(d11_tmap_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( m1_pre_topc @ B @ A ) =>
% 0.46/0.66           ( ![C:$i]:
% 0.46/0.66             ( ( ( v1_pre_topc @ C ) & ( v2_pre_topc @ C ) & 
% 0.46/0.66                 ( l1_pre_topc @ C ) ) =>
% 0.46/0.66               ( ( ( C ) = ( k8_tmap_1 @ A @ B ) ) <=>
% 0.46/0.66                 ( ![D:$i]:
% 0.46/0.66                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66                     ( ( ( D ) = ( u1_struct_0 @ B ) ) =>
% 0.46/0.66                       ( ( C ) = ( k6_tmap_1 @ A @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.66  thf('17', plain,
% 0.46/0.66      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.46/0.66         (~ (m1_pre_topc @ X10 @ X11)
% 0.46/0.66          | ((X12) != (k8_tmap_1 @ X11 @ X10))
% 0.46/0.66          | ((X13) != (u1_struct_0 @ X10))
% 0.46/0.66          | ((X12) = (k6_tmap_1 @ X11 @ X13))
% 0.46/0.66          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.46/0.66          | ~ (l1_pre_topc @ X12)
% 0.46/0.66          | ~ (v2_pre_topc @ X12)
% 0.46/0.66          | ~ (v1_pre_topc @ X12)
% 0.46/0.66          | ~ (l1_pre_topc @ X11)
% 0.46/0.66          | ~ (v2_pre_topc @ X11)
% 0.46/0.66          | (v2_struct_0 @ X11))),
% 0.46/0.66      inference('cnf', [status(esa)], [d11_tmap_1])).
% 0.46/0.66  thf('18', plain,
% 0.46/0.66      (![X10 : $i, X11 : $i]:
% 0.46/0.66         ((v2_struct_0 @ X11)
% 0.46/0.66          | ~ (v2_pre_topc @ X11)
% 0.46/0.66          | ~ (l1_pre_topc @ X11)
% 0.46/0.66          | ~ (v1_pre_topc @ (k8_tmap_1 @ X11 @ X10))
% 0.46/0.66          | ~ (v2_pre_topc @ (k8_tmap_1 @ X11 @ X10))
% 0.46/0.66          | ~ (l1_pre_topc @ (k8_tmap_1 @ X11 @ X10))
% 0.46/0.66          | ~ (m1_subset_1 @ (u1_struct_0 @ X10) @ 
% 0.46/0.66               (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.46/0.66          | ((k8_tmap_1 @ X11 @ X10) = (k6_tmap_1 @ X11 @ (u1_struct_0 @ X10)))
% 0.46/0.66          | ~ (m1_pre_topc @ X10 @ X11))),
% 0.46/0.66      inference('simplify', [status(thm)], ['17'])).
% 0.46/0.66  thf('19', plain,
% 0.46/0.66      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.46/0.66        | ((k8_tmap_1 @ sk_A @ sk_B)
% 0.46/0.66            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.46/0.66        | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.46/0.66        | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.46/0.66        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.46/0.66        | ~ (l1_pre_topc @ sk_A)
% 0.46/0.66        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.66        | (v2_struct_0 @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['16', '18'])).
% 0.46/0.66  thf('20', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('21', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(dt_k8_tmap_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.46/0.66         ( l1_pre_topc @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.46/0.66       ( ( v1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.46/0.66         ( v2_pre_topc @ ( k8_tmap_1 @ A @ B ) ) & 
% 0.46/0.66         ( l1_pre_topc @ ( k8_tmap_1 @ A @ B ) ) ) ))).
% 0.46/0.66  thf('22', plain,
% 0.46/0.66      (![X23 : $i, X24 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X23)
% 0.46/0.66          | ~ (v2_pre_topc @ X23)
% 0.46/0.66          | (v2_struct_0 @ X23)
% 0.46/0.66          | ~ (m1_pre_topc @ X24 @ X23)
% 0.46/0.66          | (l1_pre_topc @ (k8_tmap_1 @ X23 @ X24)))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.46/0.66  thf('23', plain,
% 0.46/0.66      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.46/0.66        | (v2_struct_0 @ sk_A)
% 0.46/0.66        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.66        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['21', '22'])).
% 0.46/0.66  thf('24', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('26', plain,
% 0.46/0.66      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.46/0.66  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('28', plain, ((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.46/0.66      inference('clc', [status(thm)], ['26', '27'])).
% 0.46/0.66  thf('29', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('30', plain,
% 0.46/0.66      (![X23 : $i, X24 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X23)
% 0.46/0.66          | ~ (v2_pre_topc @ X23)
% 0.46/0.66          | (v2_struct_0 @ X23)
% 0.46/0.66          | ~ (m1_pre_topc @ X24 @ X23)
% 0.46/0.66          | (v2_pre_topc @ (k8_tmap_1 @ X23 @ X24)))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.46/0.66  thf('31', plain,
% 0.46/0.66      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.46/0.66        | (v2_struct_0 @ sk_A)
% 0.46/0.66        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.66        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['29', '30'])).
% 0.46/0.66  thf('32', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('34', plain,
% 0.46/0.66      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.46/0.66  thf('35', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('36', plain, ((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.46/0.66      inference('clc', [status(thm)], ['34', '35'])).
% 0.46/0.66  thf('37', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('38', plain,
% 0.46/0.66      (![X23 : $i, X24 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X23)
% 0.46/0.66          | ~ (v2_pre_topc @ X23)
% 0.46/0.66          | (v2_struct_0 @ X23)
% 0.46/0.66          | ~ (m1_pre_topc @ X24 @ X23)
% 0.46/0.66          | (v1_pre_topc @ (k8_tmap_1 @ X23 @ X24)))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_k8_tmap_1])).
% 0.46/0.66  thf('39', plain,
% 0.46/0.66      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 0.46/0.66        | (v2_struct_0 @ sk_A)
% 0.46/0.66        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.66        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['37', '38'])).
% 0.46/0.66  thf('40', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('42', plain,
% 0.46/0.66      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.46/0.66  thf('43', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('44', plain, ((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))),
% 0.46/0.66      inference('clc', [status(thm)], ['42', '43'])).
% 0.46/0.66  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('46', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('47', plain,
% 0.46/0.66      ((((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.46/0.66        | (v2_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)],
% 0.46/0.66                ['19', '20', '28', '36', '44', '45', '46'])).
% 0.46/0.66  thf('48', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('49', plain,
% 0.46/0.66      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.46/0.66      inference('clc', [status(thm)], ['47', '48'])).
% 0.46/0.66  thf('50', plain,
% 0.46/0.66      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['15', '49'])).
% 0.46/0.66  thf('51', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('53', plain,
% 0.46/0.66      (((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66         (u1_struct_0 @ sk_A))
% 0.46/0.66        | (v2_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['3', '50', '51', '52'])).
% 0.46/0.66  thf('54', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('55', plain,
% 0.46/0.66      ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66        (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('clc', [status(thm)], ['53', '54'])).
% 0.46/0.66  thf('56', plain,
% 0.46/0.66      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.46/0.66         (k1_zfmisc_1 @ 
% 0.46/0.66          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))
% 0.46/0.66        | (v1_tsep_1 @ sk_B @ sk_A))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('57', plain,
% 0.46/0.66      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.46/0.66         (k1_zfmisc_1 @ 
% 0.46/0.66          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))))
% 0.46/0.66         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.46/0.66               (k1_zfmisc_1 @ 
% 0.46/0.66                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.46/0.66      inference('split', [status(esa)], ['56'])).
% 0.46/0.66  thf(d12_tmap_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( m1_pre_topc @ B @ A ) =>
% 0.46/0.66           ( ![C:$i]:
% 0.46/0.66             ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.66                 ( v1_funct_2 @
% 0.46/0.66                   C @ ( u1_struct_0 @ A ) @ 
% 0.46/0.66                   ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) & 
% 0.46/0.66                 ( m1_subset_1 @
% 0.46/0.66                   C @ 
% 0.46/0.66                   ( k1_zfmisc_1 @
% 0.46/0.66                     ( k2_zfmisc_1 @
% 0.46/0.66                       ( u1_struct_0 @ A ) @ 
% 0.46/0.66                       ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) ) ) ) ) =>
% 0.46/0.66               ( ( ( C ) = ( k9_tmap_1 @ A @ B ) ) <=>
% 0.46/0.66                 ( ![D:$i]:
% 0.46/0.66                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66                     ( ( ( D ) = ( u1_struct_0 @ B ) ) =>
% 0.46/0.66                       ( r1_funct_2 @
% 0.46/0.66                         ( u1_struct_0 @ A ) @ 
% 0.46/0.66                         ( u1_struct_0 @ ( k8_tmap_1 @ A @ B ) ) @ 
% 0.46/0.66                         ( u1_struct_0 @ A ) @ 
% 0.46/0.66                         ( u1_struct_0 @ ( k6_tmap_1 @ A @ D ) ) @ C @ 
% 0.46/0.66                         ( k7_tmap_1 @ A @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.66  thf('58', plain,
% 0.46/0.66      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.46/0.66         (~ (m1_pre_topc @ X14 @ X15)
% 0.46/0.66          | ((X16) != (k9_tmap_1 @ X15 @ X14))
% 0.46/0.66          | ((X17) != (u1_struct_0 @ X14))
% 0.46/0.66          | (r1_funct_2 @ (u1_struct_0 @ X15) @ 
% 0.46/0.66             (u1_struct_0 @ (k8_tmap_1 @ X15 @ X14)) @ (u1_struct_0 @ X15) @ 
% 0.46/0.66             (u1_struct_0 @ (k6_tmap_1 @ X15 @ X17)) @ X16 @ 
% 0.46/0.66             (k7_tmap_1 @ X15 @ X17))
% 0.46/0.66          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.46/0.66          | ~ (m1_subset_1 @ X16 @ 
% 0.46/0.66               (k1_zfmisc_1 @ 
% 0.46/0.66                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ 
% 0.46/0.66                 (u1_struct_0 @ (k8_tmap_1 @ X15 @ X14)))))
% 0.46/0.66          | ~ (v1_funct_2 @ X16 @ (u1_struct_0 @ X15) @ 
% 0.46/0.66               (u1_struct_0 @ (k8_tmap_1 @ X15 @ X14)))
% 0.46/0.66          | ~ (v1_funct_1 @ X16)
% 0.46/0.66          | ~ (l1_pre_topc @ X15)
% 0.46/0.66          | ~ (v2_pre_topc @ X15)
% 0.46/0.66          | (v2_struct_0 @ X15))),
% 0.46/0.66      inference('cnf', [status(esa)], [d12_tmap_1])).
% 0.46/0.66  thf('59', plain,
% 0.46/0.66      (![X14 : $i, X15 : $i]:
% 0.46/0.66         ((v2_struct_0 @ X15)
% 0.46/0.66          | ~ (v2_pre_topc @ X15)
% 0.46/0.66          | ~ (l1_pre_topc @ X15)
% 0.46/0.66          | ~ (v1_funct_1 @ (k9_tmap_1 @ X15 @ X14))
% 0.46/0.66          | ~ (v1_funct_2 @ (k9_tmap_1 @ X15 @ X14) @ (u1_struct_0 @ X15) @ 
% 0.46/0.66               (u1_struct_0 @ (k8_tmap_1 @ X15 @ X14)))
% 0.46/0.66          | ~ (m1_subset_1 @ (k9_tmap_1 @ X15 @ X14) @ 
% 0.46/0.66               (k1_zfmisc_1 @ 
% 0.46/0.66                (k2_zfmisc_1 @ (u1_struct_0 @ X15) @ 
% 0.46/0.66                 (u1_struct_0 @ (k8_tmap_1 @ X15 @ X14)))))
% 0.46/0.66          | ~ (m1_subset_1 @ (u1_struct_0 @ X14) @ 
% 0.46/0.66               (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.46/0.66          | (r1_funct_2 @ (u1_struct_0 @ X15) @ 
% 0.46/0.66             (u1_struct_0 @ (k8_tmap_1 @ X15 @ X14)) @ (u1_struct_0 @ X15) @ 
% 0.46/0.66             (u1_struct_0 @ (k6_tmap_1 @ X15 @ (u1_struct_0 @ X14))) @ 
% 0.46/0.66             (k9_tmap_1 @ X15 @ X14) @ (k7_tmap_1 @ X15 @ (u1_struct_0 @ X14)))
% 0.46/0.66          | ~ (m1_pre_topc @ X14 @ X15))),
% 0.46/0.66      inference('simplify', [status(thm)], ['58'])).
% 0.46/0.66  thf('60', plain,
% 0.46/0.66      (((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.46/0.66         | (r1_funct_2 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66            (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66            (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))) @ 
% 0.46/0.66            (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.46/0.66            (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.46/0.66         | ~ (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.66              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.66         | ~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66              (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.46/0.66         | ~ (v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))
% 0.46/0.66         | ~ (l1_pre_topc @ sk_A)
% 0.46/0.66         | ~ (v2_pre_topc @ sk_A)
% 0.46/0.66         | (v2_struct_0 @ sk_A)))
% 0.46/0.66         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.46/0.66               (k1_zfmisc_1 @ 
% 0.46/0.66                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['57', '59'])).
% 0.46/0.66  thf('61', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('62', plain,
% 0.46/0.66      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['15', '49'])).
% 0.46/0.66  thf('63', plain,
% 0.46/0.66      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.46/0.66      inference('clc', [status(thm)], ['47', '48'])).
% 0.46/0.66  thf('64', plain,
% 0.46/0.66      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['15', '49'])).
% 0.46/0.66  thf('65', plain,
% 0.46/0.66      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['6', '7'])).
% 0.46/0.66  thf(d10_tmap_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66           ( ( k7_tmap_1 @ A @ B ) = ( k6_partfun1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.46/0.66  thf('66', plain,
% 0.46/0.66      (![X8 : $i, X9 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.46/0.66          | ((k7_tmap_1 @ X9 @ X8) = (k6_partfun1 @ (u1_struct_0 @ X9)))
% 0.46/0.66          | ~ (l1_pre_topc @ X9)
% 0.46/0.66          | ~ (v2_pre_topc @ X9)
% 0.46/0.66          | (v2_struct_0 @ X9))),
% 0.46/0.66      inference('cnf', [status(esa)], [d10_tmap_1])).
% 0.46/0.66  thf('67', plain,
% 0.46/0.66      (((v2_struct_0 @ sk_A)
% 0.46/0.66        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.66        | ~ (l1_pre_topc @ sk_A)
% 0.46/0.66        | ((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.46/0.66            = (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['65', '66'])).
% 0.46/0.66  thf('68', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('70', plain,
% 0.46/0.66      (((v2_struct_0 @ sk_A)
% 0.46/0.66        | ((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.46/0.66            = (k6_partfun1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.66      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.46/0.66  thf('71', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('72', plain,
% 0.46/0.66      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.46/0.66         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('clc', [status(thm)], ['70', '71'])).
% 0.46/0.66  thf('73', plain,
% 0.46/0.66      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['6', '7'])).
% 0.46/0.66  thf('74', plain,
% 0.46/0.66      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['15', '49'])).
% 0.46/0.66  thf('75', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('76', plain,
% 0.46/0.66      (![X25 : $i, X26 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X25)
% 0.46/0.66          | ~ (v2_pre_topc @ X25)
% 0.46/0.66          | (v2_struct_0 @ X25)
% 0.46/0.66          | ~ (m1_pre_topc @ X26 @ X25)
% 0.46/0.66          | (v1_funct_1 @ (k9_tmap_1 @ X25 @ X26)))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_k9_tmap_1])).
% 0.46/0.66  thf('77', plain,
% 0.46/0.66      (((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))
% 0.46/0.66        | (v2_struct_0 @ sk_A)
% 0.46/0.66        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.66        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['75', '76'])).
% 0.46/0.66  thf('78', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('79', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('80', plain,
% 0.46/0.66      (((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.46/0.66  thf('81', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('82', plain, ((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))),
% 0.46/0.66      inference('clc', [status(thm)], ['80', '81'])).
% 0.46/0.66  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('84', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('85', plain,
% 0.46/0.66      ((((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66          (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66          (k9_tmap_1 @ sk_A @ sk_B) @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.66         | ~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66              (u1_struct_0 @ sk_A))
% 0.46/0.66         | (v2_struct_0 @ sk_A)))
% 0.46/0.66         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.46/0.66               (k1_zfmisc_1 @ 
% 0.46/0.66                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.46/0.66      inference('demod', [status(thm)],
% 0.46/0.66                ['60', '61', '62', '63', '64', '72', '73', '74', '82', '83', 
% 0.46/0.66                 '84'])).
% 0.46/0.66  thf('86', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('87', plain,
% 0.46/0.66      (((~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66            (u1_struct_0 @ sk_A))
% 0.46/0.66         | (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66            (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66            (k9_tmap_1 @ sk_A @ sk_B) @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))))
% 0.46/0.66         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.46/0.66               (k1_zfmisc_1 @ 
% 0.46/0.66                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.46/0.66      inference('clc', [status(thm)], ['85', '86'])).
% 0.46/0.66  thf('88', plain,
% 0.46/0.66      (((r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66         (k9_tmap_1 @ sk_A @ sk_B) @ (k6_partfun1 @ (u1_struct_0 @ sk_A))))
% 0.46/0.66         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.46/0.66               (k1_zfmisc_1 @ 
% 0.46/0.66                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['55', '87'])).
% 0.46/0.66  thf('89', plain,
% 0.46/0.66      ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66        (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('clc', [status(thm)], ['53', '54'])).
% 0.46/0.66  thf('90', plain,
% 0.46/0.66      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['15', '49'])).
% 0.46/0.66  thf('91', plain,
% 0.46/0.66      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.46/0.66         (k1_zfmisc_1 @ 
% 0.46/0.66          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))))
% 0.46/0.66         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.46/0.66               (k1_zfmisc_1 @ 
% 0.46/0.66                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.46/0.66      inference('split', [status(esa)], ['56'])).
% 0.46/0.66  thf(redefinition_r1_funct_2, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.46/0.66     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 0.46/0.66         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 0.46/0.66         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.46/0.66         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 0.46/0.66         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.46/0.66       ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F ) <=> ( ( E ) = ( F ) ) ) ))).
% 0.46/0.66  thf('92', plain,
% 0.46/0.66      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4)))
% 0.46/0.66          | ~ (v1_funct_2 @ X2 @ X3 @ X4)
% 0.46/0.66          | ~ (v1_funct_1 @ X2)
% 0.46/0.66          | (v1_xboole_0 @ X5)
% 0.46/0.66          | (v1_xboole_0 @ X4)
% 0.46/0.66          | ~ (v1_funct_1 @ X6)
% 0.46/0.66          | ~ (v1_funct_2 @ X6 @ X7 @ X5)
% 0.46/0.66          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X5)))
% 0.46/0.66          | ((X2) = (X6))
% 0.46/0.66          | ~ (r1_funct_2 @ X3 @ X4 @ X7 @ X5 @ X2 @ X6))),
% 0.46/0.66      inference('cnf', [status(esa)], [redefinition_r1_funct_2])).
% 0.46/0.66  thf('93', plain,
% 0.46/0.66      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.66          (~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66              (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) @ X2 @ X1 @ 
% 0.46/0.66              (k9_tmap_1 @ sk_A @ sk_B) @ X0)
% 0.46/0.66           | ((k9_tmap_1 @ sk_A @ sk_B) = (X0))
% 0.46/0.66           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.46/0.66           | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 0.46/0.66           | ~ (v1_funct_1 @ X0)
% 0.46/0.66           | (v1_xboole_0 @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.46/0.66           | (v1_xboole_0 @ X1)
% 0.46/0.66           | ~ (v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))
% 0.46/0.66           | ~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.46/0.66                (u1_struct_0 @ sk_A) @ 
% 0.46/0.66                (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))
% 0.46/0.66         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.46/0.66               (k1_zfmisc_1 @ 
% 0.46/0.66                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['91', '92'])).
% 0.46/0.66  thf('94', plain,
% 0.46/0.66      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.66          (~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66              (u1_struct_0 @ sk_A))
% 0.46/0.66           | ~ (v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))
% 0.46/0.66           | (v1_xboole_0 @ X0)
% 0.46/0.66           | (v1_xboole_0 @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.46/0.66           | ~ (v1_funct_1 @ X1)
% 0.46/0.66           | ~ (v1_funct_2 @ X1 @ X2 @ X0)
% 0.46/0.66           | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.46/0.66           | ((k9_tmap_1 @ sk_A @ sk_B) = (X1))
% 0.46/0.66           | ~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66                (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) @ X2 @ X0 @ 
% 0.46/0.66                (k9_tmap_1 @ sk_A @ sk_B) @ X1)))
% 0.46/0.66         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.46/0.66               (k1_zfmisc_1 @ 
% 0.46/0.66                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['90', '93'])).
% 0.46/0.66  thf('95', plain, ((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))),
% 0.46/0.66      inference('clc', [status(thm)], ['80', '81'])).
% 0.46/0.66  thf('96', plain,
% 0.46/0.66      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['15', '49'])).
% 0.46/0.66  thf('97', plain,
% 0.46/0.66      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['15', '49'])).
% 0.46/0.66  thf('98', plain,
% 0.46/0.66      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.66          (~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66              (u1_struct_0 @ sk_A))
% 0.46/0.66           | (v1_xboole_0 @ X0)
% 0.46/0.66           | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.66           | ~ (v1_funct_1 @ X1)
% 0.46/0.66           | ~ (v1_funct_2 @ X1 @ X2 @ X0)
% 0.46/0.66           | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.46/0.66           | ((k9_tmap_1 @ sk_A @ sk_B) = (X1))
% 0.46/0.66           | ~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66                X2 @ X0 @ (k9_tmap_1 @ sk_A @ sk_B) @ X1)))
% 0.46/0.66         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.46/0.66               (k1_zfmisc_1 @ 
% 0.46/0.66                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.46/0.66      inference('demod', [status(thm)], ['94', '95', '96', '97'])).
% 0.46/0.66  thf('99', plain,
% 0.46/0.66      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.66          (~ (r1_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ X2 @ 
% 0.46/0.66              X1 @ (k9_tmap_1 @ sk_A @ sk_B) @ X0)
% 0.46/0.66           | ((k9_tmap_1 @ sk_A @ sk_B) = (X0))
% 0.46/0.66           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.46/0.66           | ~ (v1_funct_2 @ X0 @ X2 @ X1)
% 0.46/0.66           | ~ (v1_funct_1 @ X0)
% 0.46/0.66           | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.66           | (v1_xboole_0 @ X1)))
% 0.46/0.66         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.46/0.66               (k1_zfmisc_1 @ 
% 0.46/0.66                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['89', '98'])).
% 0.46/0.66  thf('100', plain,
% 0.46/0.66      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.66         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.66         | ~ (v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.66         | ~ (v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.46/0.66              (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.46/0.66         | ~ (m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.46/0.66              (k1_zfmisc_1 @ 
% 0.46/0.66               (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.46/0.66         | ((k9_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))))
% 0.46/0.66         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.46/0.66               (k1_zfmisc_1 @ 
% 0.46/0.66                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['88', '99'])).
% 0.46/0.66  thf('101', plain,
% 0.46/0.66      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['6', '7'])).
% 0.46/0.66  thf(dt_k7_tmap_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.46/0.66         ( l1_pre_topc @ A ) & 
% 0.46/0.66         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.66       ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) ) & 
% 0.46/0.66         ( v1_funct_2 @
% 0.46/0.66           ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.46/0.66           ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 0.46/0.66         ( m1_subset_1 @
% 0.46/0.66           ( k7_tmap_1 @ A @ B ) @ 
% 0.46/0.66           ( k1_zfmisc_1 @
% 0.46/0.66             ( k2_zfmisc_1 @
% 0.46/0.66               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ))).
% 0.46/0.66  thf('102', plain,
% 0.46/0.66      (![X21 : $i, X22 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X21)
% 0.46/0.66          | ~ (v2_pre_topc @ X21)
% 0.46/0.66          | (v2_struct_0 @ X21)
% 0.46/0.66          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.46/0.66          | (v1_funct_1 @ (k7_tmap_1 @ X21 @ X22)))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.46/0.66  thf('103', plain,
% 0.46/0.66      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.46/0.66        | (v2_struct_0 @ sk_A)
% 0.46/0.66        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.66        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['101', '102'])).
% 0.46/0.66  thf('104', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('105', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('106', plain,
% 0.46/0.66      (((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.46/0.66        | (v2_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['103', '104', '105'])).
% 0.46/0.66  thf('107', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('108', plain, ((v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.46/0.66      inference('clc', [status(thm)], ['106', '107'])).
% 0.46/0.66  thf('109', plain,
% 0.46/0.66      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.46/0.66         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('clc', [status(thm)], ['70', '71'])).
% 0.46/0.66  thf('110', plain, ((v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['108', '109'])).
% 0.46/0.66  thf('111', plain,
% 0.46/0.66      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['6', '7'])).
% 0.46/0.66  thf('112', plain,
% 0.46/0.66      (![X21 : $i, X22 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X21)
% 0.46/0.66          | ~ (v2_pre_topc @ X21)
% 0.46/0.66          | (v2_struct_0 @ X21)
% 0.46/0.66          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.46/0.66          | (m1_subset_1 @ (k7_tmap_1 @ X21 @ X22) @ 
% 0.46/0.66             (k1_zfmisc_1 @ 
% 0.46/0.66              (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ 
% 0.46/0.66               (u1_struct_0 @ (k6_tmap_1 @ X21 @ X22))))))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.46/0.66  thf('113', plain,
% 0.46/0.66      (((m1_subset_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.46/0.66         (k1_zfmisc_1 @ 
% 0.46/0.66          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66           (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))))
% 0.46/0.66        | (v2_struct_0 @ sk_A)
% 0.46/0.66        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.66        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['111', '112'])).
% 0.46/0.66  thf('114', plain,
% 0.46/0.66      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.46/0.66         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('clc', [status(thm)], ['70', '71'])).
% 0.46/0.66  thf('115', plain,
% 0.46/0.66      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.46/0.66      inference('clc', [status(thm)], ['47', '48'])).
% 0.46/0.66  thf('116', plain,
% 0.46/0.66      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['15', '49'])).
% 0.46/0.66  thf('117', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('118', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('119', plain,
% 0.46/0.66      (((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.46/0.66         (k1_zfmisc_1 @ 
% 0.46/0.66          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.46/0.66        | (v2_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)],
% 0.46/0.66                ['113', '114', '115', '116', '117', '118'])).
% 0.46/0.66  thf('120', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('121', plain,
% 0.46/0.66      ((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.46/0.66        (k1_zfmisc_1 @ 
% 0.46/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 0.46/0.66      inference('clc', [status(thm)], ['119', '120'])).
% 0.46/0.66  thf('122', plain,
% 0.46/0.66      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.66         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.66         | ~ (v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.46/0.66              (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.46/0.66         | ((k9_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))))
% 0.46/0.66         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.46/0.66               (k1_zfmisc_1 @ 
% 0.46/0.66                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.46/0.66      inference('demod', [status(thm)], ['100', '110', '121'])).
% 0.46/0.66  thf('123', plain,
% 0.46/0.66      (((((k9_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.66         | ~ (v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.46/0.66              (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.46/0.66         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.46/0.66         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.46/0.66               (k1_zfmisc_1 @ 
% 0.46/0.66                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.46/0.66      inference('simplify', [status(thm)], ['122'])).
% 0.46/0.66  thf('124', plain,
% 0.46/0.66      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['6', '7'])).
% 0.46/0.66  thf('125', plain,
% 0.46/0.66      (![X21 : $i, X22 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X21)
% 0.46/0.66          | ~ (v2_pre_topc @ X21)
% 0.46/0.66          | (v2_struct_0 @ X21)
% 0.46/0.66          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.46/0.66          | (v1_funct_2 @ (k7_tmap_1 @ X21 @ X22) @ (u1_struct_0 @ X21) @ 
% 0.46/0.66             (u1_struct_0 @ (k6_tmap_1 @ X21 @ X22))))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_k7_tmap_1])).
% 0.46/0.66  thf('126', plain,
% 0.46/0.66      (((v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.46/0.66         (u1_struct_0 @ sk_A) @ 
% 0.46/0.66         (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))
% 0.46/0.66        | (v2_struct_0 @ sk_A)
% 0.46/0.66        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.66        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['124', '125'])).
% 0.46/0.66  thf('127', plain,
% 0.46/0.66      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.46/0.66         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('clc', [status(thm)], ['70', '71'])).
% 0.46/0.66  thf('128', plain,
% 0.46/0.66      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.46/0.66      inference('clc', [status(thm)], ['47', '48'])).
% 0.46/0.66  thf('129', plain,
% 0.46/0.66      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['15', '49'])).
% 0.46/0.66  thf('130', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('131', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('132', plain,
% 0.46/0.66      (((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.46/0.66         (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.46/0.66        | (v2_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)],
% 0.46/0.66                ['126', '127', '128', '129', '130', '131'])).
% 0.46/0.66  thf('133', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('134', plain,
% 0.46/0.66      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.46/0.66        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('clc', [status(thm)], ['132', '133'])).
% 0.46/0.66  thf('135', plain,
% 0.46/0.66      (((((k9_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.66         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.46/0.66         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.46/0.66               (k1_zfmisc_1 @ 
% 0.46/0.66                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.46/0.66      inference('demod', [status(thm)], ['123', '134'])).
% 0.46/0.66  thf('136', plain,
% 0.46/0.66      (((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.46/0.66         (k8_tmap_1 @ sk_A @ sk_B))
% 0.46/0.66        | (v1_tsep_1 @ sk_B @ sk_A))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('137', plain,
% 0.46/0.66      (((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.46/0.66         (k8_tmap_1 @ sk_A @ sk_B)))
% 0.46/0.66         <= (((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.46/0.66               (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.46/0.66      inference('split', [status(esa)], ['136'])).
% 0.46/0.66  thf('138', plain,
% 0.46/0.66      ((((v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 0.46/0.66          (k8_tmap_1 @ sk_A @ sk_B))
% 0.46/0.66         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.46/0.66         <= (((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.46/0.66               (k8_tmap_1 @ sk_A @ sk_B))) & 
% 0.46/0.66             ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.46/0.66               (k1_zfmisc_1 @ 
% 0.46/0.66                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.46/0.66      inference('sup+', [status(thm)], ['135', '137'])).
% 0.46/0.66  thf('139', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('140', plain,
% 0.46/0.66      (![X25 : $i, X26 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X25)
% 0.46/0.66          | ~ (v2_pre_topc @ X25)
% 0.46/0.66          | (v2_struct_0 @ X25)
% 0.46/0.66          | ~ (m1_pre_topc @ X26 @ X25)
% 0.46/0.66          | (m1_subset_1 @ (k9_tmap_1 @ X25 @ X26) @ 
% 0.46/0.66             (k1_zfmisc_1 @ 
% 0.46/0.66              (k2_zfmisc_1 @ (u1_struct_0 @ X25) @ 
% 0.46/0.66               (u1_struct_0 @ (k8_tmap_1 @ X25 @ X26))))))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_k9_tmap_1])).
% 0.46/0.66  thf('141', plain,
% 0.46/0.66      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.46/0.66         (k1_zfmisc_1 @ 
% 0.46/0.66          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))
% 0.46/0.66        | (v2_struct_0 @ sk_A)
% 0.46/0.66        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.66        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['139', '140'])).
% 0.46/0.66  thf('142', plain,
% 0.46/0.66      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['15', '49'])).
% 0.46/0.66  thf('143', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('144', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('145', plain,
% 0.46/0.66      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.46/0.66         (k1_zfmisc_1 @ 
% 0.46/0.66          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.46/0.66        | (v2_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['141', '142', '143', '144'])).
% 0.46/0.66  thf('146', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('147', plain,
% 0.46/0.66      ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.46/0.66        (k1_zfmisc_1 @ 
% 0.46/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 0.46/0.66      inference('clc', [status(thm)], ['145', '146'])).
% 0.46/0.66  thf('148', plain,
% 0.46/0.66      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['15', '49'])).
% 0.46/0.66  thf('149', plain,
% 0.46/0.66      ((~ (m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.46/0.66           (k1_zfmisc_1 @ 
% 0.46/0.66            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))
% 0.46/0.66        | ~ (v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.46/0.66             (k8_tmap_1 @ sk_A @ sk_B))
% 0.46/0.66        | ~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.46/0.66        | ~ (v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))
% 0.46/0.66        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.46/0.66        | ~ (v1_tsep_1 @ sk_B @ sk_A))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('150', plain,
% 0.46/0.66      ((~ (m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.46/0.66           (k1_zfmisc_1 @ 
% 0.46/0.66            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))))
% 0.46/0.66         <= (~
% 0.46/0.66             ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.46/0.66               (k1_zfmisc_1 @ 
% 0.46/0.66                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.46/0.66      inference('split', [status(esa)], ['149'])).
% 0.46/0.66  thf('151', plain,
% 0.46/0.66      ((~ (m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.46/0.66           (k1_zfmisc_1 @ 
% 0.46/0.66            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))
% 0.46/0.66         <= (~
% 0.46/0.66             ((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.46/0.66               (k1_zfmisc_1 @ 
% 0.46/0.66                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['148', '150'])).
% 0.46/0.66  thf('152', plain,
% 0.46/0.66      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.46/0.66         (k1_zfmisc_1 @ 
% 0.46/0.66          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['147', '151'])).
% 0.46/0.66  thf('153', plain,
% 0.46/0.66      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.46/0.66         (k1_zfmisc_1 @ 
% 0.46/0.66          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))))),
% 0.46/0.66      inference('sat_resolution*', [status(thm)], ['152'])).
% 0.46/0.66  thf('154', plain,
% 0.46/0.66      ((((v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 0.46/0.66          (k8_tmap_1 @ sk_A @ sk_B))
% 0.46/0.66         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.46/0.66         <= (((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.46/0.66               (k8_tmap_1 @ sk_A @ sk_B))))),
% 0.46/0.66      inference('simpl_trail', [status(thm)], ['138', '153'])).
% 0.46/0.66  thf('155', plain,
% 0.46/0.66      (((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B)) | (v1_tsep_1 @ sk_B @ sk_A))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('156', plain,
% 0.46/0.66      (((v1_tsep_1 @ sk_B @ sk_A)) <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.46/0.66      inference('split', [status(esa)], ['155'])).
% 0.46/0.66  thf('157', plain,
% 0.46/0.66      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['6', '7'])).
% 0.46/0.66  thf(d1_tsep_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( l1_pre_topc @ A ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( m1_pre_topc @ B @ A ) =>
% 0.46/0.66           ( ( v1_tsep_1 @ B @ A ) <=>
% 0.46/0.66             ( ![C:$i]:
% 0.46/0.66               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66                 ( ( ( C ) = ( u1_struct_0 @ B ) ) => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.46/0.66  thf('158', plain,
% 0.46/0.66      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.46/0.66         (~ (m1_pre_topc @ X18 @ X19)
% 0.46/0.66          | ~ (v1_tsep_1 @ X18 @ X19)
% 0.46/0.66          | ((X20) != (u1_struct_0 @ X18))
% 0.46/0.66          | (v3_pre_topc @ X20 @ X19)
% 0.46/0.66          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.46/0.66          | ~ (l1_pre_topc @ X19))),
% 0.46/0.66      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.46/0.66  thf('159', plain,
% 0.46/0.66      (![X18 : $i, X19 : $i]:
% 0.46/0.66         (~ (l1_pre_topc @ X19)
% 0.46/0.66          | ~ (m1_subset_1 @ (u1_struct_0 @ X18) @ 
% 0.46/0.66               (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.46/0.66          | (v3_pre_topc @ (u1_struct_0 @ X18) @ X19)
% 0.46/0.66          | ~ (v1_tsep_1 @ X18 @ X19)
% 0.46/0.66          | ~ (m1_pre_topc @ X18 @ X19))),
% 0.46/0.66      inference('simplify', [status(thm)], ['158'])).
% 0.46/0.66  thf('160', plain,
% 0.46/0.66      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.46/0.66        | ~ (v1_tsep_1 @ sk_B @ sk_A)
% 0.46/0.66        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.46/0.66        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['157', '159'])).
% 0.46/0.66  thf('161', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('162', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('163', plain,
% 0.46/0.66      ((~ (v1_tsep_1 @ sk_B @ sk_A)
% 0.46/0.66        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['160', '161', '162'])).
% 0.46/0.66  thf('164', plain,
% 0.46/0.66      (((v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))
% 0.46/0.66         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['156', '163'])).
% 0.46/0.66  thf('165', plain,
% 0.46/0.66      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['6', '7'])).
% 0.46/0.66  thf(t113_tmap_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.66           ( ( v3_pre_topc @ B @ A ) <=>
% 0.46/0.66             ( ( v1_funct_1 @ ( k7_tmap_1 @ A @ B ) ) & 
% 0.46/0.66               ( v1_funct_2 @
% 0.46/0.66                 ( k7_tmap_1 @ A @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.46/0.66                 ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) & 
% 0.46/0.66               ( v5_pre_topc @
% 0.46/0.66                 ( k7_tmap_1 @ A @ B ) @ A @ ( k6_tmap_1 @ A @ B ) ) & 
% 0.46/0.66               ( m1_subset_1 @
% 0.46/0.66                 ( k7_tmap_1 @ A @ B ) @ 
% 0.46/0.66                 ( k1_zfmisc_1 @
% 0.46/0.66                   ( k2_zfmisc_1 @
% 0.46/0.66                     ( u1_struct_0 @ A ) @ 
% 0.46/0.66                     ( u1_struct_0 @ ( k6_tmap_1 @ A @ B ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.66  thf('166', plain,
% 0.46/0.66      (![X30 : $i, X31 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.46/0.66          | ~ (v3_pre_topc @ X30 @ X31)
% 0.46/0.66          | (v5_pre_topc @ (k7_tmap_1 @ X31 @ X30) @ X31 @ 
% 0.46/0.66             (k6_tmap_1 @ X31 @ X30))
% 0.46/0.66          | ~ (l1_pre_topc @ X31)
% 0.46/0.66          | ~ (v2_pre_topc @ X31)
% 0.46/0.66          | (v2_struct_0 @ X31))),
% 0.46/0.66      inference('cnf', [status(esa)], [t113_tmap_1])).
% 0.46/0.66  thf('167', plain,
% 0.46/0.66      (((v2_struct_0 @ sk_A)
% 0.46/0.66        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.66        | ~ (l1_pre_topc @ sk_A)
% 0.46/0.66        | (v5_pre_topc @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_A @ 
% 0.46/0.66           (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.46/0.66        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['165', '166'])).
% 0.46/0.66  thf('168', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('169', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('170', plain,
% 0.46/0.66      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.46/0.66         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('clc', [status(thm)], ['70', '71'])).
% 0.46/0.66  thf('171', plain,
% 0.46/0.66      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.46/0.66      inference('clc', [status(thm)], ['47', '48'])).
% 0.46/0.66  thf('172', plain,
% 0.46/0.66      (((v2_struct_0 @ sk_A)
% 0.46/0.66        | (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 0.46/0.66           (k8_tmap_1 @ sk_A @ sk_B))
% 0.46/0.66        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['167', '168', '169', '170', '171'])).
% 0.46/0.66  thf('173', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('174', plain,
% 0.46/0.66      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.46/0.66        | (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 0.46/0.66           (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.46/0.66      inference('clc', [status(thm)], ['172', '173'])).
% 0.46/0.66  thf('175', plain,
% 0.46/0.66      (((v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 0.46/0.66         (k8_tmap_1 @ sk_A @ sk_B))) <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['164', '174'])).
% 0.46/0.66  thf('176', plain,
% 0.46/0.66      (((((k9_tmap_1 @ sk_A @ sk_B) = (k6_partfun1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.66         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.46/0.66         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.46/0.66               (k1_zfmisc_1 @ 
% 0.46/0.66                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.46/0.66      inference('demod', [status(thm)], ['123', '134'])).
% 0.46/0.66  thf('177', plain,
% 0.46/0.66      ((v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66        (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('clc', [status(thm)], ['53', '54'])).
% 0.46/0.66  thf('178', plain,
% 0.46/0.66      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['15', '49'])).
% 0.46/0.66  thf('179', plain,
% 0.46/0.66      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.46/0.66         (k1_zfmisc_1 @ 
% 0.46/0.66          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))))
% 0.46/0.66         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.46/0.66               (k1_zfmisc_1 @ 
% 0.46/0.66                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.46/0.66      inference('split', [status(esa)], ['56'])).
% 0.46/0.66  thf('180', plain,
% 0.46/0.66      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.46/0.66         (k1_zfmisc_1 @ 
% 0.46/0.66          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))
% 0.46/0.66         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.46/0.66               (k1_zfmisc_1 @ 
% 0.46/0.66                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.46/0.66      inference('sup+', [status(thm)], ['178', '179'])).
% 0.46/0.66  thf('181', plain,
% 0.46/0.66      ((~ (m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.46/0.66           (k1_zfmisc_1 @ 
% 0.46/0.66            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))
% 0.46/0.66        | ~ (v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.46/0.66             (k8_tmap_1 @ sk_A @ sk_B))
% 0.46/0.66        | ~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66             (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))
% 0.46/0.66        | ~ (v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))
% 0.46/0.66        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.46/0.66        | ~ (v1_tsep_1 @ sk_B @ sk_A))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('182', plain,
% 0.46/0.66      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['15', '49'])).
% 0.46/0.66  thf('183', plain,
% 0.46/0.66      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['15', '49'])).
% 0.46/0.66  thf('184', plain, ((v1_funct_1 @ (k9_tmap_1 @ sk_A @ sk_B))),
% 0.46/0.66      inference('clc', [status(thm)], ['80', '81'])).
% 0.46/0.66  thf('185', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('186', plain,
% 0.46/0.66      ((~ (m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.46/0.66           (k1_zfmisc_1 @ 
% 0.46/0.66            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.46/0.66        | ~ (v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.46/0.66             (k8_tmap_1 @ sk_A @ sk_B))
% 0.46/0.66        | ~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66             (u1_struct_0 @ sk_A))
% 0.46/0.66        | ~ (v1_tsep_1 @ sk_B @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['181', '182', '183', '184', '185'])).
% 0.46/0.66  thf('187', plain,
% 0.46/0.66      (((~ (v1_tsep_1 @ sk_B @ sk_A)
% 0.46/0.66         | ~ (v1_funct_2 @ (k9_tmap_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66              (u1_struct_0 @ sk_A))
% 0.46/0.66         | ~ (v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.46/0.66              (k8_tmap_1 @ sk_A @ sk_B))))
% 0.46/0.66         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.46/0.66               (k1_zfmisc_1 @ 
% 0.46/0.66                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['180', '186'])).
% 0.46/0.66  thf('188', plain,
% 0.46/0.66      (((~ (v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.46/0.66            (k8_tmap_1 @ sk_A @ sk_B))
% 0.46/0.66         | ~ (v1_tsep_1 @ sk_B @ sk_A)))
% 0.46/0.66         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.46/0.66               (k1_zfmisc_1 @ 
% 0.46/0.66                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['177', '187'])).
% 0.46/0.66  thf('189', plain,
% 0.46/0.66      (((~ (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 0.46/0.66            (k8_tmap_1 @ sk_A @ sk_B))
% 0.46/0.66         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.66         | ~ (v1_tsep_1 @ sk_B @ sk_A)))
% 0.46/0.66         <= (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.46/0.66               (k1_zfmisc_1 @ 
% 0.46/0.66                (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66                 (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['176', '188'])).
% 0.46/0.66  thf('190', plain,
% 0.46/0.66      (((m1_subset_1 @ (k9_tmap_1 @ sk_A @ sk_B) @ 
% 0.46/0.66         (k1_zfmisc_1 @ 
% 0.46/0.66          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66           (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))))),
% 0.46/0.66      inference('sat_resolution*', [status(thm)], ['152'])).
% 0.46/0.66  thf('191', plain,
% 0.46/0.66      ((~ (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 0.46/0.66           (k8_tmap_1 @ sk_A @ sk_B))
% 0.46/0.66        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.66        | ~ (v1_tsep_1 @ sk_B @ sk_A))),
% 0.46/0.66      inference('simpl_trail', [status(thm)], ['189', '190'])).
% 0.46/0.66  thf('192', plain,
% 0.46/0.66      (((~ (v1_tsep_1 @ sk_B @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.46/0.66         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['175', '191'])).
% 0.46/0.66  thf('193', plain,
% 0.46/0.66      (((v1_tsep_1 @ sk_B @ sk_A)) <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.46/0.66      inference('split', [status(esa)], ['155'])).
% 0.46/0.66  thf('194', plain,
% 0.46/0.66      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))) <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['192', '193'])).
% 0.46/0.66  thf(fc2_struct_0, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.46/0.66       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.46/0.66  thf('195', plain,
% 0.46/0.66      (![X1 : $i]:
% 0.46/0.66         (~ (v1_xboole_0 @ (u1_struct_0 @ X1))
% 0.46/0.66          | ~ (l1_struct_0 @ X1)
% 0.46/0.66          | (v2_struct_0 @ X1))),
% 0.46/0.66      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.46/0.66  thf('196', plain,
% 0.46/0.66      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.46/0.66         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['194', '195'])).
% 0.46/0.66  thf('197', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(dt_l1_pre_topc, axiom,
% 0.46/0.66    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.46/0.66  thf('198', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.46/0.66  thf('199', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.66      inference('sup-', [status(thm)], ['197', '198'])).
% 0.46/0.66  thf('200', plain, (((v2_struct_0 @ sk_A)) <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['196', '199'])).
% 0.46/0.66  thf('201', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('202', plain, (~ ((v1_tsep_1 @ sk_B @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['200', '201'])).
% 0.46/0.66  thf('203', plain,
% 0.46/0.66      (((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.46/0.66         (k8_tmap_1 @ sk_A @ sk_B))) | 
% 0.46/0.66       ((v1_tsep_1 @ sk_B @ sk_A))),
% 0.46/0.66      inference('split', [status(esa)], ['136'])).
% 0.46/0.66  thf('204', plain,
% 0.46/0.66      (((v5_pre_topc @ (k9_tmap_1 @ sk_A @ sk_B) @ sk_A @ 
% 0.46/0.66         (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.46/0.66      inference('sat_resolution*', [status(thm)], ['202', '203'])).
% 0.46/0.66  thf('205', plain,
% 0.46/0.66      (((v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 0.46/0.66         (k8_tmap_1 @ sk_A @ sk_B))
% 0.46/0.66        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('simpl_trail', [status(thm)], ['154', '204'])).
% 0.46/0.66  thf('206', plain,
% 0.46/0.66      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.46/0.66         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('clc', [status(thm)], ['70', '71'])).
% 0.46/0.66  thf('207', plain,
% 0.46/0.66      (![X30 : $i, X31 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.46/0.66          | ~ (v1_funct_1 @ (k7_tmap_1 @ X31 @ X30))
% 0.46/0.66          | ~ (v1_funct_2 @ (k7_tmap_1 @ X31 @ X30) @ (u1_struct_0 @ X31) @ 
% 0.46/0.66               (u1_struct_0 @ (k6_tmap_1 @ X31 @ X30)))
% 0.46/0.66          | ~ (v5_pre_topc @ (k7_tmap_1 @ X31 @ X30) @ X31 @ 
% 0.46/0.66               (k6_tmap_1 @ X31 @ X30))
% 0.46/0.66          | ~ (m1_subset_1 @ (k7_tmap_1 @ X31 @ X30) @ 
% 0.46/0.66               (k1_zfmisc_1 @ 
% 0.46/0.66                (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ 
% 0.46/0.66                 (u1_struct_0 @ (k6_tmap_1 @ X31 @ X30)))))
% 0.46/0.66          | (v3_pre_topc @ X30 @ X31)
% 0.46/0.66          | ~ (l1_pre_topc @ X31)
% 0.46/0.66          | ~ (v2_pre_topc @ X31)
% 0.46/0.66          | (v2_struct_0 @ X31))),
% 0.46/0.66      inference('cnf', [status(esa)], [t113_tmap_1])).
% 0.46/0.66  thf('208', plain,
% 0.46/0.66      ((~ (m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.46/0.66           (k1_zfmisc_1 @ 
% 0.46/0.66            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66             (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))))
% 0.46/0.66        | (v2_struct_0 @ sk_A)
% 0.46/0.66        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.66        | ~ (l1_pre_topc @ sk_A)
% 0.46/0.66        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.46/0.66        | ~ (v5_pre_topc @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_A @ 
% 0.46/0.66             (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.46/0.66        | ~ (v1_funct_2 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) @ 
% 0.46/0.66             (u1_struct_0 @ sk_A) @ 
% 0.46/0.66             (u1_struct_0 @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))
% 0.46/0.66        | ~ (v1_funct_1 @ (k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.46/0.66        | ~ (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.66             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['206', '207'])).
% 0.46/0.66  thf('209', plain,
% 0.46/0.66      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.46/0.66      inference('clc', [status(thm)], ['47', '48'])).
% 0.46/0.66  thf('210', plain,
% 0.46/0.66      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['15', '49'])).
% 0.46/0.66  thf('211', plain,
% 0.46/0.66      ((m1_subset_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.46/0.66        (k1_zfmisc_1 @ 
% 0.46/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 0.46/0.66      inference('clc', [status(thm)], ['119', '120'])).
% 0.46/0.66  thf('212', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('213', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('214', plain,
% 0.46/0.66      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.46/0.66         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('clc', [status(thm)], ['70', '71'])).
% 0.46/0.66  thf('215', plain,
% 0.46/0.66      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.46/0.66      inference('clc', [status(thm)], ['47', '48'])).
% 0.46/0.66  thf('216', plain,
% 0.46/0.66      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.46/0.66         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('clc', [status(thm)], ['70', '71'])).
% 0.46/0.66  thf('217', plain,
% 0.46/0.66      (((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.46/0.66      inference('clc', [status(thm)], ['47', '48'])).
% 0.46/0.66  thf('218', plain,
% 0.46/0.66      (((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['15', '49'])).
% 0.46/0.66  thf('219', plain,
% 0.46/0.66      ((v1_funct_2 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ 
% 0.46/0.66        (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('clc', [status(thm)], ['132', '133'])).
% 0.46/0.66  thf('220', plain,
% 0.46/0.66      (((k7_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 0.46/0.66         = (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('clc', [status(thm)], ['70', '71'])).
% 0.46/0.66  thf('221', plain, ((v1_funct_1 @ (k6_partfun1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['108', '109'])).
% 0.46/0.66  thf('222', plain,
% 0.46/0.66      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['6', '7'])).
% 0.46/0.66  thf('223', plain,
% 0.46/0.66      (((v2_struct_0 @ sk_A)
% 0.46/0.66        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.46/0.66        | ~ (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 0.46/0.66             (k8_tmap_1 @ sk_A @ sk_B)))),
% 0.46/0.66      inference('demod', [status(thm)],
% 0.46/0.66                ['208', '209', '210', '211', '212', '213', '214', '215', 
% 0.46/0.66                 '216', '217', '218', '219', '220', '221', '222'])).
% 0.46/0.66  thf('224', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('225', plain,
% 0.46/0.66      ((~ (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 0.46/0.66           (k8_tmap_1 @ sk_A @ sk_B))
% 0.46/0.66        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 0.46/0.66      inference('clc', [status(thm)], ['223', '224'])).
% 0.46/0.66  thf('226', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('227', plain,
% 0.46/0.66      (![X18 : $i, X19 : $i]:
% 0.46/0.66         (~ (m1_pre_topc @ X18 @ X19)
% 0.46/0.66          | ((sk_C @ X18 @ X19) = (u1_struct_0 @ X18))
% 0.46/0.66          | (v1_tsep_1 @ X18 @ X19)
% 0.46/0.66          | ~ (l1_pre_topc @ X19))),
% 0.46/0.66      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.46/0.66  thf('228', plain,
% 0.46/0.66      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.66        | (v1_tsep_1 @ sk_B @ sk_A)
% 0.46/0.66        | ((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['226', '227'])).
% 0.46/0.66  thf('229', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('230', plain,
% 0.46/0.66      (((v1_tsep_1 @ sk_B @ sk_A)
% 0.46/0.66        | ((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))),
% 0.46/0.66      inference('demod', [status(thm)], ['228', '229'])).
% 0.46/0.66  thf('231', plain,
% 0.46/0.66      ((~ (v1_tsep_1 @ sk_B @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.46/0.66      inference('split', [status(esa)], ['149'])).
% 0.46/0.66  thf('232', plain,
% 0.46/0.66      ((((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))
% 0.46/0.66         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['230', '231'])).
% 0.46/0.66  thf('233', plain,
% 0.46/0.66      (![X18 : $i, X19 : $i]:
% 0.46/0.66         (~ (m1_pre_topc @ X18 @ X19)
% 0.46/0.66          | ~ (v3_pre_topc @ (sk_C @ X18 @ X19) @ X19)
% 0.46/0.66          | (v1_tsep_1 @ X18 @ X19)
% 0.46/0.66          | ~ (l1_pre_topc @ X19))),
% 0.46/0.66      inference('cnf', [status(esa)], [d1_tsep_1])).
% 0.46/0.66  thf('234', plain,
% 0.46/0.66      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.46/0.66         | ~ (l1_pre_topc @ sk_A)
% 0.46/0.66         | (v1_tsep_1 @ sk_B @ sk_A)
% 0.46/0.66         | ~ (m1_pre_topc @ sk_B @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['232', '233'])).
% 0.46/0.66  thf('235', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('236', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('237', plain,
% 0.46/0.66      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 0.46/0.66         | (v1_tsep_1 @ sk_B @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['234', '235', '236'])).
% 0.46/0.66  thf('238', plain,
% 0.46/0.66      ((~ (v1_tsep_1 @ sk_B @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.46/0.66      inference('split', [status(esa)], ['149'])).
% 0.46/0.66  thf('239', plain,
% 0.46/0.66      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))
% 0.46/0.66         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 0.46/0.66      inference('clc', [status(thm)], ['237', '238'])).
% 0.46/0.66  thf('240', plain, (~ ((v1_tsep_1 @ sk_B @ sk_A))),
% 0.46/0.66      inference('sat_resolution*', [status(thm)], ['202'])).
% 0.46/0.66  thf('241', plain, (~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)),
% 0.46/0.66      inference('simpl_trail', [status(thm)], ['239', '240'])).
% 0.46/0.66  thf('242', plain,
% 0.46/0.66      (~ (v5_pre_topc @ (k6_partfun1 @ (u1_struct_0 @ sk_A)) @ sk_A @ 
% 0.46/0.66          (k8_tmap_1 @ sk_A @ sk_B))),
% 0.46/0.66      inference('clc', [status(thm)], ['225', '241'])).
% 0.46/0.66  thf('243', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['205', '242'])).
% 0.46/0.66  thf('244', plain,
% 0.46/0.66      (![X1 : $i]:
% 0.46/0.66         (~ (v1_xboole_0 @ (u1_struct_0 @ X1))
% 0.46/0.66          | ~ (l1_struct_0 @ X1)
% 0.46/0.66          | (v2_struct_0 @ X1))),
% 0.46/0.66      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.46/0.66  thf('245', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['243', '244'])).
% 0.46/0.66  thf('246', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.66      inference('sup-', [status(thm)], ['197', '198'])).
% 0.46/0.66  thf('247', plain, ((v2_struct_0 @ sk_A)),
% 0.46/0.66      inference('demod', [status(thm)], ['245', '246'])).
% 0.46/0.66  thf('248', plain, ($false), inference('demod', [status(thm)], ['0', '247'])).
% 0.46/0.66  
% 0.46/0.66  % SZS output end Refutation
% 0.46/0.66  
% 0.46/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
