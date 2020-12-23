%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iBxaPbf34Y

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:43 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  193 (2746 expanded)
%              Number of leaves         :   43 ( 774 expanded)
%              Depth                    :   28
%              Number of atoms          : 1820 (80374 expanded)
%              Number of equality atoms :   70 (1938 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t60_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ B ) )
             => ! [D: $i] :
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
                 => ( ( ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) )
                      = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                   => ( r1_funct_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ ( k2_tmap_1 @ B @ A @ D @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v2_pre_topc @ B )
              & ( l1_pre_topc @ B ) )
           => ! [C: $i] :
                ( ( ~ ( v2_struct_0 @ C )
                  & ( m1_pre_topc @ C @ B ) )
               => ! [D: $i] :
                    ( ( ( v1_funct_1 @ D )
                      & ( v1_funct_2 @ D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                      & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
                   => ( ( ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) )
                        = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                     => ( r1_funct_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ ( k2_tmap_1 @ B @ A @ D @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t60_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('2',plain,(
    ! [X35: $i] :
      ( ( m1_pre_topc @ X35 @ X35 )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('3',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t11_tmap_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
            & ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) )).

thf('4',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_pre_topc @ X31 @ X32 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X31 ) @ ( u1_pre_topc @ X31 ) ) @ X32 )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[t11_tmap_1])).

thf('5',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X35: $i] :
      ( ( m1_pre_topc @ X35 @ X35 )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t25_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ( ( k1_tsep_1 @ A @ B @ B )
            = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) )).

thf('10',plain,(
    ! [X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X33 )
      | ~ ( m1_pre_topc @ X33 @ X34 )
      | ( ( k1_tsep_1 @ X34 @ X33 @ X33 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X33 ) @ ( u1_pre_topc @ X33 ) ) )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t25_tmap_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tsep_1 @ X0 @ X0 @ X0 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k1_tsep_1 @ X0 @ X0 @ X0 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( ( k1_tsep_1 @ sk_B @ sk_B @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( v2_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['8','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( k1_tsep_1 @ sk_B @ sk_B @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( k1_tsep_1 @ sk_B @ sk_B @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['7','18'])).

thf(d2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( v1_pre_topc @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ( ( D
                      = ( k1_tsep_1 @ A @ B @ C ) )
                  <=> ( ( u1_struct_0 @ D )
                      = ( k2_xboole_0 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) )).

thf('20',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X23 )
      | ~ ( m1_pre_topc @ X23 @ X24 )
      | ( v2_struct_0 @ X25 )
      | ~ ( v1_pre_topc @ X25 )
      | ~ ( m1_pre_topc @ X25 @ X24 )
      | ( X25
       != ( k1_tsep_1 @ X24 @ X23 @ X26 ) )
      | ( ( u1_struct_0 @ X25 )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( m1_pre_topc @ X26 @ X24 )
      | ( v2_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d2_tsep_1])).

thf('21',plain,(
    ! [X23: $i,X24: $i,X26: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X24 )
      | ( ( u1_struct_0 @ ( k1_tsep_1 @ X24 @ X23 @ X26 ) )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ X24 @ X23 @ X26 ) @ X24 )
      | ~ ( v1_pre_topc @ ( k1_tsep_1 @ X24 @ X23 @ X26 ) )
      | ( v2_struct_0 @ ( k1_tsep_1 @ X24 @ X23 @ X26 ) )
      | ~ ( m1_pre_topc @ X23 @ X24 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc7_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ( ~ ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
        & ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('24',plain,(
    ! [X16: $i] :
      ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X16 ) @ ( u1_pre_topc @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc7_pre_topc])).

thf('25',plain,
    ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k1_tsep_1 @ sk_B @ sk_B @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('31',plain,(
    v1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('33',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
      = ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['22','31','32','33'])).

thf('35',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
      = ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X33 )
      | ~ ( m1_pre_topc @ X33 @ X34 )
      | ( ( k1_tsep_1 @ X34 @ X33 @ X33 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X33 ) @ ( u1_pre_topc @ X33 ) ) )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t25_tmap_1])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( ( k1_tsep_1 @ sk_B @ sk_C @ sk_C )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k1_tsep_1 @ sk_B @ sk_C @ sk_C )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k1_tsep_1 @ sk_B @ sk_C @ sk_C )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k1_tsep_1 @ sk_B @ sk_C @ sk_C )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k1_tsep_1 @ sk_B @ sk_B @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('47',plain,
    ( ( k1_tsep_1 @ sk_B @ sk_B @ sk_B )
    = ( k1_tsep_1 @ sk_B @ sk_C @ sk_C ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k1_tsep_1 @ sk_B @ sk_B @ sk_B )
    = ( k1_tsep_1 @ sk_B @ sk_C @ sk_C ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('49',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_C @ sk_C ) )
      = ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_C @ sk_C ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['35','47','48'])).

thf('50',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_C @ sk_C ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_C @ sk_C ) )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_C @ sk_C ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_C @ sk_C ) )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_C @ sk_C ) )
      = ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_C @ sk_C ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X16: $i] :
      ( ~ ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X16 ) @ ( u1_pre_topc @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc7_pre_topc])).

thf('57',plain,
    ( ~ ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ~ ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ~ ( v2_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k1_tsep_1 @ sk_B @ sk_B @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k1_tsep_1 @ sk_B @ sk_B @ sk_B )
    = ( k1_tsep_1 @ sk_B @ sk_C @ sk_C ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('65',plain,(
    ~ ( v2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_C @ sk_C ) )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['54','65'])).

thf('67',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['7','18'])).

thf('68',plain,
    ( ( k1_tsep_1 @ sk_B @ sk_B @ sk_B )
    = ( k1_tsep_1 @ sk_B @ sk_C @ sk_C ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('69',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_C @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X23: $i,X24: $i,X26: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_pre_topc @ X26 @ X24 )
      | ( ( u1_struct_0 @ ( k1_tsep_1 @ X24 @ X23 @ X26 ) )
        = ( k2_xboole_0 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( m1_pre_topc @ ( k1_tsep_1 @ X24 @ X23 @ X26 ) @ X24 )
      | ~ ( v1_pre_topc @ ( k1_tsep_1 @ X24 @ X23 @ X26 ) )
      | ( v2_struct_0 @ ( k1_tsep_1 @ X24 @ X23 @ X26 ) )
      | ~ ( m1_pre_topc @ X23 @ X24 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('71',plain,
    ( ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_B )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_C @ sk_C ) )
    | ~ ( v1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_C @ sk_C ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_C @ sk_C ) )
      = ( k2_xboole_0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('74',plain,
    ( ( k1_tsep_1 @ sk_B @ sk_B @ sk_B )
    = ( k1_tsep_1 @ sk_B @ sk_C @ sk_C ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('75',plain,(
    v1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('77',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_C @ sk_C ) )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_C @ sk_C ) )
      = ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['71','72','75','76','77','78'])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_C @ sk_C ) )
      = ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_C @ sk_C ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_C @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['66','80'])).

thf('82',plain,(
    ~ ( v2_struct_0 @ ( k1_tsep_1 @ sk_B @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('83',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( ( u1_struct_0 @ sk_B )
      = ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('90',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( r1_funct_2 @ X17 @ X18 @ X19 @ X20 @ X21 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X17 @ X18 )
      | ~ ( v1_funct_1 @ X21 )
      | ( v1_xboole_0 @ X20 )
      | ( v1_xboole_0 @ X18 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_2 @ X22 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r1_funct_2])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X1 @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ X1 @ X0 @ sk_D @ sk_D ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X1 @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ( r1_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ X1 @ X0 @ sk_D @ sk_D ) ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X1 @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ X1 @ X0 @ sk_D @ sk_D ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['88','96'])).

thf('98',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('101',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['97','98','101'])).

thf('103',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('106',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ! [D: $i] :
                  ( ( m1_pre_topc @ D @ A )
                 => ( ( k2_tmap_1 @ A @ B @ C @ D )
                    = ( k2_partfun1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( u1_struct_0 @ D ) ) ) ) ) ) ) )).

thf('109',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( m1_pre_topc @ X28 @ X29 )
      | ( ( k2_tmap_1 @ X29 @ X27 @ X30 @ X28 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X27 ) @ X30 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('116',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ( ( k2_partfun1 @ X10 @ X11 @ X9 @ X12 )
        = ( k7_relat_1 @ X9 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['110','111','112','113','114','119','120','121'])).

thf('123',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['107','122'])).

thf('124',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('125',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v4_relat_1 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('126',plain,(
    v4_relat_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('127',plain,(
    ! [X1: $i,X2: $i] :
      ( ( X1
        = ( k7_relat_1 @ X1 @ X2 ) )
      | ~ ( v4_relat_1 @ X1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('128',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('130',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('131',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['128','131'])).

thf('133',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('134',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['123','134'])).

thf('136',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = sk_D ) ),
    inference(clc,[status(thm)],['135','136'])).

thf('138',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
    = sk_D ),
    inference(clc,[status(thm)],['137','138'])).

thf('140',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ),
    inference(demod,[status(thm)],['106','139'])).

thf('141',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['103','140'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('142',plain,(
    ! [X14: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('143',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('145',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('146',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['143','146'])).

thf('148',plain,(
    $false ),
    inference(demod,[status(thm)],['0','147'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iBxaPbf34Y
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:29:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.46/0.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.71  % Solved by: fo/fo7.sh
% 0.46/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.71  % done 304 iterations in 0.242s
% 0.46/0.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.71  % SZS output start Refutation
% 0.46/0.71  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.46/0.71  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.71  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.46/0.71  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.46/0.71  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 0.46/0.71  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.46/0.71  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.46/0.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.71  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.46/0.71  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.46/0.71  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.46/0.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.71  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.71  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.71  thf(sk_D_type, type, sk_D: $i).
% 0.46/0.71  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.46/0.71  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.71  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.46/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.71  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.71  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.46/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.71  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.71  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.71  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.46/0.71  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.46/0.71  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 0.46/0.71  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.71  thf(t60_tmap_1, conjecture,
% 0.46/0.71    (![A:$i]:
% 0.46/0.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.71       ( ![B:$i]:
% 0.46/0.71         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.46/0.71             ( l1_pre_topc @ B ) ) =>
% 0.46/0.71           ( ![C:$i]:
% 0.46/0.71             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.46/0.71               ( ![D:$i]:
% 0.46/0.71                 ( ( ( v1_funct_1 @ D ) & 
% 0.46/0.71                     ( v1_funct_2 @
% 0.46/0.71                       D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.46/0.71                     ( m1_subset_1 @
% 0.46/0.71                       D @ 
% 0.46/0.71                       ( k1_zfmisc_1 @
% 0.46/0.71                         ( k2_zfmisc_1 @
% 0.46/0.71                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.46/0.71                   ( ( ( g1_pre_topc @
% 0.46/0.71                         ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.46/0.71                       ( g1_pre_topc @
% 0.46/0.71                         ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.46/0.71                     ( r1_funct_2 @
% 0.46/0.71                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.46/0.71                       ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ 
% 0.46/0.71                       ( k2_tmap_1 @ B @ A @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.71    (~( ![A:$i]:
% 0.46/0.71        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.46/0.71            ( l1_pre_topc @ A ) ) =>
% 0.46/0.71          ( ![B:$i]:
% 0.46/0.71            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.46/0.71                ( l1_pre_topc @ B ) ) =>
% 0.46/0.71              ( ![C:$i]:
% 0.46/0.71                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.46/0.71                  ( ![D:$i]:
% 0.46/0.71                    ( ( ( v1_funct_1 @ D ) & 
% 0.46/0.71                        ( v1_funct_2 @
% 0.46/0.71                          D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.46/0.71                        ( m1_subset_1 @
% 0.46/0.71                          D @ 
% 0.46/0.71                          ( k1_zfmisc_1 @
% 0.46/0.71                            ( k2_zfmisc_1 @
% 0.46/0.71                              ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.46/0.71                      ( ( ( g1_pre_topc @
% 0.46/0.71                            ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.46/0.71                          ( g1_pre_topc @
% 0.46/0.71                            ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.46/0.71                        ( r1_funct_2 @
% 0.46/0.71                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.46/0.71                          ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ 
% 0.46/0.71                          ( k2_tmap_1 @ B @ A @ D @ C ) ) ) ) ) ) ) ) ) ) )),
% 0.46/0.71    inference('cnf.neg', [status(esa)], [t60_tmap_1])).
% 0.46/0.71  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('1', plain,
% 0.46/0.71      ((m1_subset_1 @ sk_D @ 
% 0.46/0.71        (k1_zfmisc_1 @ 
% 0.46/0.71         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf(t2_tsep_1, axiom,
% 0.46/0.71    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.46/0.71  thf('2', plain,
% 0.46/0.71      (![X35 : $i]: ((m1_pre_topc @ X35 @ X35) | ~ (l1_pre_topc @ X35))),
% 0.46/0.71      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.46/0.71  thf('3', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf(t11_tmap_1, axiom,
% 0.46/0.71    (![A:$i]:
% 0.46/0.71     ( ( l1_pre_topc @ A ) =>
% 0.46/0.71       ( ![B:$i]:
% 0.46/0.71         ( ( m1_pre_topc @ B @ A ) =>
% 0.46/0.71           ( ( v1_pre_topc @
% 0.46/0.71               ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.46/0.71             ( m1_pre_topc @
% 0.46/0.71               ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) ))).
% 0.46/0.71  thf('4', plain,
% 0.46/0.71      (![X31 : $i, X32 : $i]:
% 0.46/0.71         (~ (m1_pre_topc @ X31 @ X32)
% 0.46/0.71          | (m1_pre_topc @ 
% 0.46/0.71             (g1_pre_topc @ (u1_struct_0 @ X31) @ (u1_pre_topc @ X31)) @ X32)
% 0.46/0.71          | ~ (l1_pre_topc @ X32))),
% 0.46/0.71      inference('cnf', [status(esa)], [t11_tmap_1])).
% 0.46/0.71  thf('5', plain,
% 0.46/0.71      ((~ (l1_pre_topc @ sk_B)
% 0.46/0.71        | (m1_pre_topc @ 
% 0.46/0.71           (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ sk_B))),
% 0.46/0.71      inference('sup-', [status(thm)], ['3', '4'])).
% 0.46/0.71  thf('6', plain, ((l1_pre_topc @ sk_B)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('7', plain,
% 0.46/0.71      ((m1_pre_topc @ 
% 0.46/0.71        (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ sk_B)),
% 0.46/0.71      inference('demod', [status(thm)], ['5', '6'])).
% 0.46/0.71  thf('8', plain,
% 0.46/0.71      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.46/0.71         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('9', plain,
% 0.46/0.71      (![X35 : $i]: ((m1_pre_topc @ X35 @ X35) | ~ (l1_pre_topc @ X35))),
% 0.46/0.71      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.46/0.71  thf(t25_tmap_1, axiom,
% 0.46/0.71    (![A:$i]:
% 0.46/0.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.71       ( ![B:$i]:
% 0.46/0.71         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.46/0.71           ( ( k1_tsep_1 @ A @ B @ B ) =
% 0.46/0.71             ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ))).
% 0.46/0.71  thf('10', plain,
% 0.46/0.71      (![X33 : $i, X34 : $i]:
% 0.46/0.71         ((v2_struct_0 @ X33)
% 0.46/0.71          | ~ (m1_pre_topc @ X33 @ X34)
% 0.46/0.71          | ((k1_tsep_1 @ X34 @ X33 @ X33)
% 0.46/0.71              = (g1_pre_topc @ (u1_struct_0 @ X33) @ (u1_pre_topc @ X33)))
% 0.46/0.71          | ~ (l1_pre_topc @ X34)
% 0.46/0.71          | ~ (v2_pre_topc @ X34)
% 0.46/0.71          | (v2_struct_0 @ X34))),
% 0.46/0.71      inference('cnf', [status(esa)], [t25_tmap_1])).
% 0.46/0.71  thf('11', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         (~ (l1_pre_topc @ X0)
% 0.46/0.71          | (v2_struct_0 @ X0)
% 0.46/0.71          | ~ (v2_pre_topc @ X0)
% 0.46/0.71          | ~ (l1_pre_topc @ X0)
% 0.46/0.71          | ((k1_tsep_1 @ X0 @ X0 @ X0)
% 0.46/0.71              = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.46/0.71          | (v2_struct_0 @ X0))),
% 0.46/0.71      inference('sup-', [status(thm)], ['9', '10'])).
% 0.46/0.71  thf('12', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         (((k1_tsep_1 @ X0 @ X0 @ X0)
% 0.46/0.71            = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.46/0.71          | ~ (v2_pre_topc @ X0)
% 0.46/0.71          | (v2_struct_0 @ X0)
% 0.46/0.71          | ~ (l1_pre_topc @ X0))),
% 0.46/0.71      inference('simplify', [status(thm)], ['11'])).
% 0.46/0.71  thf('13', plain,
% 0.46/0.71      ((((k1_tsep_1 @ sk_B @ sk_B @ sk_B)
% 0.46/0.71          = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.46/0.71        | ~ (l1_pre_topc @ sk_B)
% 0.46/0.71        | (v2_struct_0 @ sk_B)
% 0.46/0.71        | ~ (v2_pre_topc @ sk_B))),
% 0.46/0.71      inference('sup+', [status(thm)], ['8', '12'])).
% 0.46/0.71  thf('14', plain, ((l1_pre_topc @ sk_B)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('15', plain, ((v2_pre_topc @ sk_B)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('16', plain,
% 0.46/0.71      ((((k1_tsep_1 @ sk_B @ sk_B @ sk_B)
% 0.46/0.71          = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.46/0.71        | (v2_struct_0 @ sk_B))),
% 0.46/0.71      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.46/0.71  thf('17', plain, (~ (v2_struct_0 @ sk_B)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('18', plain,
% 0.46/0.71      (((k1_tsep_1 @ sk_B @ sk_B @ sk_B)
% 0.46/0.71         = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.46/0.71      inference('clc', [status(thm)], ['16', '17'])).
% 0.46/0.71  thf('19', plain, ((m1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B) @ sk_B)),
% 0.46/0.71      inference('demod', [status(thm)], ['7', '18'])).
% 0.46/0.71  thf(d2_tsep_1, axiom,
% 0.46/0.71    (![A:$i]:
% 0.46/0.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.71       ( ![B:$i]:
% 0.46/0.71         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.46/0.71           ( ![C:$i]:
% 0.46/0.71             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.46/0.71               ( ![D:$i]:
% 0.46/0.71                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_pre_topc @ D ) & 
% 0.46/0.71                     ( m1_pre_topc @ D @ A ) ) =>
% 0.46/0.71                   ( ( ( D ) = ( k1_tsep_1 @ A @ B @ C ) ) <=>
% 0.46/0.71                     ( ( u1_struct_0 @ D ) =
% 0.46/0.71                       ( k2_xboole_0 @
% 0.46/0.71                         ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.71  thf('20', plain,
% 0.46/0.71      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.46/0.71         ((v2_struct_0 @ X23)
% 0.46/0.71          | ~ (m1_pre_topc @ X23 @ X24)
% 0.46/0.71          | (v2_struct_0 @ X25)
% 0.46/0.71          | ~ (v1_pre_topc @ X25)
% 0.46/0.71          | ~ (m1_pre_topc @ X25 @ X24)
% 0.46/0.71          | ((X25) != (k1_tsep_1 @ X24 @ X23 @ X26))
% 0.46/0.71          | ((u1_struct_0 @ X25)
% 0.46/0.71              = (k2_xboole_0 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X26)))
% 0.46/0.71          | ~ (m1_pre_topc @ X26 @ X24)
% 0.46/0.71          | (v2_struct_0 @ X26)
% 0.46/0.71          | ~ (l1_pre_topc @ X24)
% 0.46/0.71          | (v2_struct_0 @ X24))),
% 0.46/0.71      inference('cnf', [status(esa)], [d2_tsep_1])).
% 0.46/0.71  thf('21', plain,
% 0.46/0.71      (![X23 : $i, X24 : $i, X26 : $i]:
% 0.46/0.71         ((v2_struct_0 @ X24)
% 0.46/0.71          | ~ (l1_pre_topc @ X24)
% 0.46/0.71          | (v2_struct_0 @ X26)
% 0.46/0.71          | ~ (m1_pre_topc @ X26 @ X24)
% 0.46/0.71          | ((u1_struct_0 @ (k1_tsep_1 @ X24 @ X23 @ X26))
% 0.46/0.71              = (k2_xboole_0 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X26)))
% 0.46/0.71          | ~ (m1_pre_topc @ (k1_tsep_1 @ X24 @ X23 @ X26) @ X24)
% 0.46/0.71          | ~ (v1_pre_topc @ (k1_tsep_1 @ X24 @ X23 @ X26))
% 0.46/0.71          | (v2_struct_0 @ (k1_tsep_1 @ X24 @ X23 @ X26))
% 0.46/0.71          | ~ (m1_pre_topc @ X23 @ X24)
% 0.46/0.71          | (v2_struct_0 @ X23))),
% 0.46/0.71      inference('simplify', [status(thm)], ['20'])).
% 0.46/0.71  thf('22', plain,
% 0.46/0.71      (((v2_struct_0 @ sk_B)
% 0.46/0.71        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 0.46/0.71        | (v2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 0.46/0.71        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 0.46/0.71        | ((u1_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 0.46/0.71            = (k2_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_B)))
% 0.46/0.71        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 0.46/0.71        | (v2_struct_0 @ sk_B)
% 0.46/0.71        | ~ (l1_pre_topc @ sk_B)
% 0.46/0.71        | (v2_struct_0 @ sk_B))),
% 0.46/0.71      inference('sup-', [status(thm)], ['19', '21'])).
% 0.46/0.71  thf('23', plain,
% 0.46/0.71      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.46/0.71         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf(fc7_pre_topc, axiom,
% 0.46/0.71    (![A:$i]:
% 0.46/0.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.71       ( ( ~( v2_struct_0 @
% 0.46/0.71              ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) & 
% 0.46/0.71         ( v1_pre_topc @
% 0.46/0.71           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.46/0.71  thf('24', plain,
% 0.46/0.71      (![X16 : $i]:
% 0.46/0.71         ((v1_pre_topc @ 
% 0.46/0.71           (g1_pre_topc @ (u1_struct_0 @ X16) @ (u1_pre_topc @ X16)))
% 0.46/0.71          | ~ (l1_pre_topc @ X16)
% 0.46/0.71          | (v2_struct_0 @ X16))),
% 0.46/0.71      inference('cnf', [status(esa)], [fc7_pre_topc])).
% 0.46/0.71  thf('25', plain,
% 0.46/0.71      (((v1_pre_topc @ 
% 0.46/0.71         (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.46/0.71        | (v2_struct_0 @ sk_B)
% 0.46/0.71        | ~ (l1_pre_topc @ sk_B))),
% 0.46/0.71      inference('sup+', [status(thm)], ['23', '24'])).
% 0.46/0.71  thf('26', plain, ((l1_pre_topc @ sk_B)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('27', plain,
% 0.46/0.71      (((v1_pre_topc @ 
% 0.46/0.71         (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.46/0.71        | (v2_struct_0 @ sk_B))),
% 0.46/0.71      inference('demod', [status(thm)], ['25', '26'])).
% 0.46/0.71  thf('28', plain, (~ (v2_struct_0 @ sk_B)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('29', plain,
% 0.46/0.71      ((v1_pre_topc @ 
% 0.46/0.71        (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.46/0.71      inference('clc', [status(thm)], ['27', '28'])).
% 0.46/0.71  thf('30', plain,
% 0.46/0.71      (((k1_tsep_1 @ sk_B @ sk_B @ sk_B)
% 0.46/0.71         = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.46/0.71      inference('clc', [status(thm)], ['16', '17'])).
% 0.46/0.71  thf('31', plain, ((v1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))),
% 0.46/0.71      inference('demod', [status(thm)], ['29', '30'])).
% 0.46/0.71  thf(idempotence_k2_xboole_0, axiom,
% 0.46/0.71    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.46/0.71  thf('32', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.46/0.71      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.46/0.71  thf('33', plain, ((l1_pre_topc @ sk_B)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('34', plain,
% 0.46/0.71      (((v2_struct_0 @ sk_B)
% 0.46/0.71        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 0.46/0.71        | (v2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 0.46/0.71        | ((u1_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 0.46/0.71            = (u1_struct_0 @ sk_B))
% 0.46/0.71        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 0.46/0.71        | (v2_struct_0 @ sk_B)
% 0.46/0.71        | (v2_struct_0 @ sk_B))),
% 0.46/0.71      inference('demod', [status(thm)], ['22', '31', '32', '33'])).
% 0.46/0.71  thf('35', plain,
% 0.46/0.71      ((((u1_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 0.46/0.71          = (u1_struct_0 @ sk_B))
% 0.46/0.71        | (v2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))
% 0.46/0.71        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 0.46/0.71        | (v2_struct_0 @ sk_B))),
% 0.46/0.71      inference('simplify', [status(thm)], ['34'])).
% 0.46/0.71  thf('36', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('37', plain,
% 0.46/0.71      (![X33 : $i, X34 : $i]:
% 0.46/0.71         ((v2_struct_0 @ X33)
% 0.46/0.71          | ~ (m1_pre_topc @ X33 @ X34)
% 0.46/0.71          | ((k1_tsep_1 @ X34 @ X33 @ X33)
% 0.46/0.71              = (g1_pre_topc @ (u1_struct_0 @ X33) @ (u1_pre_topc @ X33)))
% 0.46/0.71          | ~ (l1_pre_topc @ X34)
% 0.46/0.71          | ~ (v2_pre_topc @ X34)
% 0.46/0.71          | (v2_struct_0 @ X34))),
% 0.46/0.71      inference('cnf', [status(esa)], [t25_tmap_1])).
% 0.46/0.71  thf('38', plain,
% 0.46/0.71      (((v2_struct_0 @ sk_B)
% 0.46/0.71        | ~ (v2_pre_topc @ sk_B)
% 0.46/0.71        | ~ (l1_pre_topc @ sk_B)
% 0.46/0.71        | ((k1_tsep_1 @ sk_B @ sk_C @ sk_C)
% 0.46/0.71            = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.46/0.71        | (v2_struct_0 @ sk_C))),
% 0.46/0.71      inference('sup-', [status(thm)], ['36', '37'])).
% 0.46/0.71  thf('39', plain, ((v2_pre_topc @ sk_B)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('40', plain, ((l1_pre_topc @ sk_B)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('41', plain,
% 0.46/0.71      (((v2_struct_0 @ sk_B)
% 0.46/0.71        | ((k1_tsep_1 @ sk_B @ sk_C @ sk_C)
% 0.46/0.71            = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.46/0.71        | (v2_struct_0 @ sk_C))),
% 0.46/0.71      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.46/0.71  thf('42', plain, (~ (v2_struct_0 @ sk_B)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('43', plain,
% 0.46/0.71      (((v2_struct_0 @ sk_C)
% 0.46/0.71        | ((k1_tsep_1 @ sk_B @ sk_C @ sk_C)
% 0.46/0.71            = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))))),
% 0.46/0.71      inference('clc', [status(thm)], ['41', '42'])).
% 0.46/0.71  thf('44', plain, (~ (v2_struct_0 @ sk_C)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('45', plain,
% 0.46/0.71      (((k1_tsep_1 @ sk_B @ sk_C @ sk_C)
% 0.46/0.71         = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.46/0.71      inference('clc', [status(thm)], ['43', '44'])).
% 0.46/0.71  thf('46', plain,
% 0.46/0.71      (((k1_tsep_1 @ sk_B @ sk_B @ sk_B)
% 0.46/0.71         = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.46/0.71      inference('clc', [status(thm)], ['16', '17'])).
% 0.46/0.71  thf('47', plain,
% 0.46/0.71      (((k1_tsep_1 @ sk_B @ sk_B @ sk_B) = (k1_tsep_1 @ sk_B @ sk_C @ sk_C))),
% 0.46/0.71      inference('sup+', [status(thm)], ['45', '46'])).
% 0.46/0.71  thf('48', plain,
% 0.46/0.71      (((k1_tsep_1 @ sk_B @ sk_B @ sk_B) = (k1_tsep_1 @ sk_B @ sk_C @ sk_C))),
% 0.46/0.71      inference('sup+', [status(thm)], ['45', '46'])).
% 0.46/0.71  thf('49', plain,
% 0.46/0.71      ((((u1_struct_0 @ (k1_tsep_1 @ sk_B @ sk_C @ sk_C))
% 0.46/0.71          = (u1_struct_0 @ sk_B))
% 0.46/0.71        | (v2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_C @ sk_C))
% 0.46/0.71        | ~ (m1_pre_topc @ sk_B @ sk_B)
% 0.46/0.71        | (v2_struct_0 @ sk_B))),
% 0.46/0.71      inference('demod', [status(thm)], ['35', '47', '48'])).
% 0.46/0.71  thf('50', plain,
% 0.46/0.71      ((~ (l1_pre_topc @ sk_B)
% 0.46/0.71        | (v2_struct_0 @ sk_B)
% 0.46/0.71        | (v2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_C @ sk_C))
% 0.46/0.71        | ((u1_struct_0 @ (k1_tsep_1 @ sk_B @ sk_C @ sk_C))
% 0.46/0.71            = (u1_struct_0 @ sk_B)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['2', '49'])).
% 0.46/0.71  thf('51', plain, ((l1_pre_topc @ sk_B)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('52', plain,
% 0.46/0.71      (((v2_struct_0 @ sk_B)
% 0.46/0.71        | (v2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_C @ sk_C))
% 0.46/0.71        | ((u1_struct_0 @ (k1_tsep_1 @ sk_B @ sk_C @ sk_C))
% 0.46/0.71            = (u1_struct_0 @ sk_B)))),
% 0.46/0.71      inference('demod', [status(thm)], ['50', '51'])).
% 0.46/0.71  thf('53', plain, (~ (v2_struct_0 @ sk_B)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('54', plain,
% 0.46/0.71      ((((u1_struct_0 @ (k1_tsep_1 @ sk_B @ sk_C @ sk_C))
% 0.46/0.71          = (u1_struct_0 @ sk_B))
% 0.46/0.71        | (v2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_C @ sk_C)))),
% 0.46/0.71      inference('clc', [status(thm)], ['52', '53'])).
% 0.46/0.71  thf('55', plain,
% 0.46/0.71      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.46/0.71         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('56', plain,
% 0.46/0.71      (![X16 : $i]:
% 0.46/0.71         (~ (v2_struct_0 @ 
% 0.46/0.71             (g1_pre_topc @ (u1_struct_0 @ X16) @ (u1_pre_topc @ X16)))
% 0.46/0.71          | ~ (l1_pre_topc @ X16)
% 0.46/0.71          | (v2_struct_0 @ X16))),
% 0.46/0.71      inference('cnf', [status(esa)], [fc7_pre_topc])).
% 0.46/0.71  thf('57', plain,
% 0.46/0.71      ((~ (v2_struct_0 @ 
% 0.46/0.71           (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.46/0.71        | (v2_struct_0 @ sk_B)
% 0.46/0.71        | ~ (l1_pre_topc @ sk_B))),
% 0.46/0.71      inference('sup-', [status(thm)], ['55', '56'])).
% 0.46/0.71  thf('58', plain, ((l1_pre_topc @ sk_B)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('59', plain,
% 0.46/0.71      ((~ (v2_struct_0 @ 
% 0.46/0.71           (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.46/0.71        | (v2_struct_0 @ sk_B))),
% 0.46/0.71      inference('demod', [status(thm)], ['57', '58'])).
% 0.46/0.71  thf('60', plain, (~ (v2_struct_0 @ sk_B)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('61', plain,
% 0.46/0.71      (~ (v2_struct_0 @ 
% 0.46/0.71          (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.46/0.71      inference('clc', [status(thm)], ['59', '60'])).
% 0.46/0.71  thf('62', plain,
% 0.46/0.71      (((k1_tsep_1 @ sk_B @ sk_B @ sk_B)
% 0.46/0.71         = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.46/0.71      inference('clc', [status(thm)], ['16', '17'])).
% 0.46/0.71  thf('63', plain, (~ (v2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))),
% 0.46/0.71      inference('demod', [status(thm)], ['61', '62'])).
% 0.46/0.71  thf('64', plain,
% 0.46/0.71      (((k1_tsep_1 @ sk_B @ sk_B @ sk_B) = (k1_tsep_1 @ sk_B @ sk_C @ sk_C))),
% 0.46/0.71      inference('sup+', [status(thm)], ['45', '46'])).
% 0.46/0.71  thf('65', plain, (~ (v2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_C @ sk_C))),
% 0.46/0.71      inference('demod', [status(thm)], ['63', '64'])).
% 0.46/0.71  thf('66', plain,
% 0.46/0.71      (((u1_struct_0 @ (k1_tsep_1 @ sk_B @ sk_C @ sk_C)) = (u1_struct_0 @ sk_B))),
% 0.46/0.71      inference('clc', [status(thm)], ['54', '65'])).
% 0.46/0.71  thf('67', plain, ((m1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B) @ sk_B)),
% 0.46/0.71      inference('demod', [status(thm)], ['7', '18'])).
% 0.46/0.71  thf('68', plain,
% 0.46/0.71      (((k1_tsep_1 @ sk_B @ sk_B @ sk_B) = (k1_tsep_1 @ sk_B @ sk_C @ sk_C))),
% 0.46/0.71      inference('sup+', [status(thm)], ['45', '46'])).
% 0.46/0.71  thf('69', plain, ((m1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_C @ sk_C) @ sk_B)),
% 0.46/0.71      inference('demod', [status(thm)], ['67', '68'])).
% 0.46/0.71  thf('70', plain,
% 0.46/0.71      (![X23 : $i, X24 : $i, X26 : $i]:
% 0.46/0.71         ((v2_struct_0 @ X24)
% 0.46/0.71          | ~ (l1_pre_topc @ X24)
% 0.46/0.71          | (v2_struct_0 @ X26)
% 0.46/0.71          | ~ (m1_pre_topc @ X26 @ X24)
% 0.46/0.71          | ((u1_struct_0 @ (k1_tsep_1 @ X24 @ X23 @ X26))
% 0.46/0.71              = (k2_xboole_0 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X26)))
% 0.46/0.71          | ~ (m1_pre_topc @ (k1_tsep_1 @ X24 @ X23 @ X26) @ X24)
% 0.46/0.71          | ~ (v1_pre_topc @ (k1_tsep_1 @ X24 @ X23 @ X26))
% 0.46/0.71          | (v2_struct_0 @ (k1_tsep_1 @ X24 @ X23 @ X26))
% 0.46/0.71          | ~ (m1_pre_topc @ X23 @ X24)
% 0.46/0.71          | (v2_struct_0 @ X23))),
% 0.46/0.71      inference('simplify', [status(thm)], ['20'])).
% 0.46/0.71  thf('71', plain,
% 0.46/0.71      (((v2_struct_0 @ sk_C)
% 0.46/0.71        | ~ (m1_pre_topc @ sk_C @ sk_B)
% 0.46/0.71        | (v2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_C @ sk_C))
% 0.46/0.71        | ~ (v1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_C @ sk_C))
% 0.46/0.71        | ((u1_struct_0 @ (k1_tsep_1 @ sk_B @ sk_C @ sk_C))
% 0.46/0.71            = (k2_xboole_0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_C)))
% 0.46/0.71        | ~ (m1_pre_topc @ sk_C @ sk_B)
% 0.46/0.71        | (v2_struct_0 @ sk_C)
% 0.46/0.71        | ~ (l1_pre_topc @ sk_B)
% 0.46/0.71        | (v2_struct_0 @ sk_B))),
% 0.46/0.71      inference('sup-', [status(thm)], ['69', '70'])).
% 0.46/0.71  thf('72', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('73', plain, ((v1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B))),
% 0.46/0.71      inference('demod', [status(thm)], ['29', '30'])).
% 0.46/0.71  thf('74', plain,
% 0.46/0.71      (((k1_tsep_1 @ sk_B @ sk_B @ sk_B) = (k1_tsep_1 @ sk_B @ sk_C @ sk_C))),
% 0.46/0.71      inference('sup+', [status(thm)], ['45', '46'])).
% 0.46/0.71  thf('75', plain, ((v1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_C @ sk_C))),
% 0.46/0.71      inference('demod', [status(thm)], ['73', '74'])).
% 0.46/0.71  thf('76', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.46/0.71      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.46/0.71  thf('77', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('78', plain, ((l1_pre_topc @ sk_B)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('79', plain,
% 0.46/0.71      (((v2_struct_0 @ sk_C)
% 0.46/0.71        | (v2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_C @ sk_C))
% 0.46/0.71        | ((u1_struct_0 @ (k1_tsep_1 @ sk_B @ sk_C @ sk_C))
% 0.46/0.71            = (u1_struct_0 @ sk_C))
% 0.46/0.71        | (v2_struct_0 @ sk_C)
% 0.46/0.71        | (v2_struct_0 @ sk_B))),
% 0.46/0.71      inference('demod', [status(thm)], ['71', '72', '75', '76', '77', '78'])).
% 0.46/0.71  thf('80', plain,
% 0.46/0.71      (((v2_struct_0 @ sk_B)
% 0.46/0.71        | ((u1_struct_0 @ (k1_tsep_1 @ sk_B @ sk_C @ sk_C))
% 0.46/0.71            = (u1_struct_0 @ sk_C))
% 0.46/0.71        | (v2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_C @ sk_C))
% 0.46/0.71        | (v2_struct_0 @ sk_C))),
% 0.46/0.71      inference('simplify', [status(thm)], ['79'])).
% 0.46/0.71  thf('81', plain,
% 0.46/0.71      ((((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))
% 0.46/0.71        | (v2_struct_0 @ sk_C)
% 0.46/0.71        | (v2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_C @ sk_C))
% 0.46/0.71        | (v2_struct_0 @ sk_B))),
% 0.46/0.71      inference('sup+', [status(thm)], ['66', '80'])).
% 0.46/0.71  thf('82', plain, (~ (v2_struct_0 @ (k1_tsep_1 @ sk_B @ sk_C @ sk_C))),
% 0.46/0.71      inference('demod', [status(thm)], ['63', '64'])).
% 0.46/0.71  thf('83', plain,
% 0.46/0.71      (((v2_struct_0 @ sk_B)
% 0.46/0.71        | (v2_struct_0 @ sk_C)
% 0.46/0.71        | ((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['81', '82'])).
% 0.46/0.71  thf('84', plain, (~ (v2_struct_0 @ sk_B)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('85', plain,
% 0.46/0.71      ((((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C)) | (v2_struct_0 @ sk_C))),
% 0.46/0.71      inference('clc', [status(thm)], ['83', '84'])).
% 0.46/0.71  thf('86', plain, (~ (v2_struct_0 @ sk_C)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('87', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.46/0.71      inference('clc', [status(thm)], ['85', '86'])).
% 0.46/0.71  thf('88', plain,
% 0.46/0.71      ((m1_subset_1 @ sk_D @ 
% 0.46/0.71        (k1_zfmisc_1 @ 
% 0.46/0.71         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.46/0.71      inference('demod', [status(thm)], ['1', '87'])).
% 0.46/0.71  thf('89', plain,
% 0.46/0.71      ((m1_subset_1 @ sk_D @ 
% 0.46/0.71        (k1_zfmisc_1 @ 
% 0.46/0.71         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf(reflexivity_r1_funct_2, axiom,
% 0.46/0.71    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.46/0.71     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 0.46/0.71         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 0.46/0.71         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.46/0.71         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 0.46/0.71         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.46/0.71       ( r1_funct_2 @ A @ B @ C @ D @ E @ E ) ))).
% 0.46/0.71  thf('90', plain,
% 0.46/0.71      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.46/0.71         ((r1_funct_2 @ X17 @ X18 @ X19 @ X20 @ X21 @ X21)
% 0.46/0.71          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.46/0.71          | ~ (v1_funct_2 @ X21 @ X17 @ X18)
% 0.46/0.71          | ~ (v1_funct_1 @ X21)
% 0.46/0.71          | (v1_xboole_0 @ X20)
% 0.46/0.71          | (v1_xboole_0 @ X18)
% 0.46/0.71          | ~ (v1_funct_1 @ X22)
% 0.46/0.71          | ~ (v1_funct_2 @ X22 @ X19 @ X20)
% 0.46/0.71          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.46/0.71      inference('cnf', [status(esa)], [reflexivity_r1_funct_2])).
% 0.46/0.71  thf('91', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.71         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.46/0.71          | ~ (v1_funct_2 @ X2 @ X1 @ X0)
% 0.46/0.71          | ~ (v1_funct_1 @ X2)
% 0.46/0.71          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.71          | (v1_xboole_0 @ X0)
% 0.46/0.71          | ~ (v1_funct_1 @ sk_D)
% 0.46/0.71          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.46/0.71          | (r1_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ X1 @ 
% 0.46/0.71             X0 @ sk_D @ sk_D))),
% 0.46/0.71      inference('sup-', [status(thm)], ['89', '90'])).
% 0.46/0.71  thf('92', plain, ((v1_funct_1 @ sk_D)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('93', plain,
% 0.46/0.71      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('94', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.71         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.46/0.71          | ~ (v1_funct_2 @ X2 @ X1 @ X0)
% 0.46/0.71          | ~ (v1_funct_1 @ X2)
% 0.46/0.71          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.71          | (v1_xboole_0 @ X0)
% 0.46/0.71          | (r1_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ X1 @ 
% 0.46/0.71             X0 @ sk_D @ sk_D))),
% 0.46/0.71      inference('demod', [status(thm)], ['91', '92', '93'])).
% 0.46/0.71  thf('95', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.46/0.71      inference('clc', [status(thm)], ['85', '86'])).
% 0.46/0.71  thf('96', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.71         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.46/0.71          | ~ (v1_funct_2 @ X2 @ X1 @ X0)
% 0.46/0.71          | ~ (v1_funct_1 @ X2)
% 0.46/0.71          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.71          | (v1_xboole_0 @ X0)
% 0.46/0.71          | (r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ X1 @ 
% 0.46/0.71             X0 @ sk_D @ sk_D))),
% 0.46/0.71      inference('demod', [status(thm)], ['94', '95'])).
% 0.46/0.71  thf('97', plain,
% 0.46/0.71      (((r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.71         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)
% 0.46/0.71        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.71        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.71        | ~ (v1_funct_1 @ sk_D)
% 0.46/0.71        | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['88', '96'])).
% 0.46/0.71  thf('98', plain, ((v1_funct_1 @ sk_D)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('99', plain,
% 0.46/0.71      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('100', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.46/0.71      inference('clc', [status(thm)], ['85', '86'])).
% 0.46/0.71  thf('101', plain,
% 0.46/0.71      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.46/0.71      inference('demod', [status(thm)], ['99', '100'])).
% 0.46/0.71  thf('102', plain,
% 0.46/0.71      (((r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.71         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)
% 0.46/0.71        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.71        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.71      inference('demod', [status(thm)], ['97', '98', '101'])).
% 0.46/0.71  thf('103', plain,
% 0.46/0.71      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.71        | (r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.71           (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.46/0.71      inference('simplify', [status(thm)], ['102'])).
% 0.46/0.71  thf('104', plain,
% 0.46/0.71      (~ (r1_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.71          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.46/0.71          (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('105', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.46/0.71      inference('clc', [status(thm)], ['85', '86'])).
% 0.46/0.71  thf('106', plain,
% 0.46/0.71      (~ (r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.71          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.46/0.71          (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.46/0.71      inference('demod', [status(thm)], ['104', '105'])).
% 0.46/0.71  thf('107', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('108', plain,
% 0.46/0.71      ((m1_subset_1 @ sk_D @ 
% 0.46/0.71        (k1_zfmisc_1 @ 
% 0.46/0.71         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf(d4_tmap_1, axiom,
% 0.46/0.71    (![A:$i]:
% 0.46/0.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.71       ( ![B:$i]:
% 0.46/0.71         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.46/0.71             ( l1_pre_topc @ B ) ) =>
% 0.46/0.71           ( ![C:$i]:
% 0.46/0.71             ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.71                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.46/0.71                 ( m1_subset_1 @
% 0.46/0.71                   C @ 
% 0.46/0.71                   ( k1_zfmisc_1 @
% 0.46/0.71                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.46/0.71               ( ![D:$i]:
% 0.46/0.71                 ( ( m1_pre_topc @ D @ A ) =>
% 0.46/0.71                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.46/0.71                     ( k2_partfun1 @
% 0.46/0.71                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.46/0.71                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.71  thf('109', plain,
% 0.46/0.71      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.46/0.71         ((v2_struct_0 @ X27)
% 0.46/0.71          | ~ (v2_pre_topc @ X27)
% 0.46/0.71          | ~ (l1_pre_topc @ X27)
% 0.46/0.71          | ~ (m1_pre_topc @ X28 @ X29)
% 0.46/0.71          | ((k2_tmap_1 @ X29 @ X27 @ X30 @ X28)
% 0.46/0.71              = (k2_partfun1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X27) @ 
% 0.46/0.71                 X30 @ (u1_struct_0 @ X28)))
% 0.46/0.71          | ~ (m1_subset_1 @ X30 @ 
% 0.46/0.71               (k1_zfmisc_1 @ 
% 0.46/0.71                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X27))))
% 0.46/0.71          | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X27))
% 0.46/0.71          | ~ (v1_funct_1 @ X30)
% 0.46/0.71          | ~ (l1_pre_topc @ X29)
% 0.46/0.71          | ~ (v2_pre_topc @ X29)
% 0.46/0.71          | (v2_struct_0 @ X29))),
% 0.46/0.71      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.46/0.71  thf('110', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         ((v2_struct_0 @ sk_B)
% 0.46/0.71          | ~ (v2_pre_topc @ sk_B)
% 0.46/0.71          | ~ (l1_pre_topc @ sk_B)
% 0.46/0.71          | ~ (v1_funct_1 @ sk_D)
% 0.46/0.71          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.46/0.71          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.46/0.71              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.71                 sk_D @ (u1_struct_0 @ X0)))
% 0.46/0.71          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.46/0.71          | ~ (l1_pre_topc @ sk_A)
% 0.46/0.71          | ~ (v2_pre_topc @ sk_A)
% 0.46/0.71          | (v2_struct_0 @ sk_A))),
% 0.46/0.71      inference('sup-', [status(thm)], ['108', '109'])).
% 0.46/0.71  thf('111', plain, ((v2_pre_topc @ sk_B)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('112', plain, ((l1_pre_topc @ sk_B)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('113', plain, ((v1_funct_1 @ sk_D)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('114', plain,
% 0.46/0.71      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('115', plain,
% 0.46/0.71      ((m1_subset_1 @ sk_D @ 
% 0.46/0.71        (k1_zfmisc_1 @ 
% 0.46/0.71         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf(redefinition_k2_partfun1, axiom,
% 0.46/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.71     ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.71         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.71       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.46/0.71  thf('116', plain,
% 0.46/0.71      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.71         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 0.46/0.71          | ~ (v1_funct_1 @ X9)
% 0.46/0.71          | ((k2_partfun1 @ X10 @ X11 @ X9 @ X12) = (k7_relat_1 @ X9 @ X12)))),
% 0.46/0.71      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.46/0.71  thf('117', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         (((k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.46/0.71            X0) = (k7_relat_1 @ sk_D @ X0))
% 0.46/0.71          | ~ (v1_funct_1 @ sk_D))),
% 0.46/0.71      inference('sup-', [status(thm)], ['115', '116'])).
% 0.46/0.71  thf('118', plain, ((v1_funct_1 @ sk_D)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('119', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         ((k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.46/0.71           X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.46/0.71      inference('demod', [status(thm)], ['117', '118'])).
% 0.46/0.71  thf('120', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('121', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('122', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         ((v2_struct_0 @ sk_B)
% 0.46/0.71          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.46/0.71              = (k7_relat_1 @ sk_D @ (u1_struct_0 @ X0)))
% 0.46/0.71          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.46/0.71          | (v2_struct_0 @ sk_A))),
% 0.46/0.71      inference('demod', [status(thm)],
% 0.46/0.71                ['110', '111', '112', '113', '114', '119', '120', '121'])).
% 0.46/0.71  thf('123', plain,
% 0.46/0.71      (((v2_struct_0 @ sk_A)
% 0.46/0.71        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.46/0.71            = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))
% 0.46/0.71        | (v2_struct_0 @ sk_B))),
% 0.46/0.71      inference('sup-', [status(thm)], ['107', '122'])).
% 0.46/0.71  thf('124', plain,
% 0.46/0.71      ((m1_subset_1 @ sk_D @ 
% 0.46/0.71        (k1_zfmisc_1 @ 
% 0.46/0.71         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf(cc2_relset_1, axiom,
% 0.46/0.71    (![A:$i,B:$i,C:$i]:
% 0.46/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.71       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.46/0.71  thf('125', plain,
% 0.46/0.71      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.46/0.71         ((v4_relat_1 @ X6 @ X7)
% 0.46/0.71          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.46/0.71      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.71  thf('126', plain, ((v4_relat_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.46/0.71      inference('sup-', [status(thm)], ['124', '125'])).
% 0.46/0.71  thf(t209_relat_1, axiom,
% 0.46/0.71    (![A:$i,B:$i]:
% 0.46/0.71     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.46/0.71       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.46/0.71  thf('127', plain,
% 0.46/0.71      (![X1 : $i, X2 : $i]:
% 0.46/0.71         (((X1) = (k7_relat_1 @ X1 @ X2))
% 0.46/0.71          | ~ (v4_relat_1 @ X1 @ X2)
% 0.46/0.71          | ~ (v1_relat_1 @ X1))),
% 0.46/0.71      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.46/0.71  thf('128', plain,
% 0.46/0.71      ((~ (v1_relat_1 @ sk_D)
% 0.46/0.71        | ((sk_D) = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_B))))),
% 0.46/0.71      inference('sup-', [status(thm)], ['126', '127'])).
% 0.46/0.71  thf('129', plain,
% 0.46/0.71      ((m1_subset_1 @ sk_D @ 
% 0.46/0.71        (k1_zfmisc_1 @ 
% 0.46/0.71         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf(cc1_relset_1, axiom,
% 0.46/0.71    (![A:$i,B:$i,C:$i]:
% 0.46/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.71       ( v1_relat_1 @ C ) ))).
% 0.46/0.71  thf('130', plain,
% 0.46/0.71      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.46/0.71         ((v1_relat_1 @ X3)
% 0.46/0.71          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 0.46/0.71      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.46/0.71  thf('131', plain, ((v1_relat_1 @ sk_D)),
% 0.46/0.71      inference('sup-', [status(thm)], ['129', '130'])).
% 0.46/0.71  thf('132', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_B)))),
% 0.46/0.71      inference('demod', [status(thm)], ['128', '131'])).
% 0.46/0.71  thf('133', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.46/0.71      inference('clc', [status(thm)], ['85', '86'])).
% 0.46/0.71  thf('134', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.46/0.71      inference('demod', [status(thm)], ['132', '133'])).
% 0.46/0.71  thf('135', plain,
% 0.46/0.71      (((v2_struct_0 @ sk_A)
% 0.46/0.71        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) = (sk_D))
% 0.46/0.71        | (v2_struct_0 @ sk_B))),
% 0.46/0.71      inference('demod', [status(thm)], ['123', '134'])).
% 0.46/0.71  thf('136', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('137', plain,
% 0.46/0.71      (((v2_struct_0 @ sk_B)
% 0.46/0.71        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) = (sk_D)))),
% 0.46/0.71      inference('clc', [status(thm)], ['135', '136'])).
% 0.46/0.71  thf('138', plain, (~ (v2_struct_0 @ sk_B)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('139', plain, (((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C) = (sk_D))),
% 0.46/0.71      inference('clc', [status(thm)], ['137', '138'])).
% 0.46/0.71  thf('140', plain,
% 0.46/0.71      (~ (r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.71          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)),
% 0.46/0.71      inference('demod', [status(thm)], ['106', '139'])).
% 0.46/0.71  thf('141', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.46/0.71      inference('clc', [status(thm)], ['103', '140'])).
% 0.46/0.71  thf(fc2_struct_0, axiom,
% 0.46/0.71    (![A:$i]:
% 0.46/0.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.46/0.71       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.46/0.71  thf('142', plain,
% 0.46/0.71      (![X14 : $i]:
% 0.46/0.71         (~ (v1_xboole_0 @ (u1_struct_0 @ X14))
% 0.46/0.71          | ~ (l1_struct_0 @ X14)
% 0.46/0.71          | (v2_struct_0 @ X14))),
% 0.46/0.71      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.46/0.71  thf('143', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.71      inference('sup-', [status(thm)], ['141', '142'])).
% 0.46/0.71  thf('144', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf(dt_l1_pre_topc, axiom,
% 0.46/0.71    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.46/0.71  thf('145', plain,
% 0.46/0.71      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 0.46/0.71      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.46/0.71  thf('146', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.71      inference('sup-', [status(thm)], ['144', '145'])).
% 0.46/0.71  thf('147', plain, ((v2_struct_0 @ sk_A)),
% 0.46/0.71      inference('demod', [status(thm)], ['143', '146'])).
% 0.46/0.71  thf('148', plain, ($false), inference('demod', [status(thm)], ['0', '147'])).
% 0.46/0.71  
% 0.46/0.71  % SZS output end Refutation
% 0.46/0.71  
% 0.46/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
