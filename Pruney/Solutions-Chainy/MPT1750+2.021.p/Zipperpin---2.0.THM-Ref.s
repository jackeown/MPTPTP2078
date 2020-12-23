%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KyEbZtmgyn

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:42 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  200 (1597 expanded)
%              Number of leaves         :   46 ( 474 expanded)
%              Depth                    :   27
%              Number of atoms          : 1776 (46681 expanded)
%              Number of equality atoms :   52 ( 894 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

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

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('3',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X23 @ X24 @ X25 )
      | ~ ( v1_funct_1 @ X23 )
      | ( v1_xboole_0 @ X26 )
      | ( v1_xboole_0 @ X25 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_2 @ X27 @ X28 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X26 ) ) )
      | ( r1_funct_2 @ X24 @ X25 @ X28 @ X26 @ X23 @ X27 )
      | ( X23 != X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_funct_2])).

thf('4',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( r1_funct_2 @ X24 @ X25 @ X28 @ X26 @ X27 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X28 @ X26 )
      | ( v1_xboole_0 @ X25 )
      | ( v1_xboole_0 @ X26 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_2 @ X27 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_D @ X1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_funct_2 @ X1 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_D @ X1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ( r1_funct_2 @ X1 @ X0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('10',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('14',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_pre_topc @ X38 @ X39 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X38 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('15',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('18',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('19',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('23',plain,(
    ! [X43: $i,X44: $i] :
      ( ( v2_struct_0 @ X43 )
      | ~ ( m1_pre_topc @ X43 @ X44 )
      | ( ( k1_tsep_1 @ X44 @ X43 @ X43 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X43 ) @ ( u1_pre_topc @ X43 ) ) )
      | ~ ( l1_pre_topc @ X44 )
      | ~ ( v2_pre_topc @ X44 )
      | ( v2_struct_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t25_tmap_1])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( ( k1_tsep_1 @ sk_B @ sk_C @ sk_C )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k1_tsep_1 @ sk_B @ sk_C @ sk_C )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( ( k1_tsep_1 @ sk_B @ sk_C @ sk_C )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k1_tsep_1 @ sk_B @ sk_C @ sk_C )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf(t23_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ( m1_pre_topc @ B @ C )
              <=> ( ( k1_tsep_1 @ A @ B @ C )
                  = ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) ) ) ) ) )).

thf('32',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( v2_struct_0 @ X40 )
      | ~ ( m1_pre_topc @ X40 @ X41 )
      | ( ( k1_tsep_1 @ X41 @ X40 @ X42 )
       != ( g1_pre_topc @ ( u1_struct_0 @ X42 ) @ ( u1_pre_topc @ X42 ) ) )
      | ( m1_pre_topc @ X40 @ X42 )
      | ~ ( m1_pre_topc @ X42 @ X41 )
      | ( v2_struct_0 @ X42 )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v2_pre_topc @ X41 )
      | ( v2_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t23_tsep_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tsep_1 @ X1 @ X0 @ sk_C )
       != ( k1_tsep_1 @ sk_B @ sk_C @ sk_C ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ X1 )
      | ( m1_pre_topc @ X0 @ sk_C )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_B )
    | ( m1_pre_topc @ sk_C @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference(eq_res,[status(thm)],['33'])).

thf('35',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( m1_pre_topc @ sk_C @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_pre_topc @ sk_C @ sk_C )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['35','36','37','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( m1_pre_topc @ sk_C @ sk_C ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference(clc,[status(thm)],['41','42'])).

thf(t11_tmap_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
            & ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) )).

thf('44',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_pre_topc @ X33 @ X34 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X33 ) @ ( u1_pre_topc @ X33 ) ) @ X34 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t11_tmap_1])).

thf('45',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('47',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( l1_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('48',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k1_tsep_1 @ sk_B @ sk_C @ sk_C )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('52',plain,(
    m1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_C @ sk_C ) @ sk_C ),
    inference(demod,[status(thm)],['45','50','51'])).

thf('53',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_tmap_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v2_pre_topc @ C )
                & ( l1_pre_topc @ C ) )
             => ( ( B
                  = ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) )
               => ( ( m1_pre_topc @ B @ A )
                <=> ( m1_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('54',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( v2_pre_topc @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ( X35
       != ( g1_pre_topc @ ( u1_struct_0 @ X36 ) @ ( u1_pre_topc @ X36 ) ) )
      | ~ ( m1_pre_topc @ X35 @ X37 )
      | ( m1_pre_topc @ X36 @ X37 )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t12_tmap_1])).

thf('55',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X36 )
      | ~ ( l1_pre_topc @ X36 )
      | ( m1_pre_topc @ X36 @ X37 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X36 ) @ ( u1_pre_topc @ X36 ) ) @ X37 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X36 ) @ ( u1_pre_topc @ X36 ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X36 ) @ ( u1_pre_topc @ X36 ) ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ X0 )
      | ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','55'])).

thf('57',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_pre_topc @ X33 @ X34 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X33 ) @ ( u1_pre_topc @ X33 ) ) @ X34 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t11_tmap_1])).

thf('59',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( l1_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('63',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc6_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
        & ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('68',plain,(
    ! [X22: $i] :
      ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X22 ) @ ( u1_pre_topc @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf('69',plain,
    ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) @ X0 )
      | ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['56','65','66','72','73','74','75'])).

thf('77',plain,(
    m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['59','60'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) @ X0 )
      | ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['56','65','66','72','73','74','75'])).

thf('79',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_pre_topc @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    m1_pre_topc @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X43: $i,X44: $i] :
      ( ( v2_struct_0 @ X43 )
      | ~ ( m1_pre_topc @ X43 @ X44 )
      | ( ( k1_tsep_1 @ X44 @ X43 @ X43 )
        = ( g1_pre_topc @ ( u1_struct_0 @ X43 ) @ ( u1_pre_topc @ X43 ) ) )
      | ~ ( l1_pre_topc @ X44 )
      | ~ ( v2_pre_topc @ X44 )
      | ( v2_struct_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t25_tmap_1])).

thf('83',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( ( k1_tsep_1 @ sk_B @ sk_B @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k1_tsep_1 @ sk_B @ sk_B @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['83','84','85','86'])).

thf('88',plain,
    ( ( ( k1_tsep_1 @ sk_B @ sk_B @ sk_B )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( k1_tsep_1 @ sk_B @ sk_B @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_B @ sk_B ) @ X0 )
      | ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['76','90'])).

thf('92',plain,
    ( ( k1_tsep_1 @ sk_B @ sk_C @ sk_C )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('93',plain,
    ( ( k1_tsep_1 @ sk_B @ sk_B @ sk_B )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('94',plain,
    ( ( k1_tsep_1 @ sk_B @ sk_B @ sk_B )
    = ( k1_tsep_1 @ sk_B @ sk_C @ sk_C ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ ( k1_tsep_1 @ sk_B @ sk_C @ sk_C ) @ X0 )
      | ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['91','94'])).

thf('96',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( m1_pre_topc @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['52','95'])).

thf('97',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['48','49'])).

thf('98',plain,(
    m1_pre_topc @ sk_B @ sk_C ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_pre_topc @ X38 @ X39 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X38 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('100',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['48','49'])).

thf('102',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('104',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['21','104'])).

thf('106',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['21','104'])).

thf('107',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ),
    inference(demod,[status(thm)],['12','105','106'])).

thf('108',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
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

thf('111',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( m1_pre_topc @ X30 @ X31 )
      | ( ( k2_tmap_1 @ X31 @ X29 @ X32 @ X30 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X29 ) @ X32 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X29 ) ) ) )
      | ~ ( v1_funct_2 @ X32 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X29 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('112',plain,(
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
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('118',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ( ( k2_partfun1 @ X15 @ X16 @ X14 @ X17 )
        = ( k7_relat_1 @ X14 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['112','113','114','115','116','121','122','123'])).

thf('125',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['109','124'])).

thf('126',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('128',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
    = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['127','128'])).

thf('130',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['108','129'])).

thf('131',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['21','104'])).

thf('132',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('134',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v4_relat_1 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('135',plain,(
    v4_relat_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('136',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X6
        = ( k7_relat_1 @ X6 @ X7 ) )
      | ~ ( v4_relat_1 @ X6 @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('137',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('139',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('140',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['137','140'])).

thf('142',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['21','104'])).

thf('143',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ),
    inference(demod,[status(thm)],['132','143'])).

thf('145',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['107','144'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('146',plain,(
    ! [X21: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('147',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('149',plain,(
    ! [X18: $i] :
      ( ( l1_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('150',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['147','150'])).

thf('152',plain,(
    $false ),
    inference(demod,[status(thm)],['0','151'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KyEbZtmgyn
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:55:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.58  % Solved by: fo/fo7.sh
% 0.39/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.58  % done 215 iterations in 0.124s
% 0.39/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.58  % SZS output start Refutation
% 0.39/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.58  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.39/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.58  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.39/0.58  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 0.39/0.58  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.39/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.58  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 0.39/0.58  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.39/0.58  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.39/0.58  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.39/0.58  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.39/0.58  thf(sk_D_type, type, sk_D: $i).
% 0.39/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.39/0.58  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.39/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.39/0.58  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.39/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.39/0.58  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.39/0.58  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.39/0.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.39/0.58  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.39/0.58  thf(t60_tmap_1, conjecture,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.39/0.58             ( l1_pre_topc @ B ) ) =>
% 0.39/0.58           ( ![C:$i]:
% 0.39/0.58             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.39/0.58               ( ![D:$i]:
% 0.39/0.58                 ( ( ( v1_funct_1 @ D ) & 
% 0.39/0.58                     ( v1_funct_2 @
% 0.39/0.58                       D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.39/0.58                     ( m1_subset_1 @
% 0.39/0.58                       D @ 
% 0.39/0.58                       ( k1_zfmisc_1 @
% 0.39/0.58                         ( k2_zfmisc_1 @
% 0.39/0.58                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.39/0.58                   ( ( ( g1_pre_topc @
% 0.39/0.58                         ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.39/0.58                       ( g1_pre_topc @
% 0.39/0.58                         ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.39/0.58                     ( r1_funct_2 @
% 0.39/0.58                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.39/0.58                       ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ 
% 0.39/0.58                       ( k2_tmap_1 @ B @ A @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.58    (~( ![A:$i]:
% 0.39/0.58        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.39/0.58            ( l1_pre_topc @ A ) ) =>
% 0.39/0.58          ( ![B:$i]:
% 0.39/0.58            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.39/0.58                ( l1_pre_topc @ B ) ) =>
% 0.39/0.58              ( ![C:$i]:
% 0.39/0.58                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.39/0.58                  ( ![D:$i]:
% 0.39/0.58                    ( ( ( v1_funct_1 @ D ) & 
% 0.39/0.58                        ( v1_funct_2 @
% 0.39/0.58                          D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.39/0.58                        ( m1_subset_1 @
% 0.39/0.58                          D @ 
% 0.39/0.58                          ( k1_zfmisc_1 @
% 0.39/0.58                            ( k2_zfmisc_1 @
% 0.39/0.58                              ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.39/0.58                      ( ( ( g1_pre_topc @
% 0.39/0.58                            ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.39/0.58                          ( g1_pre_topc @
% 0.39/0.58                            ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.39/0.58                        ( r1_funct_2 @
% 0.39/0.58                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.39/0.58                          ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ 
% 0.39/0.58                          ( k2_tmap_1 @ B @ A @ D @ C ) ) ) ) ) ) ) ) ) ) )),
% 0.39/0.58    inference('cnf.neg', [status(esa)], [t60_tmap_1])).
% 0.39/0.58  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('1', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_D @ 
% 0.39/0.58        (k1_zfmisc_1 @ 
% 0.39/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('2', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_D @ 
% 0.39/0.58        (k1_zfmisc_1 @ 
% 0.39/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(redefinition_r1_funct_2, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.39/0.58     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 0.39/0.58         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 0.39/0.58         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.39/0.58         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 0.39/0.58         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.39/0.58       ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F ) <=> ( ( E ) = ( F ) ) ) ))).
% 0.39/0.58  thf('3', plain,
% 0.39/0.58      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.39/0.58          | ~ (v1_funct_2 @ X23 @ X24 @ X25)
% 0.39/0.58          | ~ (v1_funct_1 @ X23)
% 0.39/0.58          | (v1_xboole_0 @ X26)
% 0.39/0.58          | (v1_xboole_0 @ X25)
% 0.39/0.58          | ~ (v1_funct_1 @ X27)
% 0.39/0.58          | ~ (v1_funct_2 @ X27 @ X28 @ X26)
% 0.39/0.58          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X26)))
% 0.39/0.58          | (r1_funct_2 @ X24 @ X25 @ X28 @ X26 @ X23 @ X27)
% 0.39/0.58          | ((X23) != (X27)))),
% 0.39/0.58      inference('cnf', [status(esa)], [redefinition_r1_funct_2])).
% 0.39/0.58  thf('4', plain,
% 0.39/0.58      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.39/0.58         ((r1_funct_2 @ X24 @ X25 @ X28 @ X26 @ X27 @ X27)
% 0.39/0.58          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X26)))
% 0.39/0.58          | ~ (v1_funct_2 @ X27 @ X28 @ X26)
% 0.39/0.58          | (v1_xboole_0 @ X25)
% 0.39/0.58          | (v1_xboole_0 @ X26)
% 0.39/0.58          | ~ (v1_funct_1 @ X27)
% 0.39/0.58          | ~ (v1_funct_2 @ X27 @ X24 @ X25)
% 0.39/0.58          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.39/0.58      inference('simplify', [status(thm)], ['3'])).
% 0.39/0.58  thf('5', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.39/0.58          | ~ (v1_funct_2 @ sk_D @ X1 @ X0)
% 0.39/0.58          | ~ (v1_funct_1 @ sk_D)
% 0.39/0.58          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58          | (v1_xboole_0 @ X0)
% 0.39/0.58          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.39/0.58          | (r1_funct_2 @ X1 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.58             (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.39/0.58      inference('sup-', [status(thm)], ['2', '4'])).
% 0.39/0.58  thf('6', plain, ((v1_funct_1 @ sk_D)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('7', plain,
% 0.39/0.58      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('8', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.39/0.58          | ~ (v1_funct_2 @ sk_D @ X1 @ X0)
% 0.39/0.58          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58          | (v1_xboole_0 @ X0)
% 0.39/0.58          | (r1_funct_2 @ X1 @ X0 @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.58             (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.39/0.58      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.39/0.58  thf('9', plain,
% 0.39/0.58      (((r1_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.58         (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)
% 0.39/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58        | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['1', '8'])).
% 0.39/0.58  thf('10', plain,
% 0.39/0.58      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('11', plain,
% 0.39/0.58      (((r1_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.58         (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)
% 0.39/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('demod', [status(thm)], ['9', '10'])).
% 0.39/0.58  thf('12', plain,
% 0.39/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.58        | (r1_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.58           (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.39/0.58      inference('simplify', [status(thm)], ['11'])).
% 0.39/0.58  thf('13', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(t1_tsep_1, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( l1_pre_topc @ A ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( m1_pre_topc @ B @ A ) =>
% 0.39/0.58           ( m1_subset_1 @
% 0.39/0.58             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.39/0.58  thf('14', plain,
% 0.39/0.58      (![X38 : $i, X39 : $i]:
% 0.39/0.58         (~ (m1_pre_topc @ X38 @ X39)
% 0.39/0.58          | (m1_subset_1 @ (u1_struct_0 @ X38) @ 
% 0.39/0.58             (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 0.39/0.58          | ~ (l1_pre_topc @ X39))),
% 0.39/0.58      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.39/0.58  thf('15', plain,
% 0.39/0.58      ((~ (l1_pre_topc @ sk_B)
% 0.39/0.58        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.39/0.58           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['13', '14'])).
% 0.39/0.58  thf('16', plain, ((l1_pre_topc @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('17', plain,
% 0.39/0.58      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.39/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.39/0.58      inference('demod', [status(thm)], ['15', '16'])).
% 0.39/0.58  thf(t3_subset, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.39/0.58  thf('18', plain,
% 0.39/0.58      (![X3 : $i, X4 : $i]:
% 0.39/0.58         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.58  thf('19', plain, ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.39/0.58      inference('sup-', [status(thm)], ['17', '18'])).
% 0.39/0.58  thf(d10_xboole_0, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.39/0.58  thf('20', plain,
% 0.39/0.58      (![X0 : $i, X2 : $i]:
% 0.39/0.58         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.39/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.39/0.58  thf('21', plain,
% 0.39/0.58      ((~ (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.39/0.58        | ((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['19', '20'])).
% 0.39/0.58  thf('22', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(t25_tmap_1, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.39/0.58           ( ( k1_tsep_1 @ A @ B @ B ) =
% 0.39/0.58             ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ))).
% 0.39/0.58  thf('23', plain,
% 0.39/0.58      (![X43 : $i, X44 : $i]:
% 0.39/0.58         ((v2_struct_0 @ X43)
% 0.39/0.58          | ~ (m1_pre_topc @ X43 @ X44)
% 0.39/0.58          | ((k1_tsep_1 @ X44 @ X43 @ X43)
% 0.39/0.58              = (g1_pre_topc @ (u1_struct_0 @ X43) @ (u1_pre_topc @ X43)))
% 0.39/0.58          | ~ (l1_pre_topc @ X44)
% 0.39/0.58          | ~ (v2_pre_topc @ X44)
% 0.39/0.58          | (v2_struct_0 @ X44))),
% 0.39/0.58      inference('cnf', [status(esa)], [t25_tmap_1])).
% 0.39/0.58  thf('24', plain,
% 0.39/0.58      (((v2_struct_0 @ sk_B)
% 0.39/0.58        | ~ (v2_pre_topc @ sk_B)
% 0.39/0.58        | ~ (l1_pre_topc @ sk_B)
% 0.39/0.58        | ((k1_tsep_1 @ sk_B @ sk_C @ sk_C)
% 0.39/0.58            = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.39/0.58        | (v2_struct_0 @ sk_C))),
% 0.39/0.58      inference('sup-', [status(thm)], ['22', '23'])).
% 0.39/0.58  thf('25', plain, ((v2_pre_topc @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('26', plain, ((l1_pre_topc @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('27', plain,
% 0.39/0.58      (((v2_struct_0 @ sk_B)
% 0.39/0.58        | ((k1_tsep_1 @ sk_B @ sk_C @ sk_C)
% 0.39/0.58            = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.39/0.58        | (v2_struct_0 @ sk_C))),
% 0.39/0.58      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.39/0.58  thf('28', plain, (~ (v2_struct_0 @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('29', plain,
% 0.39/0.58      (((v2_struct_0 @ sk_C)
% 0.39/0.58        | ((k1_tsep_1 @ sk_B @ sk_C @ sk_C)
% 0.39/0.58            = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))))),
% 0.39/0.58      inference('clc', [status(thm)], ['27', '28'])).
% 0.39/0.58  thf('30', plain, (~ (v2_struct_0 @ sk_C)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('31', plain,
% 0.39/0.58      (((k1_tsep_1 @ sk_B @ sk_C @ sk_C)
% 0.39/0.58         = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.39/0.58      inference('clc', [status(thm)], ['29', '30'])).
% 0.39/0.58  thf(t23_tsep_1, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.39/0.58           ( ![C:$i]:
% 0.39/0.58             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.39/0.58               ( ( m1_pre_topc @ B @ C ) <=>
% 0.39/0.58                 ( ( k1_tsep_1 @ A @ B @ C ) =
% 0.39/0.58                   ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) ) ) ) ) ) ))).
% 0.39/0.58  thf('32', plain,
% 0.39/0.58      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.39/0.58         ((v2_struct_0 @ X40)
% 0.39/0.58          | ~ (m1_pre_topc @ X40 @ X41)
% 0.39/0.58          | ((k1_tsep_1 @ X41 @ X40 @ X42)
% 0.39/0.58              != (g1_pre_topc @ (u1_struct_0 @ X42) @ (u1_pre_topc @ X42)))
% 0.39/0.58          | (m1_pre_topc @ X40 @ X42)
% 0.39/0.58          | ~ (m1_pre_topc @ X42 @ X41)
% 0.39/0.58          | (v2_struct_0 @ X42)
% 0.39/0.58          | ~ (l1_pre_topc @ X41)
% 0.39/0.58          | ~ (v2_pre_topc @ X41)
% 0.39/0.58          | (v2_struct_0 @ X41))),
% 0.39/0.58      inference('cnf', [status(esa)], [t23_tsep_1])).
% 0.39/0.58  thf('33', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (((k1_tsep_1 @ X1 @ X0 @ sk_C) != (k1_tsep_1 @ sk_B @ sk_C @ sk_C))
% 0.39/0.58          | (v2_struct_0 @ X1)
% 0.39/0.58          | ~ (v2_pre_topc @ X1)
% 0.39/0.58          | ~ (l1_pre_topc @ X1)
% 0.39/0.58          | (v2_struct_0 @ sk_C)
% 0.39/0.58          | ~ (m1_pre_topc @ sk_C @ X1)
% 0.39/0.58          | (m1_pre_topc @ X0 @ sk_C)
% 0.39/0.58          | ~ (m1_pre_topc @ X0 @ X1)
% 0.39/0.58          | (v2_struct_0 @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['31', '32'])).
% 0.39/0.58  thf('34', plain,
% 0.39/0.58      (((v2_struct_0 @ sk_C)
% 0.39/0.58        | ~ (m1_pre_topc @ sk_C @ sk_B)
% 0.39/0.58        | (m1_pre_topc @ sk_C @ sk_C)
% 0.39/0.58        | ~ (m1_pre_topc @ sk_C @ sk_B)
% 0.39/0.58        | (v2_struct_0 @ sk_C)
% 0.39/0.58        | ~ (l1_pre_topc @ sk_B)
% 0.39/0.58        | ~ (v2_pre_topc @ sk_B)
% 0.39/0.58        | (v2_struct_0 @ sk_B))),
% 0.39/0.58      inference('eq_res', [status(thm)], ['33'])).
% 0.39/0.58  thf('35', plain,
% 0.39/0.58      (((v2_struct_0 @ sk_B)
% 0.39/0.58        | ~ (v2_pre_topc @ sk_B)
% 0.39/0.58        | ~ (l1_pre_topc @ sk_B)
% 0.39/0.58        | (m1_pre_topc @ sk_C @ sk_C)
% 0.39/0.58        | ~ (m1_pre_topc @ sk_C @ sk_B)
% 0.39/0.58        | (v2_struct_0 @ sk_C))),
% 0.39/0.58      inference('simplify', [status(thm)], ['34'])).
% 0.39/0.58  thf('36', plain, ((v2_pre_topc @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('37', plain, ((l1_pre_topc @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('38', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('39', plain,
% 0.39/0.58      (((v2_struct_0 @ sk_B)
% 0.39/0.58        | (m1_pre_topc @ sk_C @ sk_C)
% 0.39/0.58        | (v2_struct_0 @ sk_C))),
% 0.39/0.58      inference('demod', [status(thm)], ['35', '36', '37', '38'])).
% 0.39/0.58  thf('40', plain, (~ (v2_struct_0 @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('41', plain, (((v2_struct_0 @ sk_C) | (m1_pre_topc @ sk_C @ sk_C))),
% 0.39/0.58      inference('clc', [status(thm)], ['39', '40'])).
% 0.39/0.58  thf('42', plain, (~ (v2_struct_0 @ sk_C)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('43', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 0.39/0.58      inference('clc', [status(thm)], ['41', '42'])).
% 0.39/0.58  thf(t11_tmap_1, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( l1_pre_topc @ A ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( m1_pre_topc @ B @ A ) =>
% 0.39/0.58           ( ( v1_pre_topc @
% 0.39/0.58               ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.39/0.58             ( m1_pre_topc @
% 0.39/0.58               ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) ))).
% 0.39/0.58  thf('44', plain,
% 0.39/0.58      (![X33 : $i, X34 : $i]:
% 0.39/0.58         (~ (m1_pre_topc @ X33 @ X34)
% 0.39/0.58          | (m1_pre_topc @ 
% 0.39/0.58             (g1_pre_topc @ (u1_struct_0 @ X33) @ (u1_pre_topc @ X33)) @ X34)
% 0.39/0.58          | ~ (l1_pre_topc @ X34))),
% 0.39/0.58      inference('cnf', [status(esa)], [t11_tmap_1])).
% 0.39/0.58  thf('45', plain,
% 0.39/0.58      ((~ (l1_pre_topc @ sk_C)
% 0.39/0.58        | (m1_pre_topc @ 
% 0.39/0.58           (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ sk_C))),
% 0.39/0.58      inference('sup-', [status(thm)], ['43', '44'])).
% 0.39/0.58  thf('46', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(dt_m1_pre_topc, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( l1_pre_topc @ A ) =>
% 0.39/0.58       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.39/0.58  thf('47', plain,
% 0.39/0.58      (![X19 : $i, X20 : $i]:
% 0.39/0.58         (~ (m1_pre_topc @ X19 @ X20)
% 0.39/0.58          | (l1_pre_topc @ X19)
% 0.39/0.58          | ~ (l1_pre_topc @ X20))),
% 0.39/0.58      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.39/0.58  thf('48', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_C))),
% 0.39/0.58      inference('sup-', [status(thm)], ['46', '47'])).
% 0.39/0.58  thf('49', plain, ((l1_pre_topc @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('50', plain, ((l1_pre_topc @ sk_C)),
% 0.39/0.58      inference('demod', [status(thm)], ['48', '49'])).
% 0.39/0.58  thf('51', plain,
% 0.39/0.58      (((k1_tsep_1 @ sk_B @ sk_C @ sk_C)
% 0.39/0.58         = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.39/0.58      inference('clc', [status(thm)], ['29', '30'])).
% 0.39/0.58  thf('52', plain, ((m1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_C @ sk_C) @ sk_C)),
% 0.39/0.58      inference('demod', [status(thm)], ['45', '50', '51'])).
% 0.39/0.58  thf('53', plain,
% 0.39/0.58      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.39/0.58         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(t12_tmap_1, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( l1_pre_topc @ A ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.39/0.58           ( ![C:$i]:
% 0.39/0.58             ( ( ( v2_pre_topc @ C ) & ( l1_pre_topc @ C ) ) =>
% 0.39/0.58               ( ( ( B ) =
% 0.39/0.58                   ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) =>
% 0.39/0.58                 ( ( m1_pre_topc @ B @ A ) <=> ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.39/0.58  thf('54', plain,
% 0.39/0.58      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.39/0.58         (~ (v2_pre_topc @ X35)
% 0.39/0.58          | ~ (l1_pre_topc @ X35)
% 0.39/0.58          | ((X35) != (g1_pre_topc @ (u1_struct_0 @ X36) @ (u1_pre_topc @ X36)))
% 0.39/0.58          | ~ (m1_pre_topc @ X35 @ X37)
% 0.39/0.58          | (m1_pre_topc @ X36 @ X37)
% 0.39/0.58          | ~ (l1_pre_topc @ X36)
% 0.39/0.58          | ~ (v2_pre_topc @ X36)
% 0.39/0.58          | ~ (l1_pre_topc @ X37))),
% 0.39/0.58      inference('cnf', [status(esa)], [t12_tmap_1])).
% 0.39/0.58  thf('55', plain,
% 0.39/0.58      (![X36 : $i, X37 : $i]:
% 0.39/0.58         (~ (l1_pre_topc @ X37)
% 0.39/0.58          | ~ (v2_pre_topc @ X36)
% 0.39/0.58          | ~ (l1_pre_topc @ X36)
% 0.39/0.58          | (m1_pre_topc @ X36 @ X37)
% 0.39/0.58          | ~ (m1_pre_topc @ 
% 0.39/0.58               (g1_pre_topc @ (u1_struct_0 @ X36) @ (u1_pre_topc @ X36)) @ X37)
% 0.39/0.58          | ~ (l1_pre_topc @ 
% 0.39/0.58               (g1_pre_topc @ (u1_struct_0 @ X36) @ (u1_pre_topc @ X36)))
% 0.39/0.58          | ~ (v2_pre_topc @ 
% 0.39/0.58               (g1_pre_topc @ (u1_struct_0 @ X36) @ (u1_pre_topc @ X36))))),
% 0.39/0.58      inference('simplify', [status(thm)], ['54'])).
% 0.39/0.58  thf('56', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (l1_pre_topc @ 
% 0.39/0.58             (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.39/0.58          | ~ (v2_pre_topc @ 
% 0.39/0.58               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.39/0.58          | ~ (m1_pre_topc @ 
% 0.39/0.58               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ X0)
% 0.39/0.58          | (m1_pre_topc @ sk_B @ X0)
% 0.39/0.58          | ~ (l1_pre_topc @ sk_B)
% 0.39/0.58          | ~ (v2_pre_topc @ sk_B)
% 0.39/0.58          | ~ (l1_pre_topc @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['53', '55'])).
% 0.39/0.58  thf('57', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('58', plain,
% 0.39/0.58      (![X33 : $i, X34 : $i]:
% 0.39/0.58         (~ (m1_pre_topc @ X33 @ X34)
% 0.39/0.58          | (m1_pre_topc @ 
% 0.39/0.58             (g1_pre_topc @ (u1_struct_0 @ X33) @ (u1_pre_topc @ X33)) @ X34)
% 0.39/0.58          | ~ (l1_pre_topc @ X34))),
% 0.39/0.58      inference('cnf', [status(esa)], [t11_tmap_1])).
% 0.39/0.58  thf('59', plain,
% 0.39/0.58      ((~ (l1_pre_topc @ sk_B)
% 0.39/0.58        | (m1_pre_topc @ 
% 0.39/0.58           (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ sk_B))),
% 0.39/0.58      inference('sup-', [status(thm)], ['57', '58'])).
% 0.39/0.58  thf('60', plain, ((l1_pre_topc @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('61', plain,
% 0.39/0.58      ((m1_pre_topc @ 
% 0.39/0.58        (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ sk_B)),
% 0.39/0.58      inference('demod', [status(thm)], ['59', '60'])).
% 0.39/0.58  thf('62', plain,
% 0.39/0.58      (![X19 : $i, X20 : $i]:
% 0.39/0.58         (~ (m1_pre_topc @ X19 @ X20)
% 0.39/0.58          | (l1_pre_topc @ X19)
% 0.39/0.58          | ~ (l1_pre_topc @ X20))),
% 0.39/0.58      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.39/0.58  thf('63', plain,
% 0.39/0.58      ((~ (l1_pre_topc @ sk_B)
% 0.39/0.58        | (l1_pre_topc @ 
% 0.39/0.58           (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['61', '62'])).
% 0.39/0.58  thf('64', plain, ((l1_pre_topc @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('65', plain,
% 0.39/0.58      ((l1_pre_topc @ 
% 0.39/0.58        (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.39/0.58      inference('demod', [status(thm)], ['63', '64'])).
% 0.39/0.58  thf('66', plain,
% 0.39/0.58      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.39/0.58         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('67', plain,
% 0.39/0.58      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.39/0.58         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(fc6_pre_topc, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.58       ( ( v1_pre_topc @
% 0.39/0.58           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.39/0.58         ( v2_pre_topc @
% 0.39/0.58           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.39/0.58  thf('68', plain,
% 0.39/0.58      (![X22 : $i]:
% 0.39/0.58         ((v2_pre_topc @ 
% 0.39/0.58           (g1_pre_topc @ (u1_struct_0 @ X22) @ (u1_pre_topc @ X22)))
% 0.39/0.58          | ~ (l1_pre_topc @ X22)
% 0.39/0.58          | ~ (v2_pre_topc @ X22))),
% 0.39/0.58      inference('cnf', [status(esa)], [fc6_pre_topc])).
% 0.39/0.58  thf('69', plain,
% 0.39/0.58      (((v2_pre_topc @ 
% 0.39/0.58         (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.39/0.58        | ~ (v2_pre_topc @ sk_B)
% 0.39/0.58        | ~ (l1_pre_topc @ sk_B))),
% 0.39/0.58      inference('sup+', [status(thm)], ['67', '68'])).
% 0.39/0.58  thf('70', plain, ((v2_pre_topc @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('71', plain, ((l1_pre_topc @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('72', plain,
% 0.39/0.58      ((v2_pre_topc @ 
% 0.39/0.58        (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.39/0.58      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.39/0.58  thf('73', plain,
% 0.39/0.58      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.39/0.58         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('74', plain, ((l1_pre_topc @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('75', plain, ((v2_pre_topc @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('76', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (~ (m1_pre_topc @ 
% 0.39/0.59             (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ X0)
% 0.39/0.59          | (m1_pre_topc @ sk_B @ X0)
% 0.39/0.59          | ~ (l1_pre_topc @ X0))),
% 0.39/0.59      inference('demod', [status(thm)],
% 0.39/0.59                ['56', '65', '66', '72', '73', '74', '75'])).
% 0.39/0.59  thf('77', plain,
% 0.39/0.59      ((m1_pre_topc @ 
% 0.39/0.59        (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ sk_B)),
% 0.39/0.59      inference('demod', [status(thm)], ['59', '60'])).
% 0.39/0.59  thf('78', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (~ (m1_pre_topc @ 
% 0.39/0.59             (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ X0)
% 0.39/0.59          | (m1_pre_topc @ sk_B @ X0)
% 0.39/0.59          | ~ (l1_pre_topc @ X0))),
% 0.39/0.59      inference('demod', [status(thm)],
% 0.39/0.59                ['56', '65', '66', '72', '73', '74', '75'])).
% 0.39/0.59  thf('79', plain, ((~ (l1_pre_topc @ sk_B) | (m1_pre_topc @ sk_B @ sk_B))),
% 0.39/0.59      inference('sup-', [status(thm)], ['77', '78'])).
% 0.39/0.59  thf('80', plain, ((l1_pre_topc @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('81', plain, ((m1_pre_topc @ sk_B @ sk_B)),
% 0.39/0.59      inference('demod', [status(thm)], ['79', '80'])).
% 0.39/0.59  thf('82', plain,
% 0.39/0.59      (![X43 : $i, X44 : $i]:
% 0.39/0.59         ((v2_struct_0 @ X43)
% 0.39/0.59          | ~ (m1_pre_topc @ X43 @ X44)
% 0.39/0.59          | ((k1_tsep_1 @ X44 @ X43 @ X43)
% 0.39/0.59              = (g1_pre_topc @ (u1_struct_0 @ X43) @ (u1_pre_topc @ X43)))
% 0.39/0.59          | ~ (l1_pre_topc @ X44)
% 0.39/0.59          | ~ (v2_pre_topc @ X44)
% 0.39/0.59          | (v2_struct_0 @ X44))),
% 0.39/0.59      inference('cnf', [status(esa)], [t25_tmap_1])).
% 0.39/0.59  thf('83', plain,
% 0.39/0.59      (((v2_struct_0 @ sk_B)
% 0.39/0.59        | ~ (v2_pre_topc @ sk_B)
% 0.39/0.59        | ~ (l1_pre_topc @ sk_B)
% 0.39/0.59        | ((k1_tsep_1 @ sk_B @ sk_B @ sk_B)
% 0.39/0.59            = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.39/0.59        | (v2_struct_0 @ sk_B))),
% 0.39/0.59      inference('sup-', [status(thm)], ['81', '82'])).
% 0.39/0.59  thf('84', plain, ((v2_pre_topc @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('85', plain, ((l1_pre_topc @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('86', plain,
% 0.39/0.59      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.39/0.59         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('87', plain,
% 0.39/0.59      (((v2_struct_0 @ sk_B)
% 0.39/0.59        | ((k1_tsep_1 @ sk_B @ sk_B @ sk_B)
% 0.39/0.59            = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.39/0.59        | (v2_struct_0 @ sk_B))),
% 0.39/0.59      inference('demod', [status(thm)], ['83', '84', '85', '86'])).
% 0.39/0.59  thf('88', plain,
% 0.39/0.59      ((((k1_tsep_1 @ sk_B @ sk_B @ sk_B)
% 0.39/0.59          = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.39/0.59        | (v2_struct_0 @ sk_B))),
% 0.39/0.59      inference('simplify', [status(thm)], ['87'])).
% 0.39/0.59  thf('89', plain, (~ (v2_struct_0 @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('90', plain,
% 0.39/0.59      (((k1_tsep_1 @ sk_B @ sk_B @ sk_B)
% 0.39/0.59         = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.39/0.59      inference('clc', [status(thm)], ['88', '89'])).
% 0.39/0.59  thf('91', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (~ (m1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_B @ sk_B) @ X0)
% 0.39/0.59          | (m1_pre_topc @ sk_B @ X0)
% 0.39/0.59          | ~ (l1_pre_topc @ X0))),
% 0.39/0.59      inference('demod', [status(thm)], ['76', '90'])).
% 0.39/0.59  thf('92', plain,
% 0.39/0.59      (((k1_tsep_1 @ sk_B @ sk_C @ sk_C)
% 0.39/0.59         = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.39/0.59      inference('clc', [status(thm)], ['29', '30'])).
% 0.39/0.59  thf('93', plain,
% 0.39/0.59      (((k1_tsep_1 @ sk_B @ sk_B @ sk_B)
% 0.39/0.59         = (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.39/0.59      inference('clc', [status(thm)], ['88', '89'])).
% 0.39/0.59  thf('94', plain,
% 0.39/0.59      (((k1_tsep_1 @ sk_B @ sk_B @ sk_B) = (k1_tsep_1 @ sk_B @ sk_C @ sk_C))),
% 0.39/0.59      inference('sup+', [status(thm)], ['92', '93'])).
% 0.39/0.59  thf('95', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (~ (m1_pre_topc @ (k1_tsep_1 @ sk_B @ sk_C @ sk_C) @ X0)
% 0.39/0.59          | (m1_pre_topc @ sk_B @ X0)
% 0.39/0.59          | ~ (l1_pre_topc @ X0))),
% 0.39/0.59      inference('demod', [status(thm)], ['91', '94'])).
% 0.39/0.59  thf('96', plain, ((~ (l1_pre_topc @ sk_C) | (m1_pre_topc @ sk_B @ sk_C))),
% 0.39/0.59      inference('sup-', [status(thm)], ['52', '95'])).
% 0.39/0.59  thf('97', plain, ((l1_pre_topc @ sk_C)),
% 0.39/0.59      inference('demod', [status(thm)], ['48', '49'])).
% 0.39/0.59  thf('98', plain, ((m1_pre_topc @ sk_B @ sk_C)),
% 0.39/0.59      inference('demod', [status(thm)], ['96', '97'])).
% 0.39/0.59  thf('99', plain,
% 0.39/0.59      (![X38 : $i, X39 : $i]:
% 0.39/0.59         (~ (m1_pre_topc @ X38 @ X39)
% 0.39/0.59          | (m1_subset_1 @ (u1_struct_0 @ X38) @ 
% 0.39/0.59             (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 0.39/0.59          | ~ (l1_pre_topc @ X39))),
% 0.39/0.59      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.39/0.59  thf('100', plain,
% 0.39/0.59      ((~ (l1_pre_topc @ sk_C)
% 0.39/0.59        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.59           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['98', '99'])).
% 0.39/0.59  thf('101', plain, ((l1_pre_topc @ sk_C)),
% 0.39/0.59      inference('demod', [status(thm)], ['48', '49'])).
% 0.39/0.59  thf('102', plain,
% 0.39/0.59      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.39/0.59      inference('demod', [status(thm)], ['100', '101'])).
% 0.39/0.59  thf('103', plain,
% 0.39/0.59      (![X3 : $i, X4 : $i]:
% 0.39/0.59         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.39/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.59  thf('104', plain,
% 0.39/0.59      ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))),
% 0.39/0.59      inference('sup-', [status(thm)], ['102', '103'])).
% 0.39/0.59  thf('105', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.39/0.59      inference('demod', [status(thm)], ['21', '104'])).
% 0.39/0.59  thf('106', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.39/0.59      inference('demod', [status(thm)], ['21', '104'])).
% 0.39/0.59  thf('107', plain,
% 0.39/0.59      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.59        | (r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.59           (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.39/0.59      inference('demod', [status(thm)], ['12', '105', '106'])).
% 0.39/0.59  thf('108', plain,
% 0.39/0.59      (~ (r1_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.59          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.39/0.59          (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('109', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('110', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_D @ 
% 0.39/0.59        (k1_zfmisc_1 @ 
% 0.39/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(d4_tmap_1, axiom,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.59       ( ![B:$i]:
% 0.39/0.59         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.39/0.59             ( l1_pre_topc @ B ) ) =>
% 0.39/0.59           ( ![C:$i]:
% 0.39/0.59             ( ( ( v1_funct_1 @ C ) & 
% 0.39/0.59                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.39/0.59                 ( m1_subset_1 @
% 0.39/0.59                   C @ 
% 0.39/0.59                   ( k1_zfmisc_1 @
% 0.39/0.59                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.39/0.59               ( ![D:$i]:
% 0.39/0.59                 ( ( m1_pre_topc @ D @ A ) =>
% 0.39/0.59                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.39/0.59                     ( k2_partfun1 @
% 0.39/0.59                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.39/0.59                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.59  thf('111', plain,
% 0.39/0.59      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.39/0.59         ((v2_struct_0 @ X29)
% 0.39/0.59          | ~ (v2_pre_topc @ X29)
% 0.39/0.59          | ~ (l1_pre_topc @ X29)
% 0.39/0.59          | ~ (m1_pre_topc @ X30 @ X31)
% 0.39/0.59          | ((k2_tmap_1 @ X31 @ X29 @ X32 @ X30)
% 0.39/0.59              = (k2_partfun1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X29) @ 
% 0.39/0.59                 X32 @ (u1_struct_0 @ X30)))
% 0.39/0.59          | ~ (m1_subset_1 @ X32 @ 
% 0.39/0.59               (k1_zfmisc_1 @ 
% 0.39/0.59                (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X29))))
% 0.39/0.59          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X29))
% 0.39/0.59          | ~ (v1_funct_1 @ X32)
% 0.39/0.59          | ~ (l1_pre_topc @ X31)
% 0.39/0.59          | ~ (v2_pre_topc @ X31)
% 0.39/0.59          | (v2_struct_0 @ X31))),
% 0.39/0.59      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.39/0.59  thf('112', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((v2_struct_0 @ sk_B)
% 0.39/0.59          | ~ (v2_pre_topc @ sk_B)
% 0.39/0.59          | ~ (l1_pre_topc @ sk_B)
% 0.39/0.59          | ~ (v1_funct_1 @ sk_D)
% 0.39/0.59          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.39/0.59          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.39/0.59              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.59                 sk_D @ (u1_struct_0 @ X0)))
% 0.39/0.59          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.39/0.59          | ~ (l1_pre_topc @ sk_A)
% 0.39/0.59          | ~ (v2_pre_topc @ sk_A)
% 0.39/0.59          | (v2_struct_0 @ sk_A))),
% 0.39/0.59      inference('sup-', [status(thm)], ['110', '111'])).
% 0.39/0.59  thf('113', plain, ((v2_pre_topc @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('114', plain, ((l1_pre_topc @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('115', plain, ((v1_funct_1 @ sk_D)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('116', plain,
% 0.39/0.59      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('117', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_D @ 
% 0.39/0.59        (k1_zfmisc_1 @ 
% 0.39/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(redefinition_k2_partfun1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.59     ( ( ( v1_funct_1 @ C ) & 
% 0.39/0.59         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.59       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.39/0.59  thf('118', plain,
% 0.39/0.59      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.39/0.59         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.39/0.59          | ~ (v1_funct_1 @ X14)
% 0.39/0.59          | ((k2_partfun1 @ X15 @ X16 @ X14 @ X17) = (k7_relat_1 @ X14 @ X17)))),
% 0.39/0.59      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.39/0.59  thf('119', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (((k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.39/0.59            X0) = (k7_relat_1 @ sk_D @ X0))
% 0.39/0.59          | ~ (v1_funct_1 @ sk_D))),
% 0.39/0.59      inference('sup-', [status(thm)], ['117', '118'])).
% 0.39/0.59  thf('120', plain, ((v1_funct_1 @ sk_D)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('121', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.39/0.59           X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.39/0.59      inference('demod', [status(thm)], ['119', '120'])).
% 0.39/0.59  thf('122', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('123', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('124', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((v2_struct_0 @ sk_B)
% 0.39/0.59          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.39/0.59              = (k7_relat_1 @ sk_D @ (u1_struct_0 @ X0)))
% 0.39/0.59          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.39/0.59          | (v2_struct_0 @ sk_A))),
% 0.39/0.59      inference('demod', [status(thm)],
% 0.39/0.59                ['112', '113', '114', '115', '116', '121', '122', '123'])).
% 0.39/0.59  thf('125', plain,
% 0.39/0.59      (((v2_struct_0 @ sk_A)
% 0.39/0.59        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.39/0.59            = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))
% 0.39/0.59        | (v2_struct_0 @ sk_B))),
% 0.39/0.59      inference('sup-', [status(thm)], ['109', '124'])).
% 0.39/0.59  thf('126', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('127', plain,
% 0.39/0.59      (((v2_struct_0 @ sk_B)
% 0.39/0.59        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.39/0.59            = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C))))),
% 0.39/0.59      inference('clc', [status(thm)], ['125', '126'])).
% 0.39/0.59  thf('128', plain, (~ (v2_struct_0 @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('129', plain,
% 0.39/0.59      (((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.39/0.59         = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.39/0.59      inference('clc', [status(thm)], ['127', '128'])).
% 0.39/0.59  thf('130', plain,
% 0.39/0.59      (~ (r1_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.59          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.39/0.59          (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.39/0.59      inference('demod', [status(thm)], ['108', '129'])).
% 0.39/0.59  thf('131', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.39/0.59      inference('demod', [status(thm)], ['21', '104'])).
% 0.39/0.59  thf('132', plain,
% 0.39/0.59      (~ (r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.59          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.39/0.59          (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.39/0.59      inference('demod', [status(thm)], ['130', '131'])).
% 0.39/0.59  thf('133', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_D @ 
% 0.39/0.59        (k1_zfmisc_1 @ 
% 0.39/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(cc2_relset_1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.59       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.39/0.59  thf('134', plain,
% 0.39/0.59      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.39/0.59         ((v4_relat_1 @ X11 @ X12)
% 0.39/0.59          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.39/0.59      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.39/0.59  thf('135', plain, ((v4_relat_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.39/0.59      inference('sup-', [status(thm)], ['133', '134'])).
% 0.39/0.59  thf(t209_relat_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.39/0.59       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.39/0.59  thf('136', plain,
% 0.39/0.59      (![X6 : $i, X7 : $i]:
% 0.39/0.59         (((X6) = (k7_relat_1 @ X6 @ X7))
% 0.39/0.59          | ~ (v4_relat_1 @ X6 @ X7)
% 0.39/0.59          | ~ (v1_relat_1 @ X6))),
% 0.39/0.59      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.39/0.59  thf('137', plain,
% 0.39/0.59      ((~ (v1_relat_1 @ sk_D)
% 0.39/0.59        | ((sk_D) = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_B))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['135', '136'])).
% 0.39/0.59  thf('138', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_D @ 
% 0.39/0.59        (k1_zfmisc_1 @ 
% 0.39/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(cc1_relset_1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.59       ( v1_relat_1 @ C ) ))).
% 0.39/0.59  thf('139', plain,
% 0.39/0.59      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.39/0.59         ((v1_relat_1 @ X8)
% 0.39/0.59          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.39/0.59      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.39/0.59  thf('140', plain, ((v1_relat_1 @ sk_D)),
% 0.39/0.59      inference('sup-', [status(thm)], ['138', '139'])).
% 0.39/0.59  thf('141', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_B)))),
% 0.39/0.59      inference('demod', [status(thm)], ['137', '140'])).
% 0.39/0.59  thf('142', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.39/0.59      inference('demod', [status(thm)], ['21', '104'])).
% 0.39/0.59  thf('143', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.39/0.59      inference('demod', [status(thm)], ['141', '142'])).
% 0.39/0.59  thf('144', plain,
% 0.39/0.59      (~ (r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.59          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)),
% 0.39/0.59      inference('demod', [status(thm)], ['132', '143'])).
% 0.39/0.59  thf('145', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.39/0.59      inference('clc', [status(thm)], ['107', '144'])).
% 0.39/0.59  thf(fc2_struct_0, axiom,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.39/0.59       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.39/0.59  thf('146', plain,
% 0.39/0.59      (![X21 : $i]:
% 0.39/0.59         (~ (v1_xboole_0 @ (u1_struct_0 @ X21))
% 0.39/0.59          | ~ (l1_struct_0 @ X21)
% 0.39/0.59          | (v2_struct_0 @ X21))),
% 0.39/0.59      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.39/0.59  thf('147', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.39/0.59      inference('sup-', [status(thm)], ['145', '146'])).
% 0.39/0.59  thf('148', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(dt_l1_pre_topc, axiom,
% 0.39/0.59    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.39/0.59  thf('149', plain,
% 0.39/0.59      (![X18 : $i]: ((l1_struct_0 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.39/0.59      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.39/0.59  thf('150', plain, ((l1_struct_0 @ sk_A)),
% 0.39/0.59      inference('sup-', [status(thm)], ['148', '149'])).
% 0.39/0.59  thf('151', plain, ((v2_struct_0 @ sk_A)),
% 0.39/0.59      inference('demod', [status(thm)], ['147', '150'])).
% 0.39/0.59  thf('152', plain, ($false), inference('demod', [status(thm)], ['0', '151'])).
% 0.39/0.59  
% 0.39/0.59  % SZS output end Refutation
% 0.39/0.59  
% 0.42/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
