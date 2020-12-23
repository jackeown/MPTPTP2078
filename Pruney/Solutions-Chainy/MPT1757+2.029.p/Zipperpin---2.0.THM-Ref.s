%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xBJCz1qtfr

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:58 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 256 expanded)
%              Number of leaves         :   35 (  87 expanded)
%              Depth                    :   19
%              Number of atoms          : 1744 (7861 expanded)
%              Number of equality atoms :   11 ( 111 expanded)
%              Maximal formula depth    :   29 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(t67_tmap_1,conjecture,(
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
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( v1_tsep_1 @ D @ B )
                    & ( m1_pre_topc @ D @ B ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                         => ( ( E = F )
                           => ( ( r1_tmap_1 @ B @ A @ C @ E )
                            <=> ( r1_tmap_1 @ D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) )).

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
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
               => ! [D: $i] :
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( v1_tsep_1 @ D @ B )
                      & ( m1_pre_topc @ D @ B ) )
                   => ! [E: $i] :
                        ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                           => ( ( E = F )
                             => ( ( r1_tmap_1 @ B @ A @ C @ E )
                              <=> ( r1_tmap_1 @ D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t67_tmap_1])).

thf('0',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    sk_E = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('6',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
    | ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('7',plain,(
    ! [X17: $i] :
      ( ( m1_pre_topc @ X17 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('8',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('15',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F )
    | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,(
    sk_E = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_E )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t66_tmap_1,axiom,(
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
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ B ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) )
                         => ! [G: $i] :
                              ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                             => ( ( ( v3_pre_topc @ E @ B )
                                  & ( r2_hidden @ F @ E )
                                  & ( r1_tarski @ E @ ( u1_struct_0 @ D ) )
                                  & ( F = G ) )
                               => ( ( r1_tmap_1 @ B @ A @ C @ F )
                                <=> ( r1_tmap_1 @ D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) )).

thf('23',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ( v2_struct_0 @ X25 )
      | ~ ( m1_pre_topc @ X25 @ X24 )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X24 ) )
      | ~ ( v3_pre_topc @ X27 @ X24 )
      | ~ ( r2_hidden @ X26 @ X27 )
      | ~ ( r1_tarski @ X27 @ ( u1_struct_0 @ X25 ) )
      | ( X26 != X28 )
      | ~ ( r1_tmap_1 @ X25 @ X29 @ ( k2_tmap_1 @ X24 @ X29 @ X30 @ X25 ) @ X28 )
      | ( r1_tmap_1 @ X24 @ X29 @ X30 @ X26 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X25 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X29 ) ) ) )
      | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X29 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t66_tmap_1])).

thf('24',plain,(
    ! [X24: $i,X25: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( v2_struct_0 @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X29 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X29 ) ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X25 ) )
      | ( r1_tmap_1 @ X24 @ X29 @ X30 @ X28 )
      | ~ ( r1_tmap_1 @ X25 @ X29 @ ( k2_tmap_1 @ X24 @ X29 @ X30 @ X25 ) @ X28 )
      | ~ ( r1_tarski @ X27 @ ( u1_struct_0 @ X25 ) )
      | ~ ( r2_hidden @ X28 @ X27 )
      | ~ ( v3_pre_topc @ X27 @ X24 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X24 ) )
      | ~ ( m1_pre_topc @ X25 @ X24 )
      | ( v2_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v3_pre_topc @ X2 @ sk_B )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v3_pre_topc @ X2 @ sk_B )
      | ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r1_tarski @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26','27','28','29','30','31'])).

thf('33',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D ) )
        | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
        | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_D ) )
        | ~ ( r2_hidden @ sk_E @ X0 )
        | ~ ( v3_pre_topc @ X0 @ sk_B )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
        | ~ ( m1_pre_topc @ sk_D @ sk_B )
        | ( v2_struct_0 @ sk_D )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F ) ),
    inference('sup-',[status(thm)],['21','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('35',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
        | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
        | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_D ) )
        | ~ ( r2_hidden @ sk_E @ X0 )
        | ~ ( v3_pre_topc @ X0 @ sk_B )
        | ( v2_struct_0 @ sk_D )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F ) ),
    inference(demod,[status(thm)],['33','34','35','36'])).

thf('38',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_B )
      | ~ ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D ) )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_D ) )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F ) ),
    inference('sup-',[status(thm)],['17','37'])).

thf('39',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t16_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( u1_struct_0 @ B ) )
               => ( ( ( v1_tsep_1 @ B @ A )
                    & ( m1_pre_topc @ B @ A ) )
                <=> ( v3_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('40',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( X14
       != ( u1_struct_0 @ X12 ) )
      | ~ ( v1_tsep_1 @ X12 @ X13 )
      | ~ ( m1_pre_topc @ X12 @ X13 )
      | ( v3_pre_topc @ X14 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t16_tsep_1])).

thf('41',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X12 ) @ X13 )
      | ~ ( v1_tsep_1 @ X12 @ X13 )
      | ~ ( m1_pre_topc @ X12 @ X13 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ~ ( m1_pre_topc @ sk_D @ sk_B )
    | ~ ( v1_tsep_1 @ sk_D @ sk_B )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_tsep_1 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v3_pre_topc @ ( u1_struct_0 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['42','43','44','45','46'])).

thf('48',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D ) )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_D ) )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F ) ),
    inference(demod,[status(thm)],['38','47'])).

thf('49',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
      | ~ ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F ) ),
    inference('sup-',[status(thm)],['12','48'])).

thf('50',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('51',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( l1_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('52',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
      | ~ ( r2_hidden @ sk_E @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F ) ),
    inference(demod,[status(thm)],['49','54'])).

thf('56',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F ) ),
    inference('sup-',[status(thm)],['6','55'])).

thf('57',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
   <= ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(split,[status(esa)],['0'])).

thf('58',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_D ) ) )
   <= ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
      & ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('59',plain,(
    ! [X8: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('60',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
      & ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['52','53'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('62',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('63',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
      & ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F ) ) ),
    inference(demod,[status(thm)],['60','63'])).

thf('65',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
      & ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
      & ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
      & ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
    | ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F ) ),
    inference(split,[status(esa)],['18'])).

thf('73',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('74',plain,
    ( ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(split,[status(esa)],['18'])).

thf('75',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t64_tmap_1,axiom,(
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
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ B ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                         => ( ( ( E = F )
                              & ( r1_tmap_1 @ B @ A @ C @ E ) )
                           => ( r1_tmap_1 @ D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) )).

thf('76',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_pre_topc @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ( r1_tmap_1 @ X19 @ X21 @ ( k2_tmap_1 @ X18 @ X21 @ X22 @ X19 ) @ X20 )
      | ( X23 != X20 )
      | ~ ( r1_tmap_1 @ X18 @ X21 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( v1_funct_2 @ X22 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t64_tmap_1])).

thf('77',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_2 @ X22 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X18 ) )
      | ~ ( r1_tmap_1 @ X18 @ X21 @ X22 @ X20 )
      | ( r1_tmap_1 @ X19 @ X21 @ ( k2_tmap_1 @ X18 @ X21 @ X22 @ X19 ) @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ~ ( m1_pre_topc @ X19 @ X18 )
      | ( v2_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','77'])).

thf('79',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['78','79','80','81','82','83','84'])).

thf('86',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ sk_E )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference('sup-',[status(thm)],['74','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0 ) @ sk_E )
        | ~ ( m1_subset_1 @ sk_E @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_B )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_B )
      | ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference('sup-',[status(thm)],['73','88'])).

thf('90',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_E )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F ) ),
    inference(split,[status(esa)],['0'])).

thf('93',plain,(
    sk_E = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_E )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['91','94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F )
      & ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E ) ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ~ ( r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E )
    | ( r1_tmap_1 @ sk_D @ sk_A @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D ) @ sk_F ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','71','72','101'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xBJCz1qtfr
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:28:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 76 iterations in 0.036s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.50  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.22/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.22/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.50  thf(sk_F_type, type, sk_F: $i).
% 0.22/0.50  thf(sk_E_type, type, sk_E: $i).
% 0.22/0.50  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.22/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.50  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.50  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.22/0.50  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.50  thf(t67_tmap_1, conjecture,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.50             ( l1_pre_topc @ B ) ) =>
% 0.22/0.50           ( ![C:$i]:
% 0.22/0.50             ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.50                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.22/0.50                 ( m1_subset_1 @
% 0.22/0.50                   C @ 
% 0.22/0.50                   ( k1_zfmisc_1 @
% 0.22/0.50                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.22/0.50               ( ![D:$i]:
% 0.22/0.50                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ B ) & 
% 0.22/0.50                     ( m1_pre_topc @ D @ B ) ) =>
% 0.22/0.50                   ( ![E:$i]:
% 0.22/0.50                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.22/0.50                       ( ![F:$i]:
% 0.22/0.50                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.22/0.50                           ( ( ( E ) = ( F ) ) =>
% 0.22/0.50                             ( ( r1_tmap_1 @ B @ A @ C @ E ) <=>
% 0.22/0.50                               ( r1_tmap_1 @
% 0.22/0.50                                 D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i]:
% 0.22/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.50            ( l1_pre_topc @ A ) ) =>
% 0.22/0.50          ( ![B:$i]:
% 0.22/0.50            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.50                ( l1_pre_topc @ B ) ) =>
% 0.22/0.50              ( ![C:$i]:
% 0.22/0.50                ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.50                    ( v1_funct_2 @
% 0.22/0.50                      C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.22/0.50                    ( m1_subset_1 @
% 0.22/0.50                      C @ 
% 0.22/0.50                      ( k1_zfmisc_1 @
% 0.22/0.50                        ( k2_zfmisc_1 @
% 0.22/0.50                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.22/0.50                  ( ![D:$i]:
% 0.22/0.50                    ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ B ) & 
% 0.22/0.50                        ( m1_pre_topc @ D @ B ) ) =>
% 0.22/0.50                      ( ![E:$i]:
% 0.22/0.50                        ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.22/0.50                          ( ![F:$i]:
% 0.22/0.50                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.22/0.50                              ( ( ( E ) = ( F ) ) =>
% 0.22/0.50                                ( ( r1_tmap_1 @ B @ A @ C @ E ) <=>
% 0.22/0.50                                  ( r1_tmap_1 @
% 0.22/0.50                                    D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t67_tmap_1])).
% 0.22/0.50  thf('0', plain,
% 0.22/0.50      ((~ (r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.22/0.50           sk_F)
% 0.22/0.50        | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)) | 
% 0.22/0.50       ~
% 0.22/0.50       ((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.22/0.50         sk_F))),
% 0.22/0.50      inference('split', [status(esa)], ['0'])).
% 0.22/0.50  thf('2', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('3', plain, (((sk_E) = (sk_F))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('4', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D))),
% 0.22/0.50      inference('demod', [status(thm)], ['2', '3'])).
% 0.22/0.50  thf(t2_subset, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ A @ B ) =>
% 0.22/0.50       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.22/0.50  thf('5', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((r2_hidden @ X0 @ X1)
% 0.22/0.50          | (v1_xboole_0 @ X1)
% 0.22/0.50          | ~ (m1_subset_1 @ X0 @ X1))),
% 0.22/0.50      inference('cnf', [status(esa)], [t2_subset])).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.22/0.50        | (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.50  thf(t2_tsep_1, axiom,
% 0.22/0.50    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.22/0.50  thf('7', plain,
% 0.22/0.50      (![X17 : $i]: ((m1_pre_topc @ X17 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.22/0.50      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.22/0.50  thf(t1_tsep_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( l1_pre_topc @ A ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.50           ( m1_subset_1 @
% 0.22/0.50             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (![X15 : $i, X16 : $i]:
% 0.22/0.50         (~ (m1_pre_topc @ X15 @ X16)
% 0.22/0.50          | (m1_subset_1 @ (u1_struct_0 @ X15) @ 
% 0.22/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.22/0.50          | ~ (l1_pre_topc @ X16))),
% 0.22/0.50      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (l1_pre_topc @ X0)
% 0.22/0.50          | ~ (l1_pre_topc @ X0)
% 0.22/0.50          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.22/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.50  thf('10', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.22/0.50           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.22/0.50          | ~ (l1_pre_topc @ X0))),
% 0.22/0.50      inference('simplify', [status(thm)], ['9'])).
% 0.22/0.50  thf(t3_subset, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      (![X2 : $i, X3 : $i]:
% 0.22/0.50         ((r1_tarski @ X2 @ X3) | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (l1_pre_topc @ X0)
% 0.22/0.50          | (r1_tarski @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.50  thf('13', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('14', plain,
% 0.22/0.50      (![X15 : $i, X16 : $i]:
% 0.22/0.50         (~ (m1_pre_topc @ X15 @ X16)
% 0.22/0.50          | (m1_subset_1 @ (u1_struct_0 @ X15) @ 
% 0.22/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.22/0.50          | ~ (l1_pre_topc @ X16))),
% 0.22/0.50      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.22/0.50  thf('15', plain,
% 0.22/0.50      ((~ (l1_pre_topc @ sk_B)
% 0.22/0.50        | (m1_subset_1 @ (u1_struct_0 @ sk_D) @ 
% 0.22/0.50           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.50  thf('16', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('17', plain,
% 0.22/0.50      ((m1_subset_1 @ (u1_struct_0 @ sk_D) @ 
% 0.22/0.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.50      inference('demod', [status(thm)], ['15', '16'])).
% 0.22/0.50  thf('18', plain,
% 0.22/0.50      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.22/0.50         sk_F)
% 0.22/0.50        | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('19', plain,
% 0.22/0.50      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.22/0.50         sk_F))
% 0.22/0.50         <= (((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.22/0.50               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_F)))),
% 0.22/0.50      inference('split', [status(esa)], ['18'])).
% 0.22/0.50  thf('20', plain, (((sk_E) = (sk_F))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('21', plain,
% 0.22/0.50      (((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.22/0.50         sk_E))
% 0.22/0.50         <= (((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.22/0.50               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_F)))),
% 0.22/0.50      inference('demod', [status(thm)], ['19', '20'])).
% 0.22/0.50  thf('22', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_C @ 
% 0.22/0.50        (k1_zfmisc_1 @ 
% 0.22/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(t66_tmap_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.50             ( l1_pre_topc @ B ) ) =>
% 0.22/0.50           ( ![C:$i]:
% 0.22/0.50             ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.50                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.22/0.50                 ( m1_subset_1 @
% 0.22/0.50                   C @ 
% 0.22/0.50                   ( k1_zfmisc_1 @
% 0.22/0.50                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.22/0.50               ( ![D:$i]:
% 0.22/0.50                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.22/0.50                   ( ![E:$i]:
% 0.22/0.50                     ( ( m1_subset_1 @
% 0.22/0.50                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.22/0.50                       ( ![F:$i]:
% 0.22/0.50                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.22/0.50                           ( ![G:$i]:
% 0.22/0.50                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 0.22/0.50                               ( ( ( v3_pre_topc @ E @ B ) & 
% 0.22/0.50                                   ( r2_hidden @ F @ E ) & 
% 0.22/0.50                                   ( r1_tarski @ E @ ( u1_struct_0 @ D ) ) & 
% 0.22/0.50                                   ( ( F ) = ( G ) ) ) =>
% 0.22/0.50                                 ( ( r1_tmap_1 @ B @ A @ C @ F ) <=>
% 0.22/0.50                                   ( r1_tmap_1 @
% 0.22/0.50                                     D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.50  thf('23', plain,
% 0.22/0.50      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.22/0.50         ((v2_struct_0 @ X24)
% 0.22/0.50          | ~ (v2_pre_topc @ X24)
% 0.22/0.50          | ~ (l1_pre_topc @ X24)
% 0.22/0.50          | (v2_struct_0 @ X25)
% 0.22/0.50          | ~ (m1_pre_topc @ X25 @ X24)
% 0.22/0.50          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X24))
% 0.22/0.50          | ~ (v3_pre_topc @ X27 @ X24)
% 0.22/0.50          | ~ (r2_hidden @ X26 @ X27)
% 0.22/0.50          | ~ (r1_tarski @ X27 @ (u1_struct_0 @ X25))
% 0.22/0.50          | ((X26) != (X28))
% 0.22/0.50          | ~ (r1_tmap_1 @ X25 @ X29 @ (k2_tmap_1 @ X24 @ X29 @ X30 @ X25) @ 
% 0.22/0.50               X28)
% 0.22/0.50          | (r1_tmap_1 @ X24 @ X29 @ X30 @ X26)
% 0.22/0.50          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X25))
% 0.22/0.50          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.22/0.50          | ~ (m1_subset_1 @ X30 @ 
% 0.22/0.50               (k1_zfmisc_1 @ 
% 0.22/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X29))))
% 0.22/0.50          | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X29))
% 0.22/0.50          | ~ (v1_funct_1 @ X30)
% 0.22/0.50          | ~ (l1_pre_topc @ X29)
% 0.22/0.50          | ~ (v2_pre_topc @ X29)
% 0.22/0.50          | (v2_struct_0 @ X29))),
% 0.22/0.50      inference('cnf', [status(esa)], [t66_tmap_1])).
% 0.22/0.50  thf('24', plain,
% 0.22/0.50      (![X24 : $i, X25 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.22/0.50         ((v2_struct_0 @ X29)
% 0.22/0.50          | ~ (v2_pre_topc @ X29)
% 0.22/0.50          | ~ (l1_pre_topc @ X29)
% 0.22/0.50          | ~ (v1_funct_1 @ X30)
% 0.22/0.50          | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X29))
% 0.22/0.50          | ~ (m1_subset_1 @ X30 @ 
% 0.22/0.50               (k1_zfmisc_1 @ 
% 0.22/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X29))))
% 0.22/0.50          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.22/0.50          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X25))
% 0.22/0.50          | (r1_tmap_1 @ X24 @ X29 @ X30 @ X28)
% 0.22/0.50          | ~ (r1_tmap_1 @ X25 @ X29 @ (k2_tmap_1 @ X24 @ X29 @ X30 @ X25) @ 
% 0.22/0.50               X28)
% 0.22/0.50          | ~ (r1_tarski @ X27 @ (u1_struct_0 @ X25))
% 0.22/0.50          | ~ (r2_hidden @ X28 @ X27)
% 0.22/0.50          | ~ (v3_pre_topc @ X27 @ X24)
% 0.22/0.50          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X24))
% 0.22/0.50          | ~ (m1_pre_topc @ X25 @ X24)
% 0.22/0.50          | (v2_struct_0 @ X25)
% 0.22/0.50          | ~ (l1_pre_topc @ X24)
% 0.22/0.50          | ~ (v2_pre_topc @ X24)
% 0.22/0.50          | (v2_struct_0 @ X24))),
% 0.22/0.50      inference('simplify', [status(thm)], ['23'])).
% 0.22/0.50  thf('25', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.50         ((v2_struct_0 @ sk_B)
% 0.22/0.50          | ~ (v2_pre_topc @ sk_B)
% 0.22/0.50          | ~ (l1_pre_topc @ sk_B)
% 0.22/0.50          | (v2_struct_0 @ X0)
% 0.22/0.50          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.22/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.22/0.50          | ~ (v3_pre_topc @ X2 @ sk_B)
% 0.22/0.50          | ~ (r2_hidden @ X1 @ X2)
% 0.22/0.50          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.22/0.50          | ~ (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.22/0.50               X1)
% 0.22/0.50          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1)
% 0.22/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.22/0.50          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.22/0.50          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.22/0.50          | ~ (v1_funct_1 @ sk_C)
% 0.22/0.50          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.50          | ~ (v2_pre_topc @ sk_A)
% 0.22/0.50          | (v2_struct_0 @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['22', '24'])).
% 0.22/0.50  thf('26', plain, ((v2_pre_topc @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('27', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('28', plain,
% 0.22/0.50      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('29', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('31', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('32', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.50         ((v2_struct_0 @ sk_B)
% 0.22/0.50          | (v2_struct_0 @ X0)
% 0.22/0.50          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.22/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.22/0.50          | ~ (v3_pre_topc @ X2 @ sk_B)
% 0.22/0.50          | ~ (r2_hidden @ X1 @ X2)
% 0.22/0.50          | ~ (r1_tarski @ X2 @ (u1_struct_0 @ X0))
% 0.22/0.50          | ~ (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.22/0.50               X1)
% 0.22/0.50          | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1)
% 0.22/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.22/0.50          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.22/0.50          | (v2_struct_0 @ sk_A))),
% 0.22/0.50      inference('demod', [status(thm)],
% 0.22/0.50                ['25', '26', '27', '28', '29', '30', '31'])).
% 0.22/0.50  thf('33', plain,
% 0.22/0.50      ((![X0 : $i]:
% 0.22/0.50          ((v2_struct_0 @ sk_A)
% 0.22/0.50           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.22/0.50           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D))
% 0.22/0.50           | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)
% 0.22/0.50           | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D))
% 0.22/0.50           | ~ (r2_hidden @ sk_E @ X0)
% 0.22/0.50           | ~ (v3_pre_topc @ X0 @ sk_B)
% 0.22/0.50           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.22/0.50           | ~ (m1_pre_topc @ sk_D @ sk_B)
% 0.22/0.50           | (v2_struct_0 @ sk_D)
% 0.22/0.50           | (v2_struct_0 @ sk_B)))
% 0.22/0.50         <= (((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.22/0.50               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_F)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['21', '32'])).
% 0.22/0.50  thf('34', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D))),
% 0.22/0.50      inference('demod', [status(thm)], ['2', '3'])).
% 0.22/0.50  thf('35', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('36', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('37', plain,
% 0.22/0.50      ((![X0 : $i]:
% 0.22/0.50          ((v2_struct_0 @ sk_A)
% 0.22/0.50           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.22/0.50           | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)
% 0.22/0.50           | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_D))
% 0.22/0.50           | ~ (r2_hidden @ sk_E @ X0)
% 0.22/0.50           | ~ (v3_pre_topc @ X0 @ sk_B)
% 0.22/0.50           | (v2_struct_0 @ sk_D)
% 0.22/0.50           | (v2_struct_0 @ sk_B)))
% 0.22/0.50         <= (((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.22/0.50               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_F)))),
% 0.22/0.50      inference('demod', [status(thm)], ['33', '34', '35', '36'])).
% 0.22/0.50  thf('38', plain,
% 0.22/0.50      ((((v2_struct_0 @ sk_B)
% 0.22/0.50         | (v2_struct_0 @ sk_D)
% 0.22/0.50         | ~ (v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_B)
% 0.22/0.50         | ~ (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D))
% 0.22/0.50         | ~ (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_D))
% 0.22/0.50         | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)
% 0.22/0.50         | (v2_struct_0 @ sk_A)))
% 0.22/0.50         <= (((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.22/0.50               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_F)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['17', '37'])).
% 0.22/0.50  thf('39', plain,
% 0.22/0.50      ((m1_subset_1 @ (u1_struct_0 @ sk_D) @ 
% 0.22/0.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.50      inference('demod', [status(thm)], ['15', '16'])).
% 0.22/0.50  thf(t16_tsep_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.50           ( ![C:$i]:
% 0.22/0.50             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.50               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.22/0.50                 ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 0.22/0.50                   ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.22/0.50  thf('40', plain,
% 0.22/0.50      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.50         (~ (m1_pre_topc @ X12 @ X13)
% 0.22/0.50          | ((X14) != (u1_struct_0 @ X12))
% 0.22/0.50          | ~ (v1_tsep_1 @ X12 @ X13)
% 0.22/0.50          | ~ (m1_pre_topc @ X12 @ X13)
% 0.22/0.50          | (v3_pre_topc @ X14 @ X13)
% 0.22/0.50          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.22/0.50          | ~ (l1_pre_topc @ X13)
% 0.22/0.50          | ~ (v2_pre_topc @ X13))),
% 0.22/0.50      inference('cnf', [status(esa)], [t16_tsep_1])).
% 0.22/0.50  thf('41', plain,
% 0.22/0.50      (![X12 : $i, X13 : $i]:
% 0.22/0.50         (~ (v2_pre_topc @ X13)
% 0.22/0.50          | ~ (l1_pre_topc @ X13)
% 0.22/0.50          | ~ (m1_subset_1 @ (u1_struct_0 @ X12) @ 
% 0.22/0.50               (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.22/0.50          | (v3_pre_topc @ (u1_struct_0 @ X12) @ X13)
% 0.22/0.50          | ~ (v1_tsep_1 @ X12 @ X13)
% 0.22/0.50          | ~ (m1_pre_topc @ X12 @ X13))),
% 0.22/0.50      inference('simplify', [status(thm)], ['40'])).
% 0.22/0.50  thf('42', plain,
% 0.22/0.50      ((~ (m1_pre_topc @ sk_D @ sk_B)
% 0.22/0.50        | ~ (v1_tsep_1 @ sk_D @ sk_B)
% 0.22/0.50        | (v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_B)
% 0.22/0.50        | ~ (l1_pre_topc @ sk_B)
% 0.22/0.50        | ~ (v2_pre_topc @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['39', '41'])).
% 0.22/0.50  thf('43', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('44', plain, ((v1_tsep_1 @ sk_D @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('45', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('46', plain, ((v2_pre_topc @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('47', plain, ((v3_pre_topc @ (u1_struct_0 @ sk_D) @ sk_B)),
% 0.22/0.50      inference('demod', [status(thm)], ['42', '43', '44', '45', '46'])).
% 0.22/0.50  thf('48', plain,
% 0.22/0.50      ((((v2_struct_0 @ sk_B)
% 0.22/0.50         | (v2_struct_0 @ sk_D)
% 0.22/0.50         | ~ (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D))
% 0.22/0.50         | ~ (r1_tarski @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_D))
% 0.22/0.50         | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)
% 0.22/0.50         | (v2_struct_0 @ sk_A)))
% 0.22/0.50         <= (((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.22/0.50               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_F)))),
% 0.22/0.50      inference('demod', [status(thm)], ['38', '47'])).
% 0.22/0.50  thf('49', plain,
% 0.22/0.50      (((~ (l1_pre_topc @ sk_D)
% 0.22/0.50         | (v2_struct_0 @ sk_A)
% 0.22/0.50         | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)
% 0.22/0.50         | ~ (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D))
% 0.22/0.50         | (v2_struct_0 @ sk_D)
% 0.22/0.50         | (v2_struct_0 @ sk_B)))
% 0.22/0.50         <= (((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.22/0.50               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_F)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['12', '48'])).
% 0.22/0.50  thf('50', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(dt_m1_pre_topc, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( l1_pre_topc @ A ) =>
% 0.22/0.50       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.22/0.50  thf('51', plain,
% 0.22/0.50      (![X6 : $i, X7 : $i]:
% 0.22/0.50         (~ (m1_pre_topc @ X6 @ X7) | (l1_pre_topc @ X6) | ~ (l1_pre_topc @ X7))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.22/0.50  thf('52', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_D))),
% 0.22/0.50      inference('sup-', [status(thm)], ['50', '51'])).
% 0.22/0.50  thf('53', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('54', plain, ((l1_pre_topc @ sk_D)),
% 0.22/0.50      inference('demod', [status(thm)], ['52', '53'])).
% 0.22/0.50  thf('55', plain,
% 0.22/0.50      ((((v2_struct_0 @ sk_A)
% 0.22/0.50         | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)
% 0.22/0.50         | ~ (r2_hidden @ sk_E @ (u1_struct_0 @ sk_D))
% 0.22/0.50         | (v2_struct_0 @ sk_D)
% 0.22/0.50         | (v2_struct_0 @ sk_B)))
% 0.22/0.50         <= (((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.22/0.50               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_F)))),
% 0.22/0.50      inference('demod', [status(thm)], ['49', '54'])).
% 0.22/0.50  thf('56', plain,
% 0.22/0.50      ((((v1_xboole_0 @ (u1_struct_0 @ sk_D))
% 0.22/0.50         | (v2_struct_0 @ sk_B)
% 0.22/0.50         | (v2_struct_0 @ sk_D)
% 0.22/0.50         | (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)
% 0.22/0.50         | (v2_struct_0 @ sk_A)))
% 0.22/0.50         <= (((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.22/0.50               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_F)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['6', '55'])).
% 0.22/0.50  thf('57', plain,
% 0.22/0.50      ((~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E))
% 0.22/0.50         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.22/0.50      inference('split', [status(esa)], ['0'])).
% 0.22/0.50  thf('58', plain,
% 0.22/0.50      ((((v2_struct_0 @ sk_A)
% 0.22/0.50         | (v2_struct_0 @ sk_D)
% 0.22/0.50         | (v2_struct_0 @ sk_B)
% 0.22/0.50         | (v1_xboole_0 @ (u1_struct_0 @ sk_D))))
% 0.22/0.50         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)) & 
% 0.22/0.50             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.22/0.50               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_F)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['56', '57'])).
% 0.22/0.50  thf(fc2_struct_0, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.50       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.22/0.50  thf('59', plain,
% 0.22/0.50      (![X8 : $i]:
% 0.22/0.50         (~ (v1_xboole_0 @ (u1_struct_0 @ X8))
% 0.22/0.50          | ~ (l1_struct_0 @ X8)
% 0.22/0.50          | (v2_struct_0 @ X8))),
% 0.22/0.50      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.22/0.50  thf('60', plain,
% 0.22/0.50      ((((v2_struct_0 @ sk_B)
% 0.22/0.50         | (v2_struct_0 @ sk_D)
% 0.22/0.50         | (v2_struct_0 @ sk_A)
% 0.22/0.50         | (v2_struct_0 @ sk_D)
% 0.22/0.50         | ~ (l1_struct_0 @ sk_D)))
% 0.22/0.50         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)) & 
% 0.22/0.50             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.22/0.50               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_F)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['58', '59'])).
% 0.22/0.50  thf('61', plain, ((l1_pre_topc @ sk_D)),
% 0.22/0.50      inference('demod', [status(thm)], ['52', '53'])).
% 0.22/0.50  thf(dt_l1_pre_topc, axiom,
% 0.22/0.50    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.22/0.50  thf('62', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.50  thf('63', plain, ((l1_struct_0 @ sk_D)),
% 0.22/0.50      inference('sup-', [status(thm)], ['61', '62'])).
% 0.22/0.50  thf('64', plain,
% 0.22/0.50      ((((v2_struct_0 @ sk_B)
% 0.22/0.50         | (v2_struct_0 @ sk_D)
% 0.22/0.50         | (v2_struct_0 @ sk_A)
% 0.22/0.50         | (v2_struct_0 @ sk_D)))
% 0.22/0.50         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)) & 
% 0.22/0.50             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.22/0.50               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_F)))),
% 0.22/0.50      inference('demod', [status(thm)], ['60', '63'])).
% 0.22/0.50  thf('65', plain,
% 0.22/0.50      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B)))
% 0.22/0.50         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)) & 
% 0.22/0.50             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.22/0.50               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_F)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['64'])).
% 0.22/0.50  thf('66', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('67', plain,
% 0.22/0.50      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D)))
% 0.22/0.50         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)) & 
% 0.22/0.50             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.22/0.50               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_F)))),
% 0.22/0.50      inference('clc', [status(thm)], ['65', '66'])).
% 0.22/0.50  thf('68', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('69', plain,
% 0.22/0.50      (((v2_struct_0 @ sk_D))
% 0.22/0.50         <= (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)) & 
% 0.22/0.50             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.22/0.50               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_F)))),
% 0.22/0.50      inference('clc', [status(thm)], ['67', '68'])).
% 0.22/0.50  thf('70', plain, (~ (v2_struct_0 @ sk_D)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('71', plain,
% 0.22/0.50      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)) | 
% 0.22/0.50       ~
% 0.22/0.50       ((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.22/0.50         sk_F))),
% 0.22/0.50      inference('sup-', [status(thm)], ['69', '70'])).
% 0.22/0.50  thf('72', plain,
% 0.22/0.50      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)) | 
% 0.22/0.50       ((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.22/0.50         sk_F))),
% 0.22/0.50      inference('split', [status(esa)], ['18'])).
% 0.22/0.50  thf('73', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_D))),
% 0.22/0.50      inference('demod', [status(thm)], ['2', '3'])).
% 0.22/0.50  thf('74', plain,
% 0.22/0.50      (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E))
% 0.22/0.50         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.22/0.50      inference('split', [status(esa)], ['18'])).
% 0.22/0.50  thf('75', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_C @ 
% 0.22/0.50        (k1_zfmisc_1 @ 
% 0.22/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(t64_tmap_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.50             ( l1_pre_topc @ B ) ) =>
% 0.22/0.50           ( ![C:$i]:
% 0.22/0.50             ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.50                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.22/0.50                 ( m1_subset_1 @
% 0.22/0.50                   C @ 
% 0.22/0.50                   ( k1_zfmisc_1 @
% 0.22/0.50                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.22/0.50               ( ![D:$i]:
% 0.22/0.50                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.22/0.50                   ( ![E:$i]:
% 0.22/0.50                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.22/0.50                       ( ![F:$i]:
% 0.22/0.50                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.22/0.50                           ( ( ( ( E ) = ( F ) ) & 
% 0.22/0.50                               ( r1_tmap_1 @ B @ A @ C @ E ) ) =>
% 0.22/0.50                             ( r1_tmap_1 @
% 0.22/0.50                               D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.50  thf('76', plain,
% 0.22/0.50      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.22/0.50         ((v2_struct_0 @ X18)
% 0.22/0.50          | ~ (v2_pre_topc @ X18)
% 0.22/0.50          | ~ (l1_pre_topc @ X18)
% 0.22/0.50          | (v2_struct_0 @ X19)
% 0.22/0.50          | ~ (m1_pre_topc @ X19 @ X18)
% 0.22/0.50          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X19))
% 0.22/0.50          | (r1_tmap_1 @ X19 @ X21 @ (k2_tmap_1 @ X18 @ X21 @ X22 @ X19) @ X20)
% 0.22/0.50          | ((X23) != (X20))
% 0.22/0.50          | ~ (r1_tmap_1 @ X18 @ X21 @ X22 @ X23)
% 0.22/0.50          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X18))
% 0.22/0.50          | ~ (m1_subset_1 @ X22 @ 
% 0.22/0.50               (k1_zfmisc_1 @ 
% 0.22/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X21))))
% 0.22/0.50          | ~ (v1_funct_2 @ X22 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X21))
% 0.22/0.50          | ~ (v1_funct_1 @ X22)
% 0.22/0.50          | ~ (l1_pre_topc @ X21)
% 0.22/0.50          | ~ (v2_pre_topc @ X21)
% 0.22/0.50          | (v2_struct_0 @ X21))),
% 0.22/0.50      inference('cnf', [status(esa)], [t64_tmap_1])).
% 0.22/0.50  thf('77', plain,
% 0.22/0.50      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.22/0.50         ((v2_struct_0 @ X21)
% 0.22/0.50          | ~ (v2_pre_topc @ X21)
% 0.22/0.50          | ~ (l1_pre_topc @ X21)
% 0.22/0.50          | ~ (v1_funct_1 @ X22)
% 0.22/0.50          | ~ (v1_funct_2 @ X22 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X21))
% 0.22/0.50          | ~ (m1_subset_1 @ X22 @ 
% 0.22/0.50               (k1_zfmisc_1 @ 
% 0.22/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X21))))
% 0.22/0.50          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X18))
% 0.22/0.50          | ~ (r1_tmap_1 @ X18 @ X21 @ X22 @ X20)
% 0.22/0.50          | (r1_tmap_1 @ X19 @ X21 @ (k2_tmap_1 @ X18 @ X21 @ X22 @ X19) @ X20)
% 0.22/0.50          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X19))
% 0.22/0.50          | ~ (m1_pre_topc @ X19 @ X18)
% 0.22/0.50          | (v2_struct_0 @ X19)
% 0.22/0.50          | ~ (l1_pre_topc @ X18)
% 0.22/0.50          | ~ (v2_pre_topc @ X18)
% 0.22/0.50          | (v2_struct_0 @ X18))),
% 0.22/0.50      inference('simplify', [status(thm)], ['76'])).
% 0.22/0.50  thf('78', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((v2_struct_0 @ sk_B)
% 0.22/0.50          | ~ (v2_pre_topc @ sk_B)
% 0.22/0.50          | ~ (l1_pre_topc @ sk_B)
% 0.22/0.50          | (v2_struct_0 @ X0)
% 0.22/0.50          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.22/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.22/0.50          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ X1)
% 0.22/0.50          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1)
% 0.22/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.22/0.50          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.22/0.50          | ~ (v1_funct_1 @ sk_C)
% 0.22/0.50          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.50          | ~ (v2_pre_topc @ sk_A)
% 0.22/0.50          | (v2_struct_0 @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['75', '77'])).
% 0.22/0.50  thf('79', plain, ((v2_pre_topc @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('80', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('81', plain,
% 0.22/0.50      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('82', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('84', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('85', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((v2_struct_0 @ sk_B)
% 0.22/0.50          | (v2_struct_0 @ X0)
% 0.22/0.50          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.22/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.22/0.50          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ X1)
% 0.22/0.50          | ~ (r1_tmap_1 @ sk_B @ sk_A @ sk_C @ X1)
% 0.22/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.22/0.50          | (v2_struct_0 @ sk_A))),
% 0.22/0.50      inference('demod', [status(thm)],
% 0.22/0.50                ['78', '79', '80', '81', '82', '83', '84'])).
% 0.22/0.50  thf('86', plain,
% 0.22/0.50      ((![X0 : $i]:
% 0.22/0.50          ((v2_struct_0 @ sk_A)
% 0.22/0.50           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))
% 0.22/0.50           | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.22/0.50              sk_E)
% 0.22/0.50           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ X0))
% 0.22/0.50           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.22/0.50           | (v2_struct_0 @ X0)
% 0.22/0.50           | (v2_struct_0 @ sk_B)))
% 0.22/0.50         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['74', '85'])).
% 0.22/0.50  thf('87', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('88', plain,
% 0.22/0.50      ((![X0 : $i]:
% 0.22/0.50          ((v2_struct_0 @ sk_A)
% 0.22/0.50           | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.22/0.50              sk_E)
% 0.22/0.50           | ~ (m1_subset_1 @ sk_E @ (u1_struct_0 @ X0))
% 0.22/0.50           | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.22/0.50           | (v2_struct_0 @ X0)
% 0.22/0.50           | (v2_struct_0 @ sk_B)))
% 0.22/0.50         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.22/0.50      inference('demod', [status(thm)], ['86', '87'])).
% 0.22/0.50  thf('89', plain,
% 0.22/0.50      ((((v2_struct_0 @ sk_B)
% 0.22/0.50         | (v2_struct_0 @ sk_D)
% 0.22/0.50         | ~ (m1_pre_topc @ sk_D @ sk_B)
% 0.22/0.50         | (r1_tmap_1 @ sk_D @ sk_A @ 
% 0.22/0.50            (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_E)
% 0.22/0.50         | (v2_struct_0 @ sk_A)))
% 0.22/0.50         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['73', '88'])).
% 0.22/0.50  thf('90', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('91', plain,
% 0.22/0.50      ((((v2_struct_0 @ sk_B)
% 0.22/0.50         | (v2_struct_0 @ sk_D)
% 0.22/0.50         | (r1_tmap_1 @ sk_D @ sk_A @ 
% 0.22/0.50            (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_E)
% 0.22/0.50         | (v2_struct_0 @ sk_A)))
% 0.22/0.50         <= (((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.22/0.50      inference('demod', [status(thm)], ['89', '90'])).
% 0.22/0.50  thf('92', plain,
% 0.22/0.50      ((~ (r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.22/0.50           sk_F))
% 0.22/0.50         <= (~
% 0.22/0.50             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.22/0.50               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_F)))),
% 0.22/0.50      inference('split', [status(esa)], ['0'])).
% 0.22/0.50  thf('93', plain, (((sk_E) = (sk_F))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('94', plain,
% 0.22/0.50      ((~ (r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.22/0.50           sk_E))
% 0.22/0.50         <= (~
% 0.22/0.50             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.22/0.50               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_F)))),
% 0.22/0.50      inference('demod', [status(thm)], ['92', '93'])).
% 0.22/0.50  thf('95', plain,
% 0.22/0.50      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B)))
% 0.22/0.50         <= (~
% 0.22/0.50             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.22/0.50               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_F)) & 
% 0.22/0.50             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['91', '94'])).
% 0.22/0.50  thf('96', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('97', plain,
% 0.22/0.50      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D)))
% 0.22/0.50         <= (~
% 0.22/0.50             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.22/0.50               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_F)) & 
% 0.22/0.50             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.22/0.50      inference('clc', [status(thm)], ['95', '96'])).
% 0.22/0.50  thf('98', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('99', plain,
% 0.22/0.50      (((v2_struct_0 @ sk_D))
% 0.22/0.50         <= (~
% 0.22/0.50             ((r1_tmap_1 @ sk_D @ sk_A @ 
% 0.22/0.50               (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ sk_F)) & 
% 0.22/0.50             ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.22/0.50      inference('clc', [status(thm)], ['97', '98'])).
% 0.22/0.50  thf('100', plain, (~ (v2_struct_0 @ sk_D)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('101', plain,
% 0.22/0.50      (~ ((r1_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_E)) | 
% 0.22/0.50       ((r1_tmap_1 @ sk_D @ sk_A @ (k2_tmap_1 @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.22/0.50         sk_F))),
% 0.22/0.50      inference('sup-', [status(thm)], ['99', '100'])).
% 0.22/0.50  thf('102', plain, ($false),
% 0.22/0.50      inference('sat_resolution*', [status(thm)], ['1', '71', '72', '101'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
