%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EcLBwAmJNg

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:30 EST 2020

% Result     : Theorem 0.66s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :  432 (217033 expanded)
%              Number of leaves         :   47 (61368 expanded)
%              Depth                    :   39
%              Number of atoms          : 7188 (7776487 expanded)
%              Number of equality atoms :  138 (111198 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(fc6_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
        & ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X41: $i] :
      ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X41 ) @ ( u1_pre_topc @ X41 ) ) )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v2_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X40: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X40 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) ) )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(dt_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) )
        & ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X38: $i,X39: $i] :
      ( ( l1_pre_topc @ ( g1_pre_topc @ X38 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_pre_topc])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t64_pre_topc,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ! [D: $i] :
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )
                 => ( ( C = D )
                   => ( ( v5_pre_topc @ C @ A @ B )
                    <=> ( v5_pre_topc @ D @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ( v2_pre_topc @ B )
              & ( l1_pre_topc @ B ) )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ! [D: $i] :
                    ( ( ( v1_funct_1 @ D )
                      & ( v1_funct_2 @ D @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) )
                      & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )
                   => ( ( C = D )
                     => ( ( v5_pre_topc @ C @ A @ B )
                      <=> ( v5_pre_topc @ D @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_pre_topc])).

thf('4',plain,
    ( ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t132_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( v1_partfun1 @ C @ A ) ) ) ) )).

thf('7',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( X35 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X35 ) ) )
      | ( v1_partfun1 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X35 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X37 @ X35 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('8',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_2 @ X36 @ X37 @ X35 )
      | ( v1_partfun1 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X35 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    sk_C = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('16',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v5_relat_1 @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('17',plain,(
    v5_relat_1 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('18',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v5_relat_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k2_relat_1 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('21',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('22',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t14_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) )).

thf('25',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X24 ) @ X25 )
      | ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[t14_relset_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('28',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_partfun1 @ X32 @ X33 )
      | ( v1_funct_2 @ X32 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('29',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ~ ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ~ ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf(t63_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ! [D: $i] :
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )
                 => ( ( C = D )
                   => ( ( v5_pre_topc @ C @ A @ B )
                    <=> ( v5_pre_topc @ D @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) ) ) )).

thf('34',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( v2_pre_topc @ X46 )
      | ~ ( l1_pre_topc @ X46 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_funct_2 @ X47 @ ( u1_struct_0 @ X48 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X46 ) @ ( u1_pre_topc @ X46 ) ) ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X48 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X46 ) @ ( u1_pre_topc @ X46 ) ) ) ) ) )
      | ~ ( v5_pre_topc @ X49 @ X48 @ X46 )
      | ( v5_pre_topc @ X47 @ X48 @ ( g1_pre_topc @ ( u1_struct_0 @ X46 ) @ ( u1_pre_topc @ X46 ) ) )
      | ( X49 != X47 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X48 ) @ ( u1_struct_0 @ X46 ) ) ) )
      | ~ ( v1_funct_2 @ X49 @ ( u1_struct_0 @ X48 ) @ ( u1_struct_0 @ X46 ) )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( l1_pre_topc @ X48 )
      | ~ ( v2_pre_topc @ X48 ) ) ),
    inference(cnf,[status(esa)],[t63_pre_topc])).

thf('35',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( v2_pre_topc @ X48 )
      | ~ ( l1_pre_topc @ X48 )
      | ~ ( v1_funct_2 @ X47 @ ( u1_struct_0 @ X48 ) @ ( u1_struct_0 @ X46 ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X48 ) @ ( u1_struct_0 @ X46 ) ) ) )
      | ( v5_pre_topc @ X47 @ X48 @ ( g1_pre_topc @ ( u1_struct_0 @ X46 ) @ ( u1_pre_topc @ X46 ) ) )
      | ~ ( v5_pre_topc @ X47 @ X48 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X48 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X46 ) @ ( u1_pre_topc @ X46 ) ) ) ) ) )
      | ~ ( v1_funct_2 @ X47 @ ( u1_struct_0 @ X48 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X46 ) @ ( u1_pre_topc @ X46 ) ) ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( l1_pre_topc @ X46 )
      | ~ ( v2_pre_topc @ X46 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ~ ( v2_pre_topc @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
    | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
    | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['36','37','38','39','40','41','42','43'])).

thf('45',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['32','44'])).

thf('46',plain,
    ( ( ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ( ( u1_struct_0 @ sk_B_1 )
        = k1_xboole_0 ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['5','45'])).

thf('47',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','31'])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t62_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ! [D: $i] :
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ ( u1_struct_0 @ B ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ ( u1_struct_0 @ B ) ) ) ) )
                 => ( ( C = D )
                   => ( ( v5_pre_topc @ C @ A @ B )
                    <=> ( v5_pre_topc @ D @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) @ B ) ) ) ) ) ) ) )).

thf('49',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( v2_pre_topc @ X42 )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X44 ) @ ( u1_pre_topc @ X44 ) ) ) @ ( u1_struct_0 @ X42 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X44 ) @ ( u1_pre_topc @ X44 ) ) ) @ ( u1_struct_0 @ X42 ) ) ) )
      | ~ ( v5_pre_topc @ X45 @ X44 @ X42 )
      | ( v5_pre_topc @ X43 @ ( g1_pre_topc @ ( u1_struct_0 @ X44 ) @ ( u1_pre_topc @ X44 ) ) @ X42 )
      | ( X45 != X43 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X44 ) @ ( u1_struct_0 @ X42 ) ) ) )
      | ~ ( v1_funct_2 @ X45 @ ( u1_struct_0 @ X44 ) @ ( u1_struct_0 @ X42 ) )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( l1_pre_topc @ X44 )
      | ~ ( v2_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[t62_pre_topc])).

thf('50',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( v2_pre_topc @ X44 )
      | ~ ( l1_pre_topc @ X44 )
      | ~ ( v1_funct_2 @ X43 @ ( u1_struct_0 @ X44 ) @ ( u1_struct_0 @ X42 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X44 ) @ ( u1_struct_0 @ X42 ) ) ) )
      | ( v5_pre_topc @ X43 @ ( g1_pre_topc @ ( u1_struct_0 @ X44 ) @ ( u1_pre_topc @ X44 ) ) @ X42 )
      | ~ ( v5_pre_topc @ X43 @ X44 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X44 ) @ ( u1_pre_topc @ X44 ) ) ) @ ( u1_struct_0 @ X42 ) ) ) )
      | ~ ( v1_funct_2 @ X43 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X44 ) @ ( u1_pre_topc @ X44 ) ) ) @ ( u1_struct_0 @ X42 ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( v2_pre_topc @ X42 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    sk_C = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['51','52','55','56','57','58'])).

thf('60',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['47','59'])).

thf('61',plain,
    ( ( ( ( u1_struct_0 @ sk_B_1 )
        = k1_xboole_0 )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ( ( u1_struct_0 @ sk_B_1 )
        = k1_xboole_0 ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['46','60'])).

thf('62',plain,
    ( ( ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ( ( u1_struct_0 @ sk_B_1 )
        = k1_xboole_0 ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ( ~ ( l1_pre_topc @ sk_B_1 )
      | ( ( u1_struct_0 @ sk_B_1 )
        = k1_xboole_0 )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','62'])).

thf('64',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( ( ( u1_struct_0 @ sk_B_1 )
        = k1_xboole_0 )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ~ ( v2_pre_topc @ sk_B_1 )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ( ( u1_struct_0 @ sk_B_1 )
        = k1_xboole_0 ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','65'])).

thf('67',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ( ( u1_struct_0 @ sk_B_1 )
        = k1_xboole_0 ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,
    ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
   <= ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(split,[status(esa)],['70'])).

thf('72',plain,(
    sk_C = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
   <= ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['69','73'])).

thf('75',plain,
    ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['51','52','55','56','57','58'])).

thf('76',plain,
    ( ( ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ k1_xboole_0 @ ( u1_pre_topc @ sk_B_1 ) ) ) )
      | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['69','73'])).

thf('78',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['69','73'])).

thf('79',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['69','73'])).

thf('80',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['69','73'])).

thf('81',plain,
    ( ( ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ k1_xboole_0 @ ( u1_pre_topc @ sk_B_1 ) ) ) )
      | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ k1_xboole_0 @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ k1_xboole_0 @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ k1_xboole_0 @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ k1_xboole_0 @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['76','77','78','79','80'])).

thf(t29_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) )).

thf('82',plain,(
    ! [X28: $i] :
      ( ( X28 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X28 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('83',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['69','73'])).

thf('84',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('85',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) )
        | ~ ( r2_hidden @ X0 @ sk_C ) )
   <= ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('88',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('89',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['88'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('90',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('91',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_C )
   <= ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['87','89','90'])).

thf('92',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['82','91'])).

thf('93',plain,
    ( ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    sk_C = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
   <= ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(split,[status(esa)],['95'])).

thf('97',plain,
    ( ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
   <= ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('98',plain,
    ( ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    sk_C = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('104',plain,(
    ! [X41: $i] :
      ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X41 ) @ ( u1_pre_topc @ X41 ) ) )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v2_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf('105',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','31'])).

thf('106',plain,
    ( ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('107',plain,(
    sk_C = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('110',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( v2_pre_topc @ X42 )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X44 ) @ ( u1_pre_topc @ X44 ) ) ) @ ( u1_struct_0 @ X42 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X44 ) @ ( u1_pre_topc @ X44 ) ) ) @ ( u1_struct_0 @ X42 ) ) ) )
      | ~ ( v5_pre_topc @ X43 @ ( g1_pre_topc @ ( u1_struct_0 @ X44 ) @ ( u1_pre_topc @ X44 ) ) @ X42 )
      | ( v5_pre_topc @ X45 @ X44 @ X42 )
      | ( X45 != X43 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X44 ) @ ( u1_struct_0 @ X42 ) ) ) )
      | ~ ( v1_funct_2 @ X45 @ ( u1_struct_0 @ X44 ) @ ( u1_struct_0 @ X42 ) )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( l1_pre_topc @ X44 )
      | ~ ( v2_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[t62_pre_topc])).

thf('111',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( v2_pre_topc @ X44 )
      | ~ ( l1_pre_topc @ X44 )
      | ~ ( v1_funct_2 @ X43 @ ( u1_struct_0 @ X44 ) @ ( u1_struct_0 @ X42 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X44 ) @ ( u1_struct_0 @ X42 ) ) ) )
      | ( v5_pre_topc @ X43 @ X44 @ X42 )
      | ~ ( v5_pre_topc @ X43 @ ( g1_pre_topc @ ( u1_struct_0 @ X44 ) @ ( u1_pre_topc @ X44 ) ) @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X44 ) @ ( u1_pre_topc @ X44 ) ) ) @ ( u1_struct_0 @ X42 ) ) ) )
      | ~ ( v1_funct_2 @ X43 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X44 ) @ ( u1_pre_topc @ X44 ) ) ) @ ( u1_struct_0 @ X42 ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( v2_pre_topc @ X42 ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,
    ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['109','111'])).

thf('113',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('115',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('116',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['112','113','114','115','116','117'])).

thf('119',plain,
    ( ( ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
      | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['108','118'])).

thf('120',plain,
    ( ( ( ( u1_struct_0 @ sk_B_1 )
        = k1_xboole_0 )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['105','119'])).

thf('121',plain,
    ( ( ~ ( v2_pre_topc @ sk_B_1 )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ( ( u1_struct_0 @ sk_B_1 )
        = k1_xboole_0 ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['104','120'])).

thf('122',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ( ( u1_struct_0 @ sk_B_1 )
        = k1_xboole_0 ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['121','122','123'])).

thf('125',plain,
    ( ( ~ ( l1_pre_topc @ sk_B_1 )
      | ( ( u1_struct_0 @ sk_B_1 )
        = k1_xboole_0 )
      | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['103','124'])).

thf('126',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( ( ( u1_struct_0 @ sk_B_1 )
        = k1_xboole_0 )
      | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','31'])).

thf('129',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('130',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( v2_pre_topc @ X46 )
      | ~ ( l1_pre_topc @ X46 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_funct_2 @ X47 @ ( u1_struct_0 @ X48 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X46 ) @ ( u1_pre_topc @ X46 ) ) ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X48 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X46 ) @ ( u1_pre_topc @ X46 ) ) ) ) ) )
      | ~ ( v5_pre_topc @ X47 @ X48 @ ( g1_pre_topc @ ( u1_struct_0 @ X46 ) @ ( u1_pre_topc @ X46 ) ) )
      | ( v5_pre_topc @ X49 @ X48 @ X46 )
      | ( X49 != X47 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X48 ) @ ( u1_struct_0 @ X46 ) ) ) )
      | ~ ( v1_funct_2 @ X49 @ ( u1_struct_0 @ X48 ) @ ( u1_struct_0 @ X46 ) )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( l1_pre_topc @ X48 )
      | ~ ( v2_pre_topc @ X48 ) ) ),
    inference(cnf,[status(esa)],[t63_pre_topc])).

thf('131',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( v2_pre_topc @ X48 )
      | ~ ( l1_pre_topc @ X48 )
      | ~ ( v1_funct_2 @ X47 @ ( u1_struct_0 @ X48 ) @ ( u1_struct_0 @ X46 ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X48 ) @ ( u1_struct_0 @ X46 ) ) ) )
      | ( v5_pre_topc @ X47 @ X48 @ X46 )
      | ~ ( v5_pre_topc @ X47 @ X48 @ ( g1_pre_topc @ ( u1_struct_0 @ X46 ) @ ( u1_pre_topc @ X46 ) ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X48 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X46 ) @ ( u1_pre_topc @ X46 ) ) ) ) ) )
      | ~ ( v1_funct_2 @ X47 @ ( u1_struct_0 @ X48 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X46 ) @ ( u1_pre_topc @ X46 ) ) ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( l1_pre_topc @ X46 )
      | ~ ( v2_pre_topc @ X46 ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,
    ( ~ ( v2_pre_topc @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['129','131'])).

thf('133',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['132','133','134','135','136','137','138','139'])).

thf('141',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['128','140'])).

thf('142',plain,
    ( ( ( ( u1_struct_0 @ sk_B_1 )
        = k1_xboole_0 )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
      | ( ( u1_struct_0 @ sk_B_1 )
        = k1_xboole_0 ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['127','141'])).

thf('143',plain,
    ( ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
      | ( ( u1_struct_0 @ sk_B_1 )
        = k1_xboole_0 ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['142'])).

thf('144',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
   <= ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['70'])).

thf('145',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X28: $i] :
      ( ( X28 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X28 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('147',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('149',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) )
        | ~ ( r2_hidden @ X0 @ sk_C ) )
   <= ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['88'])).

thf('151',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('152',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_C )
   <= ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['149','150','151'])).

thf('153',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['146','152'])).

thf('154',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = sk_C )
   <= ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['145','153'])).

thf('155',plain,(
    ! [X41: $i] :
      ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X41 ) @ ( u1_pre_topc @ X41 ) ) )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v2_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf('156',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('157',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('158',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_2 @ X36 @ X37 @ X35 )
      | ( v1_partfun1 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X35 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('159',plain,
    ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('162',plain,
    ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      = k1_xboole_0 )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['159','160','161'])).

thf('163',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('164',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v4_relat_1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('165',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('166',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v4_relat_1 @ X10 @ X11 )
      | ( r1_tarski @ ( k1_relat_1 @ X10 ) @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('167',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['20','21'])).

thf('169',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['167','168'])).

thf('170',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t13_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('171',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X20 ) @ X21 )
      | ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['169','172'])).

thf('174',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_partfun1 @ X32 @ X33 )
      | ( v1_funct_2 @ X32 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('175',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['175','176'])).

thf('178',plain,
    ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      = k1_xboole_0 )
    | ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['162','177'])).

thf('179',plain,
    ( ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('180',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('181',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( v2_pre_topc @ X48 )
      | ~ ( l1_pre_topc @ X48 )
      | ~ ( v1_funct_2 @ X47 @ ( u1_struct_0 @ X48 ) @ ( u1_struct_0 @ X46 ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X48 ) @ ( u1_struct_0 @ X46 ) ) ) )
      | ( v5_pre_topc @ X47 @ X48 @ X46 )
      | ~ ( v5_pre_topc @ X47 @ X48 @ ( g1_pre_topc @ ( u1_struct_0 @ X46 ) @ ( u1_pre_topc @ X46 ) ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X48 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X46 ) @ ( u1_pre_topc @ X46 ) ) ) ) ) )
      | ~ ( v1_funct_2 @ X47 @ ( u1_struct_0 @ X48 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X46 ) @ ( u1_pre_topc @ X46 ) ) ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( l1_pre_topc @ X46 )
      | ~ ( v2_pre_topc @ X46 ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('182',plain,
    ( ~ ( v2_pre_topc @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('187',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['169','172'])).

thf('188',plain,
    ( ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['182','183','184','185','186','187'])).

thf('189',plain,
    ( ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['179','188'])).

thf('190',plain,
    ( ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
        = k1_xboole_0 )
      | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['178','189'])).

thf('191',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 )
      | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
        = k1_xboole_0 ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['156','190'])).

thf('192',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,
    ( ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 )
      | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
        = k1_xboole_0 ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['191','192'])).

thf('194',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
        = k1_xboole_0 )
      | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['155','193'])).

thf('195',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,
    ( ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
        = k1_xboole_0 )
      | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['194','195','196'])).

thf('198',plain,
    ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      = k1_xboole_0 )
    | ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['162','177'])).

thf('199',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['169','172'])).

thf('200',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( v2_pre_topc @ X44 )
      | ~ ( l1_pre_topc @ X44 )
      | ~ ( v1_funct_2 @ X43 @ ( u1_struct_0 @ X44 ) @ ( u1_struct_0 @ X42 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X44 ) @ ( u1_struct_0 @ X42 ) ) ) )
      | ( v5_pre_topc @ X43 @ X44 @ X42 )
      | ~ ( v5_pre_topc @ X43 @ ( g1_pre_topc @ ( u1_struct_0 @ X44 ) @ ( u1_pre_topc @ X44 ) ) @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X44 ) @ ( u1_pre_topc @ X44 ) ) ) @ ( u1_struct_0 @ X42 ) ) ) )
      | ~ ( v1_funct_2 @ X43 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X44 ) @ ( u1_pre_topc @ X44 ) ) ) @ ( u1_struct_0 @ X42 ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( v2_pre_topc @ X42 ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('201',plain,
    ( ~ ( v2_pre_topc @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['199','200'])).

thf('202',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['201','202','203','204','205','206','207','208'])).

thf('210',plain,
    ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      = k1_xboole_0 )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
    | ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['198','209'])).

thf('211',plain,
    ( ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
        = k1_xboole_0 )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
      | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
        = k1_xboole_0 ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['197','210'])).

thf('212',plain,
    ( ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
      | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
        = k1_xboole_0 ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['211'])).

thf('213',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['132','133','134','135','136','137','138','139'])).

thf('214',plain,
    ( ( ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['212','213'])).

thf('215',plain,
    ( ( ~ ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['214'])).

thf('216',plain,
    ( ( ~ ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ sk_C @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) )
   <= ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['154','215'])).

thf('217',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('218',plain,
    ( ( ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
      | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['108','118'])).

thf('219',plain,
    ( ( ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ k1_xboole_0 @ ( u1_pre_topc @ sk_B_1 ) ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['217','218'])).

thf('220',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('221',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('222',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('223',plain,
    ( ( ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ k1_xboole_0 @ ( u1_pre_topc @ sk_B_1 ) ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ k1_xboole_0 @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ k1_xboole_0 @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ k1_xboole_0 @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['219','220','221','222'])).

thf('224',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['146','152'])).

thf('225',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['146','152'])).

thf('226',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = sk_C )
   <= ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['145','153'])).

thf('227',plain,(
    ! [X41: $i] :
      ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X41 ) @ ( u1_pre_topc @ X41 ) ) )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v2_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf('228',plain,
    ( ( ( v2_pre_topc @ ( g1_pre_topc @ sk_C @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( v2_pre_topc @ sk_B_1 )
      | ~ ( l1_pre_topc @ sk_B_1 ) )
   <= ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup+',[status(thm)],['226','227'])).

thf('229',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,
    ( ( v2_pre_topc @ ( g1_pre_topc @ sk_C @ ( u1_pre_topc @ sk_B_1 ) ) )
   <= ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['228','229','230'])).

thf('232',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['146','152'])).

thf('233',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = sk_C )
   <= ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['145','153'])).

thf('234',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('235',plain,
    ( ( ( l1_pre_topc @ ( g1_pre_topc @ sk_C @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ sk_B_1 ) )
   <= ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup+',[status(thm)],['233','234'])).

thf('236',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,
    ( ( l1_pre_topc @ ( g1_pre_topc @ sk_C @ ( u1_pre_topc @ sk_B_1 ) ) )
   <= ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['235','236'])).

thf('238',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['146','152'])).

thf('239',plain,
    ( ( ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ sk_C @ ( u1_pre_topc @ sk_B_1 ) ) ) )
      | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ sk_C @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['223','224','225','231','232','237','238'])).

thf('240',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = sk_C )
   <= ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['145','153'])).

thf('241',plain,
    ( ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
      | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
        = k1_xboole_0 ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['211'])).

thf('242',plain,
    ( ( ( ( u1_struct_0 @ ( g1_pre_topc @ sk_C @ ( u1_pre_topc @ sk_B_1 ) ) )
        = k1_xboole_0 )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) )
   <= ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup+',[status(thm)],['240','241'])).

thf('243',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['146','152'])).

thf('244',plain,
    ( ( ( ( u1_struct_0 @ ( g1_pre_topc @ sk_C @ ( u1_pre_topc @ sk_B_1 ) ) )
        = sk_C )
      | ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) )
   <= ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['242','243'])).

thf('245',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
   <= ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['70'])).

thf('246',plain,
    ( ( ( u1_struct_0 @ ( g1_pre_topc @ sk_C @ ( u1_pre_topc @ sk_B_1 ) ) )
      = sk_C )
   <= ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(clc,[status(thm)],['244','245'])).

thf('247',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = sk_C )
   <= ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['145','153'])).

thf('248',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ sk_C )
   <= ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup+',[status(thm)],['247','248'])).

thf('250',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ sk_C @ ( u1_pre_topc @ sk_B_1 ) ) )
   <= ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['239','246','249'])).

thf('251',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['146','152'])).

thf('252',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ sk_C )
   <= ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference('sup+',[status(thm)],['247','248'])).

thf('253',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
   <= ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
      & ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['216','250','251','252'])).

thf('254',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
   <= ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['70'])).

thf('255',plain,
    ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['253','254'])).

thf('256',plain,
    ( ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
   <= ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('257',plain,
    ( ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
   <= ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(split,[status(esa)],['101'])).

thf('258',plain,
    ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['256','257'])).

thf('259',plain,(
    ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['98','102','255','258'])).

thf('260',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(split,[status(esa)],['95'])).

thf('261',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['98','102','255','260'])).

thf('262',plain,(
    sk_C = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['92','259','261'])).

thf('263',plain,(
    sk_C = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['92','259','261'])).

thf('264',plain,(
    sk_C = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['92','259','261'])).

thf('265',plain,(
    sk_C = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['92','259','261'])).

thf('266',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['69','73'])).

thf('267',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['82','91'])).

thf('268',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = sk_C )
   <= ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['266','267'])).

thf('269',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('270',plain,
    ( ( ( l1_pre_topc @ ( g1_pre_topc @ sk_C @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ sk_B_1 ) )
   <= ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['268','269'])).

thf('271',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('272',plain,
    ( ( l1_pre_topc @ ( g1_pre_topc @ sk_C @ ( u1_pre_topc @ sk_B_1 ) ) )
   <= ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['270','271'])).

thf('273',plain,(
    ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['98','102','255','258'])).

thf('274',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['98','102','255','260'])).

thf('275',plain,(
    l1_pre_topc @ ( g1_pre_topc @ sk_C @ ( u1_pre_topc @ sk_B_1 ) ) ),
    inference(simpl_trail,[status(thm)],['272','273','274'])).

thf('276',plain,(
    sk_C = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['92','259','261'])).

thf('277',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = sk_C )
   <= ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['266','267'])).

thf('278',plain,(
    ! [X41: $i] :
      ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X41 ) @ ( u1_pre_topc @ X41 ) ) )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v2_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf('279',plain,
    ( ( ( v2_pre_topc @ ( g1_pre_topc @ sk_C @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( v2_pre_topc @ sk_B_1 )
      | ~ ( l1_pre_topc @ sk_B_1 ) )
   <= ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['277','278'])).

thf('280',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('281',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('282',plain,
    ( ( v2_pre_topc @ ( g1_pre_topc @ sk_C @ ( u1_pre_topc @ sk_B_1 ) ) )
   <= ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['279','280','281'])).

thf('283',plain,(
    ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['98','102','255','258'])).

thf('284',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['98','102','255','260'])).

thf('285',plain,(
    v2_pre_topc @ ( g1_pre_topc @ sk_C @ ( u1_pre_topc @ sk_B_1 ) ) ),
    inference(simpl_trail,[status(thm)],['282','283','284'])).

thf('286',plain,
    ( ( ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ sk_C @ ( u1_pre_topc @ sk_B_1 ) ) ) )
      | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ sk_C @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ sk_C @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['81','262','263','264','265','275','276','285'])).

thf('287',plain,(
    ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['98','102','255','258'])).

thf('288',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['98','102','255','260'])).

thf('289',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ sk_C @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ sk_C @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ sk_C @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(simpl_trail,[status(thm)],['286','287','288'])).

thf('290',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = sk_C )
   <= ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['266','267'])).

thf('291',plain,
    ( ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
   <= ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('292',plain,
    ( ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ sk_C @ ( u1_pre_topc @ sk_B_1 ) ) )
   <= ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['290','291'])).

thf('293',plain,(
    ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['98','102','255','258'])).

thf('294',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['98','102','255','260'])).

thf('295',plain,(
    ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ sk_C @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(simpl_trail,[status(thm)],['292','293','294'])).

thf('296',plain,
    ( ~ ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ sk_C @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ sk_C @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(clc,[status(thm)],['289','295'])).

thf('297',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = sk_C )
   <= ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['266','267'])).

thf('298',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
    | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['36','37','38','39','40','41','42','43'])).

thf('299',plain,
    ( ( ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ sk_C @ ( u1_pre_topc @ sk_B_1 ) ) ) )
      | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) )
   <= ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['297','298'])).

thf('300',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = sk_C )
   <= ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['266','267'])).

thf('301',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('302',plain,
    ( ( ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ sk_C @ ( u1_pre_topc @ sk_B_1 ) ) ) )
      | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ sk_C @ ( u1_pre_topc @ sk_B_1 ) ) ) )
   <= ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['299','300','301'])).

thf('303',plain,(
    ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['98','102','255','258'])).

thf('304',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['98','102','255','260'])).

thf('305',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ sk_C @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ( v5_pre_topc @ sk_C @ sk_A @ ( g1_pre_topc @ sk_C @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(simpl_trail,[status(thm)],['302','303','304'])).

thf('306',plain,(
    ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ sk_C @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ),
    inference(clc,[status(thm)],['296','305'])).

thf('307',plain,(
    ! [X41: $i] :
      ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X41 ) @ ( u1_pre_topc @ X41 ) ) )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v2_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf('308',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('309',plain,
    ( ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('310',plain,
    ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      = k1_xboole_0 )
    | ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['162','177'])).

thf('311',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['169','172'])).

thf('312',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( v2_pre_topc @ X44 )
      | ~ ( l1_pre_topc @ X44 )
      | ~ ( v1_funct_2 @ X43 @ ( u1_struct_0 @ X44 ) @ ( u1_struct_0 @ X42 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X44 ) @ ( u1_struct_0 @ X42 ) ) ) )
      | ( v5_pre_topc @ X43 @ ( g1_pre_topc @ ( u1_struct_0 @ X44 ) @ ( u1_pre_topc @ X44 ) ) @ X42 )
      | ~ ( v5_pre_topc @ X43 @ X44 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X44 ) @ ( u1_pre_topc @ X44 ) ) ) @ ( u1_struct_0 @ X42 ) ) ) )
      | ~ ( v1_funct_2 @ X43 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X44 ) @ ( u1_pre_topc @ X44 ) ) ) @ ( u1_struct_0 @ X42 ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( v2_pre_topc @ X42 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('313',plain,
    ( ~ ( v2_pre_topc @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['311','312'])).

thf('314',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('315',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('316',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('317',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('318',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('319',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('320',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('321',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['313','314','315','316','317','318','319','320'])).

thf('322',plain,
    ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      = k1_xboole_0 )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 )
    | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['310','321'])).

thf('323',plain,
    ( ( ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 )
      | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
        = k1_xboole_0 ) )
   <= ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['309','322'])).

thf('324',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['98','102','255','260'])).

thf('325',plain,
    ( ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 )
    | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      = k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['323','324'])).

thf('326',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = sk_C )
   <= ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['266','267'])).

thf('327',plain,(
    ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['98','102','255','258'])).

thf('328',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['98','102','255','260'])).

thf('329',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = sk_C ),
    inference(simpl_trail,[status(thm)],['326','327','328'])).

thf('330',plain,(
    sk_C = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['92','259','261'])).

thf('331',plain,
    ( ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 )
    | ( ( u1_struct_0 @ ( g1_pre_topc @ sk_C @ ( u1_pre_topc @ sk_B_1 ) ) )
      = sk_C ) ),
    inference(demod,[status(thm)],['325','329','330'])).

thf('332',plain,
    ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      = k1_xboole_0 )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['159','160','161'])).

thf('333',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['82','91'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('334',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('335',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_partfun1 @ X32 @ X33 )
      | ( v1_funct_2 @ X32 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('336',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_partfun1 @ k1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['334','335'])).

thf('337',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_funct_1 @ sk_C )
        | ~ ( v1_partfun1 @ k1_xboole_0 @ X0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X0 @ X1 ) )
   <= ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['333','336'])).

thf('338',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('339',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['82','91'])).

thf('340',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['82','91'])).

thf('341',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_partfun1 @ sk_C @ X0 )
        | ( v1_funct_2 @ sk_C @ X0 @ X1 ) )
   <= ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['337','338','339','340'])).

thf('342',plain,
    ( ! [X0: $i] :
        ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
          = k1_xboole_0 )
        | ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ X0 ) )
   <= ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['332','341'])).

thf('343',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = sk_C )
   <= ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['266','267'])).

thf('344',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['82','91'])).

thf('345',plain,
    ( ! [X0: $i] :
        ( ( ( u1_struct_0 @ ( g1_pre_topc @ sk_C @ ( u1_pre_topc @ sk_B_1 ) ) )
          = sk_C )
        | ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ X0 ) )
   <= ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['342','343','344'])).

thf('346',plain,(
    ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['98','102','255','258'])).

thf('347',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['98','102','255','260'])).

thf('348',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ sk_C @ ( u1_pre_topc @ sk_B_1 ) ) )
        = sk_C )
      | ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['345','346','347'])).

thf('349',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = sk_C )
   <= ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['266','267'])).

thf('350',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('351',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( v2_pre_topc @ X48 )
      | ~ ( l1_pre_topc @ X48 )
      | ~ ( v1_funct_2 @ X47 @ ( u1_struct_0 @ X48 ) @ ( u1_struct_0 @ X46 ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X48 ) @ ( u1_struct_0 @ X46 ) ) ) )
      | ( v5_pre_topc @ X47 @ X48 @ ( g1_pre_topc @ ( u1_struct_0 @ X46 ) @ ( u1_pre_topc @ X46 ) ) )
      | ~ ( v5_pre_topc @ X47 @ X48 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X48 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X46 ) @ ( u1_pre_topc @ X46 ) ) ) ) ) )
      | ~ ( v1_funct_2 @ X47 @ ( u1_struct_0 @ X48 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X46 ) @ ( u1_pre_topc @ X46 ) ) ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( l1_pre_topc @ X46 )
      | ~ ( v2_pre_topc @ X46 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('352',plain,
    ( ~ ( v2_pre_topc @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) )
    | ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['350','351'])).

thf('353',plain,(
    v2_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('354',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('355',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('356',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('357',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['169','172'])).

thf('358',plain,
    ( ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['352','353','354','355','356','357'])).

thf('359',plain,
    ( ( ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ sk_C )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 ) )
   <= ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['349','358'])).

thf('360',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = sk_C )
   <= ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['266','267'])).

thf('361',plain,
    ( ( ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ sk_C )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ sk_C @ ( u1_pre_topc @ sk_B_1 ) ) )
      | ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 ) )
   <= ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['359','360'])).

thf('362',plain,(
    ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['98','102','255','258'])).

thf('363',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['98','102','255','260'])).

thf('364',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) @ sk_C )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ sk_C @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['361','362','363'])).

thf('365',plain,
    ( ( ( u1_struct_0 @ ( g1_pre_topc @ sk_C @ ( u1_pre_topc @ sk_B_1 ) ) )
      = sk_C )
    | ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B_1 )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ sk_C @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['348','364'])).

thf('366',plain,
    ( ( ( u1_struct_0 @ ( g1_pre_topc @ sk_C @ ( u1_pre_topc @ sk_B_1 ) ) )
      = sk_C )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ sk_C @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ( ( u1_struct_0 @ ( g1_pre_topc @ sk_C @ ( u1_pre_topc @ sk_B_1 ) ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['331','365'])).

thf('367',plain,
    ( ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ sk_C @ ( u1_pre_topc @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( ( u1_struct_0 @ ( g1_pre_topc @ sk_C @ ( u1_pre_topc @ sk_B_1 ) ) )
      = sk_C ) ),
    inference(simplify,[status(thm)],['366'])).

thf('368',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( g1_pre_topc @ sk_C @ ( u1_pre_topc @ sk_B_1 ) ) )
      = sk_C )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ sk_C @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['308','367'])).

thf('369',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('370',plain,
    ( ( ( u1_struct_0 @ ( g1_pre_topc @ sk_C @ ( u1_pre_topc @ sk_B_1 ) ) )
      = sk_C )
    | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ sk_C @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['368','369'])).

thf('371',plain,(
    ~ ( v5_pre_topc @ sk_C @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ sk_C @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(simpl_trail,[status(thm)],['292','293','294'])).

thf('372',plain,
    ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( ( u1_struct_0 @ ( g1_pre_topc @ sk_C @ ( u1_pre_topc @ sk_B_1 ) ) )
      = sk_C ) ),
    inference(clc,[status(thm)],['370','371'])).

thf('373',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( g1_pre_topc @ sk_C @ ( u1_pre_topc @ sk_B_1 ) ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['307','372'])).

thf('374',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('375',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('376',plain,
    ( ( u1_struct_0 @ ( g1_pre_topc @ sk_C @ ( u1_pre_topc @ sk_B_1 ) ) )
    = sk_C ),
    inference(demod,[status(thm)],['373','374','375'])).

thf('377',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = sk_C )
   <= ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['266','267'])).

thf('378',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('379',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ sk_C )
   <= ( ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) )
      & ( v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['377','378'])).

thf('380',plain,(
    ~ ( v5_pre_topc @ sk_D @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['98','102','255','258'])).

thf('381',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['98','102','255','260'])).

thf('382',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ sk_C ),
    inference(simpl_trail,[status(thm)],['379','380','381'])).

thf('383',plain,(
    $false ),
    inference(demod,[status(thm)],['306','376','382'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EcLBwAmJNg
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:10:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.66/0.93  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.66/0.93  % Solved by: fo/fo7.sh
% 0.66/0.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.66/0.93  % done 1017 iterations in 0.463s
% 0.66/0.93  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.66/0.93  % SZS output start Refutation
% 0.66/0.93  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.66/0.93  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.66/0.93  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.66/0.93  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.66/0.93  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.66/0.93  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.66/0.93  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.66/0.93  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.66/0.93  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.66/0.93  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.66/0.93  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.66/0.93  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.66/0.93  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.66/0.93  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.66/0.93  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.66/0.93  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.66/0.93  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.66/0.93  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.66/0.93  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.66/0.93  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.66/0.93  thf(sk_B_type, type, sk_B: $i > $i).
% 0.66/0.93  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.66/0.93  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.66/0.93  thf(sk_A_type, type, sk_A: $i).
% 0.66/0.93  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.66/0.93  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.66/0.93  thf(sk_D_type, type, sk_D: $i).
% 0.66/0.93  thf(sk_C_type, type, sk_C: $i).
% 0.66/0.93  thf(fc6_pre_topc, axiom,
% 0.66/0.93    (![A:$i]:
% 0.66/0.93     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.66/0.93       ( ( v1_pre_topc @
% 0.66/0.93           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.66/0.93         ( v2_pre_topc @
% 0.66/0.93           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.66/0.93  thf('0', plain,
% 0.66/0.93      (![X41 : $i]:
% 0.66/0.93         ((v2_pre_topc @ 
% 0.66/0.93           (g1_pre_topc @ (u1_struct_0 @ X41) @ (u1_pre_topc @ X41)))
% 0.66/0.93          | ~ (l1_pre_topc @ X41)
% 0.66/0.93          | ~ (v2_pre_topc @ X41))),
% 0.66/0.93      inference('cnf', [status(esa)], [fc6_pre_topc])).
% 0.66/0.93  thf(dt_u1_pre_topc, axiom,
% 0.66/0.93    (![A:$i]:
% 0.66/0.93     ( ( l1_pre_topc @ A ) =>
% 0.66/0.93       ( m1_subset_1 @
% 0.66/0.93         ( u1_pre_topc @ A ) @ 
% 0.66/0.93         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.66/0.93  thf('1', plain,
% 0.66/0.93      (![X40 : $i]:
% 0.66/0.93         ((m1_subset_1 @ (u1_pre_topc @ X40) @ 
% 0.66/0.93           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40))))
% 0.66/0.93          | ~ (l1_pre_topc @ X40))),
% 0.66/0.93      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.66/0.93  thf(dt_g1_pre_topc, axiom,
% 0.66/0.93    (![A:$i,B:$i]:
% 0.66/0.93     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.66/0.93       ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) ) & 
% 0.66/0.93         ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ))).
% 0.66/0.93  thf('2', plain,
% 0.66/0.93      (![X38 : $i, X39 : $i]:
% 0.66/0.93         ((l1_pre_topc @ (g1_pre_topc @ X38 @ X39))
% 0.66/0.93          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X38))))),
% 0.66/0.93      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 0.66/0.93  thf('3', plain,
% 0.66/0.93      (![X0 : $i]:
% 0.66/0.93         (~ (l1_pre_topc @ X0)
% 0.66/0.93          | (l1_pre_topc @ 
% 0.66/0.93             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.66/0.93      inference('sup-', [status(thm)], ['1', '2'])).
% 0.66/0.93  thf(t64_pre_topc, conjecture,
% 0.66/0.93    (![A:$i]:
% 0.66/0.93     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.66/0.93       ( ![B:$i]:
% 0.66/0.93         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.66/0.93           ( ![C:$i]:
% 0.66/0.93             ( ( ( v1_funct_1 @ C ) & 
% 0.66/0.93                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.66/0.93                 ( m1_subset_1 @
% 0.66/0.93                   C @ 
% 0.66/0.93                   ( k1_zfmisc_1 @
% 0.66/0.93                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.66/0.93               ( ![D:$i]:
% 0.66/0.93                 ( ( ( v1_funct_1 @ D ) & 
% 0.66/0.93                     ( v1_funct_2 @
% 0.66/0.93                       D @ 
% 0.66/0.93                       ( u1_struct_0 @
% 0.66/0.93                         ( g1_pre_topc @
% 0.66/0.93                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 0.66/0.93                       ( u1_struct_0 @
% 0.66/0.93                         ( g1_pre_topc @
% 0.66/0.93                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) & 
% 0.66/0.93                     ( m1_subset_1 @
% 0.66/0.93                       D @ 
% 0.66/0.93                       ( k1_zfmisc_1 @
% 0.66/0.93                         ( k2_zfmisc_1 @
% 0.66/0.93                           ( u1_struct_0 @
% 0.66/0.93                             ( g1_pre_topc @
% 0.66/0.93                               ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 0.66/0.93                           ( u1_struct_0 @
% 0.66/0.93                             ( g1_pre_topc @
% 0.66/0.93                               ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) =>
% 0.66/0.93                   ( ( ( C ) = ( D ) ) =>
% 0.66/0.93                     ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.66/0.93                       ( v5_pre_topc @
% 0.66/0.93                         D @ 
% 0.66/0.93                         ( g1_pre_topc @
% 0.66/0.93                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) @ 
% 0.66/0.93                         ( g1_pre_topc @
% 0.66/0.93                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.66/0.93  thf(zf_stmt_0, negated_conjecture,
% 0.66/0.93    (~( ![A:$i]:
% 0.66/0.93        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.66/0.93          ( ![B:$i]:
% 0.66/0.93            ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.66/0.93              ( ![C:$i]:
% 0.66/0.93                ( ( ( v1_funct_1 @ C ) & 
% 0.66/0.93                    ( v1_funct_2 @
% 0.66/0.93                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.66/0.93                    ( m1_subset_1 @
% 0.66/0.93                      C @ 
% 0.66/0.93                      ( k1_zfmisc_1 @
% 0.66/0.93                        ( k2_zfmisc_1 @
% 0.66/0.93                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.66/0.93                  ( ![D:$i]:
% 0.66/0.93                    ( ( ( v1_funct_1 @ D ) & 
% 0.66/0.93                        ( v1_funct_2 @
% 0.66/0.93                          D @ 
% 0.66/0.93                          ( u1_struct_0 @
% 0.66/0.93                            ( g1_pre_topc @
% 0.66/0.93                              ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 0.66/0.93                          ( u1_struct_0 @
% 0.66/0.93                            ( g1_pre_topc @
% 0.66/0.93                              ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) & 
% 0.66/0.93                        ( m1_subset_1 @
% 0.66/0.93                          D @ 
% 0.66/0.93                          ( k1_zfmisc_1 @
% 0.66/0.93                            ( k2_zfmisc_1 @
% 0.66/0.93                              ( u1_struct_0 @
% 0.66/0.93                                ( g1_pre_topc @
% 0.66/0.93                                  ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 0.66/0.93                              ( u1_struct_0 @
% 0.66/0.93                                ( g1_pre_topc @
% 0.66/0.93                                  ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) =>
% 0.66/0.93                      ( ( ( C ) = ( D ) ) =>
% 0.66/0.93                        ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.66/0.93                          ( v5_pre_topc @
% 0.66/0.93                            D @ 
% 0.66/0.93                            ( g1_pre_topc @
% 0.66/0.93                              ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) @ 
% 0.66/0.93                            ( g1_pre_topc @
% 0.66/0.93                              ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.66/0.93    inference('cnf.neg', [status(esa)], [t64_pre_topc])).
% 0.66/0.93  thf('4', plain,
% 0.66/0.93      (((v5_pre_topc @ sk_D @ 
% 0.66/0.93         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.66/0.93         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.66/0.93        | (v5_pre_topc @ sk_C @ sk_A @ sk_B_1))),
% 0.66/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.93  thf('5', plain,
% 0.66/0.93      (((v5_pre_topc @ sk_C @ sk_A @ sk_B_1))
% 0.66/0.93         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.66/0.93      inference('split', [status(esa)], ['4'])).
% 0.66/0.93  thf('6', plain,
% 0.66/0.93      ((m1_subset_1 @ sk_C @ 
% 0.66/0.93        (k1_zfmisc_1 @ 
% 0.66/0.93         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.66/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.93  thf(t132_funct_2, axiom,
% 0.66/0.93    (![A:$i,B:$i,C:$i]:
% 0.66/0.93     ( ( ( v1_funct_1 @ C ) & 
% 0.66/0.93         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.66/0.93       ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.66/0.93           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.66/0.93         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.66/0.93           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.66/0.93  thf('7', plain,
% 0.66/0.93      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.66/0.93         (((X35) = (k1_xboole_0))
% 0.66/0.93          | ~ (v1_funct_1 @ X36)
% 0.66/0.93          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X35)))
% 0.66/0.93          | (v1_partfun1 @ X36 @ X37)
% 0.66/0.93          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X35)))
% 0.66/0.93          | ~ (v1_funct_2 @ X36 @ X37 @ X35)
% 0.66/0.93          | ~ (v1_funct_1 @ X36))),
% 0.66/0.93      inference('cnf', [status(esa)], [t132_funct_2])).
% 0.66/0.93  thf('8', plain,
% 0.66/0.93      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.66/0.93         (~ (v1_funct_2 @ X36 @ X37 @ X35)
% 0.66/0.93          | (v1_partfun1 @ X36 @ X37)
% 0.66/0.93          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X35)))
% 0.66/0.93          | ~ (v1_funct_1 @ X36)
% 0.66/0.93          | ((X35) = (k1_xboole_0)))),
% 0.66/0.93      inference('simplify', [status(thm)], ['7'])).
% 0.66/0.93  thf('9', plain,
% 0.66/0.93      ((((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 0.66/0.93        | ~ (v1_funct_1 @ sk_C)
% 0.66/0.93        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.66/0.93        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1)))),
% 0.66/0.93      inference('sup-', [status(thm)], ['6', '8'])).
% 0.66/0.93  thf('10', plain, ((v1_funct_1 @ sk_C)),
% 0.66/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.93  thf('11', plain,
% 0.66/0.93      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 0.66/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.93  thf('12', plain,
% 0.66/0.93      ((((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 0.66/0.93        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.66/0.93      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.66/0.93  thf('13', plain,
% 0.66/0.93      ((m1_subset_1 @ sk_D @ 
% 0.66/0.93        (k1_zfmisc_1 @ 
% 0.66/0.93         (k2_zfmisc_1 @ 
% 0.66/0.93          (u1_struct_0 @ 
% 0.66/0.93           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.66/0.93          (u1_struct_0 @ 
% 0.66/0.93           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))),
% 0.66/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.93  thf('14', plain, (((sk_C) = (sk_D))),
% 0.66/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.93  thf('15', plain,
% 0.66/0.93      ((m1_subset_1 @ sk_C @ 
% 0.66/0.93        (k1_zfmisc_1 @ 
% 0.66/0.93         (k2_zfmisc_1 @ 
% 0.66/0.93          (u1_struct_0 @ 
% 0.66/0.93           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.66/0.93          (u1_struct_0 @ 
% 0.66/0.93           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))),
% 0.66/0.93      inference('demod', [status(thm)], ['13', '14'])).
% 0.66/0.93  thf(cc2_relset_1, axiom,
% 0.66/0.93    (![A:$i,B:$i,C:$i]:
% 0.66/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.66/0.93       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.66/0.93  thf('16', plain,
% 0.66/0.93      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.66/0.93         ((v5_relat_1 @ X17 @ X19)
% 0.66/0.93          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.66/0.93      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.66/0.93  thf('17', plain,
% 0.66/0.93      ((v5_relat_1 @ sk_C @ 
% 0.66/0.93        (u1_struct_0 @ 
% 0.66/0.93         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 0.66/0.93      inference('sup-', [status(thm)], ['15', '16'])).
% 0.66/0.93  thf(d19_relat_1, axiom,
% 0.66/0.93    (![A:$i,B:$i]:
% 0.66/0.93     ( ( v1_relat_1 @ B ) =>
% 0.66/0.93       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.66/0.93  thf('18', plain,
% 0.66/0.93      (![X12 : $i, X13 : $i]:
% 0.66/0.93         (~ (v5_relat_1 @ X12 @ X13)
% 0.66/0.93          | (r1_tarski @ (k2_relat_1 @ X12) @ X13)
% 0.66/0.93          | ~ (v1_relat_1 @ X12))),
% 0.66/0.93      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.66/0.93  thf('19', plain,
% 0.66/0.93      ((~ (v1_relat_1 @ sk_C)
% 0.66/0.93        | (r1_tarski @ (k2_relat_1 @ sk_C) @ 
% 0.66/0.93           (u1_struct_0 @ 
% 0.66/0.93            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.66/0.93      inference('sup-', [status(thm)], ['17', '18'])).
% 0.66/0.93  thf('20', plain,
% 0.66/0.93      ((m1_subset_1 @ sk_C @ 
% 0.66/0.93        (k1_zfmisc_1 @ 
% 0.66/0.93         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.66/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.93  thf(cc1_relset_1, axiom,
% 0.66/0.93    (![A:$i,B:$i,C:$i]:
% 0.66/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.66/0.93       ( v1_relat_1 @ C ) ))).
% 0.66/0.93  thf('21', plain,
% 0.66/0.93      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.66/0.93         ((v1_relat_1 @ X14)
% 0.66/0.93          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.66/0.93      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.66/0.93  thf('22', plain, ((v1_relat_1 @ sk_C)),
% 0.66/0.93      inference('sup-', [status(thm)], ['20', '21'])).
% 0.66/0.93  thf('23', plain,
% 0.66/0.93      ((r1_tarski @ (k2_relat_1 @ sk_C) @ 
% 0.66/0.93        (u1_struct_0 @ 
% 0.66/0.93         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 0.66/0.93      inference('demod', [status(thm)], ['19', '22'])).
% 0.66/0.93  thf('24', plain,
% 0.66/0.93      ((m1_subset_1 @ sk_C @ 
% 0.66/0.93        (k1_zfmisc_1 @ 
% 0.66/0.93         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.66/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.93  thf(t14_relset_1, axiom,
% 0.66/0.93    (![A:$i,B:$i,C:$i,D:$i]:
% 0.66/0.93     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.66/0.93       ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B ) =>
% 0.66/0.93         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ))).
% 0.66/0.93  thf('25', plain,
% 0.66/0.93      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.66/0.93         (~ (r1_tarski @ (k2_relat_1 @ X24) @ X25)
% 0.66/0.93          | (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 0.66/0.93          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.66/0.93      inference('cnf', [status(esa)], [t14_relset_1])).
% 0.66/0.93  thf('26', plain,
% 0.66/0.93      (![X0 : $i]:
% 0.66/0.93         ((m1_subset_1 @ sk_C @ 
% 0.66/0.93           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ X0)))
% 0.66/0.93          | ~ (r1_tarski @ (k2_relat_1 @ sk_C) @ X0))),
% 0.66/0.93      inference('sup-', [status(thm)], ['24', '25'])).
% 0.66/0.93  thf('27', plain,
% 0.66/0.93      ((m1_subset_1 @ sk_C @ 
% 0.66/0.93        (k1_zfmisc_1 @ 
% 0.66/0.93         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.93          (u1_struct_0 @ 
% 0.66/0.93           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))),
% 0.66/0.93      inference('sup-', [status(thm)], ['23', '26'])).
% 0.66/0.93  thf(cc1_funct_2, axiom,
% 0.66/0.93    (![A:$i,B:$i,C:$i]:
% 0.66/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.66/0.93       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 0.66/0.93         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 0.66/0.93  thf('28', plain,
% 0.66/0.93      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.66/0.93         (~ (v1_funct_1 @ X32)
% 0.66/0.93          | ~ (v1_partfun1 @ X32 @ X33)
% 0.66/0.93          | (v1_funct_2 @ X32 @ X33 @ X34)
% 0.66/0.93          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.66/0.93      inference('cnf', [status(esa)], [cc1_funct_2])).
% 0.66/0.93  thf('29', plain,
% 0.66/0.93      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.93         (u1_struct_0 @ 
% 0.66/0.93          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 0.66/0.93        | ~ (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.66/0.93        | ~ (v1_funct_1 @ sk_C))),
% 0.66/0.93      inference('sup-', [status(thm)], ['27', '28'])).
% 0.66/0.93  thf('30', plain, ((v1_funct_1 @ sk_C)),
% 0.66/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.93  thf('31', plain,
% 0.66/0.93      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.93         (u1_struct_0 @ 
% 0.66/0.93          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 0.66/0.93        | ~ (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.66/0.93      inference('demod', [status(thm)], ['29', '30'])).
% 0.66/0.93  thf('32', plain,
% 0.66/0.93      ((((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 0.66/0.93        | (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.93           (u1_struct_0 @ 
% 0.66/0.93            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.66/0.93      inference('sup-', [status(thm)], ['12', '31'])).
% 0.66/0.93  thf('33', plain,
% 0.66/0.93      ((m1_subset_1 @ sk_C @ 
% 0.66/0.93        (k1_zfmisc_1 @ 
% 0.66/0.93         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.66/0.93          (u1_struct_0 @ 
% 0.66/0.93           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))),
% 0.66/0.93      inference('sup-', [status(thm)], ['23', '26'])).
% 0.66/0.93  thf(t63_pre_topc, axiom,
% 0.66/0.93    (![A:$i]:
% 0.66/0.93     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.66/0.93       ( ![B:$i]:
% 0.66/0.93         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.66/0.93           ( ![C:$i]:
% 0.66/0.93             ( ( ( v1_funct_1 @ C ) & 
% 0.66/0.93                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.66/0.93                 ( m1_subset_1 @
% 0.66/0.93                   C @ 
% 0.66/0.93                   ( k1_zfmisc_1 @
% 0.66/0.93                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.66/0.93               ( ![D:$i]:
% 0.66/0.93                 ( ( ( v1_funct_1 @ D ) & 
% 0.66/0.93                     ( v1_funct_2 @
% 0.66/0.93                       D @ ( u1_struct_0 @ A ) @ 
% 0.66/0.93                       ( u1_struct_0 @
% 0.66/0.93                         ( g1_pre_topc @
% 0.66/0.93                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) & 
% 0.66/0.93                     ( m1_subset_1 @
% 0.66/0.93                       D @ 
% 0.66/0.93                       ( k1_zfmisc_1 @
% 0.66/0.93                         ( k2_zfmisc_1 @
% 0.66/0.93                           ( u1_struct_0 @ A ) @ 
% 0.77/0.93                           ( u1_struct_0 @
% 0.77/0.93                             ( g1_pre_topc @
% 0.77/0.93                               ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) =>
% 0.77/0.93                   ( ( ( C ) = ( D ) ) =>
% 0.77/0.93                     ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.77/0.93                       ( v5_pre_topc @
% 0.77/0.93                         D @ A @ 
% 0.77/0.93                         ( g1_pre_topc @
% 0.77/0.93                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.77/0.93  thf('34', plain,
% 0.77/0.93      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.77/0.93         (~ (v2_pre_topc @ X46)
% 0.77/0.93          | ~ (l1_pre_topc @ X46)
% 0.77/0.93          | ~ (v1_funct_1 @ X47)
% 0.77/0.93          | ~ (v1_funct_2 @ X47 @ (u1_struct_0 @ X48) @ 
% 0.77/0.93               (u1_struct_0 @ 
% 0.77/0.93                (g1_pre_topc @ (u1_struct_0 @ X46) @ (u1_pre_topc @ X46))))
% 0.77/0.93          | ~ (m1_subset_1 @ X47 @ 
% 0.77/0.93               (k1_zfmisc_1 @ 
% 0.77/0.93                (k2_zfmisc_1 @ (u1_struct_0 @ X48) @ 
% 0.77/0.93                 (u1_struct_0 @ 
% 0.77/0.93                  (g1_pre_topc @ (u1_struct_0 @ X46) @ (u1_pre_topc @ X46))))))
% 0.77/0.93          | ~ (v5_pre_topc @ X49 @ X48 @ X46)
% 0.77/0.93          | (v5_pre_topc @ X47 @ X48 @ 
% 0.77/0.93             (g1_pre_topc @ (u1_struct_0 @ X46) @ (u1_pre_topc @ X46)))
% 0.77/0.93          | ((X49) != (X47))
% 0.77/0.93          | ~ (m1_subset_1 @ X49 @ 
% 0.77/0.93               (k1_zfmisc_1 @ 
% 0.77/0.93                (k2_zfmisc_1 @ (u1_struct_0 @ X48) @ (u1_struct_0 @ X46))))
% 0.77/0.93          | ~ (v1_funct_2 @ X49 @ (u1_struct_0 @ X48) @ (u1_struct_0 @ X46))
% 0.77/0.93          | ~ (v1_funct_1 @ X49)
% 0.77/0.93          | ~ (l1_pre_topc @ X48)
% 0.77/0.93          | ~ (v2_pre_topc @ X48))),
% 0.77/0.93      inference('cnf', [status(esa)], [t63_pre_topc])).
% 0.77/0.93  thf('35', plain,
% 0.77/0.93      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.77/0.93         (~ (v2_pre_topc @ X48)
% 0.77/0.93          | ~ (l1_pre_topc @ X48)
% 0.77/0.93          | ~ (v1_funct_2 @ X47 @ (u1_struct_0 @ X48) @ (u1_struct_0 @ X46))
% 0.77/0.93          | ~ (m1_subset_1 @ X47 @ 
% 0.77/0.93               (k1_zfmisc_1 @ 
% 0.77/0.93                (k2_zfmisc_1 @ (u1_struct_0 @ X48) @ (u1_struct_0 @ X46))))
% 0.77/0.93          | (v5_pre_topc @ X47 @ X48 @ 
% 0.77/0.93             (g1_pre_topc @ (u1_struct_0 @ X46) @ (u1_pre_topc @ X46)))
% 0.77/0.93          | ~ (v5_pre_topc @ X47 @ X48 @ X46)
% 0.77/0.93          | ~ (m1_subset_1 @ X47 @ 
% 0.77/0.93               (k1_zfmisc_1 @ 
% 0.77/0.93                (k2_zfmisc_1 @ (u1_struct_0 @ X48) @ 
% 0.77/0.93                 (u1_struct_0 @ 
% 0.77/0.93                  (g1_pre_topc @ (u1_struct_0 @ X46) @ (u1_pre_topc @ X46))))))
% 0.77/0.93          | ~ (v1_funct_2 @ X47 @ (u1_struct_0 @ X48) @ 
% 0.77/0.93               (u1_struct_0 @ 
% 0.77/0.93                (g1_pre_topc @ (u1_struct_0 @ X46) @ (u1_pre_topc @ X46))))
% 0.77/0.93          | ~ (v1_funct_1 @ X47)
% 0.77/0.93          | ~ (l1_pre_topc @ X46)
% 0.77/0.93          | ~ (v2_pre_topc @ X46))),
% 0.77/0.93      inference('simplify', [status(thm)], ['34'])).
% 0.77/0.93  thf('36', plain,
% 0.77/0.93      ((~ (v2_pre_topc @ sk_B_1)
% 0.77/0.93        | ~ (l1_pre_topc @ sk_B_1)
% 0.77/0.93        | ~ (v1_funct_1 @ sk_C)
% 0.77/0.93        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.93             (u1_struct_0 @ 
% 0.77/0.93              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 0.77/0.93        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B_1)
% 0.77/0.93        | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.77/0.93           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.93        | ~ (m1_subset_1 @ sk_C @ 
% 0.77/0.93             (k1_zfmisc_1 @ 
% 0.77/0.93              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))
% 0.77/0.93        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))
% 0.77/0.93        | ~ (l1_pre_topc @ sk_A)
% 0.77/0.93        | ~ (v2_pre_topc @ sk_A))),
% 0.77/0.93      inference('sup-', [status(thm)], ['33', '35'])).
% 0.77/0.93  thf('37', plain, ((v2_pre_topc @ sk_B_1)),
% 0.77/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.93  thf('38', plain, ((l1_pre_topc @ sk_B_1)),
% 0.77/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.93  thf('39', plain, ((v1_funct_1 @ sk_C)),
% 0.77/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.93  thf('40', plain,
% 0.77/0.93      ((m1_subset_1 @ sk_C @ 
% 0.77/0.93        (k1_zfmisc_1 @ 
% 0.77/0.93         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.77/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.93  thf('41', plain,
% 0.77/0.93      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 0.77/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.93  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.77/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.93  thf('43', plain, ((v2_pre_topc @ sk_A)),
% 0.77/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.93  thf('44', plain,
% 0.77/0.93      ((~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.93           (u1_struct_0 @ 
% 0.77/0.93            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 0.77/0.93        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B_1)
% 0.77/0.93        | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.77/0.93           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 0.77/0.93      inference('demod', [status(thm)],
% 0.77/0.93                ['36', '37', '38', '39', '40', '41', '42', '43'])).
% 0.77/0.93  thf('45', plain,
% 0.77/0.93      ((((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 0.77/0.93        | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.77/0.93           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.93        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B_1))),
% 0.77/0.93      inference('sup-', [status(thm)], ['32', '44'])).
% 0.77/0.93  thf('46', plain,
% 0.77/0.93      ((((v5_pre_topc @ sk_C @ sk_A @ 
% 0.77/0.93          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.93         | ((u1_struct_0 @ sk_B_1) = (k1_xboole_0))))
% 0.77/0.93         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.93      inference('sup-', [status(thm)], ['5', '45'])).
% 0.77/0.93  thf('47', plain,
% 0.77/0.93      ((((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 0.77/0.93        | (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.93           (u1_struct_0 @ 
% 0.77/0.93            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.93      inference('sup-', [status(thm)], ['12', '31'])).
% 0.77/0.93  thf('48', plain,
% 0.77/0.93      ((m1_subset_1 @ sk_C @ 
% 0.77/0.93        (k1_zfmisc_1 @ 
% 0.77/0.93         (k2_zfmisc_1 @ 
% 0.77/0.93          (u1_struct_0 @ 
% 0.77/0.93           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.77/0.93          (u1_struct_0 @ 
% 0.77/0.93           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))),
% 0.77/0.93      inference('demod', [status(thm)], ['13', '14'])).
% 0.77/0.93  thf(t62_pre_topc, axiom,
% 0.77/0.93    (![A:$i]:
% 0.77/0.93     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.77/0.93       ( ![B:$i]:
% 0.77/0.93         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.77/0.93           ( ![C:$i]:
% 0.77/0.93             ( ( ( v1_funct_1 @ C ) & 
% 0.77/0.93                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.77/0.93                 ( m1_subset_1 @
% 0.77/0.93                   C @ 
% 0.77/0.93                   ( k1_zfmisc_1 @
% 0.77/0.93                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.77/0.93               ( ![D:$i]:
% 0.77/0.93                 ( ( ( v1_funct_1 @ D ) & 
% 0.77/0.93                     ( v1_funct_2 @
% 0.77/0.93                       D @ 
% 0.77/0.93                       ( u1_struct_0 @
% 0.77/0.93                         ( g1_pre_topc @
% 0.77/0.93                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 0.77/0.93                       ( u1_struct_0 @ B ) ) & 
% 0.77/0.93                     ( m1_subset_1 @
% 0.77/0.93                       D @ 
% 0.77/0.93                       ( k1_zfmisc_1 @
% 0.77/0.93                         ( k2_zfmisc_1 @
% 0.77/0.93                           ( u1_struct_0 @
% 0.77/0.93                             ( g1_pre_topc @
% 0.77/0.93                               ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) @ 
% 0.77/0.93                           ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.77/0.93                   ( ( ( C ) = ( D ) ) =>
% 0.77/0.93                     ( ( v5_pre_topc @ C @ A @ B ) <=>
% 0.77/0.93                       ( v5_pre_topc @
% 0.77/0.93                         D @ 
% 0.77/0.93                         ( g1_pre_topc @
% 0.77/0.93                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) @ 
% 0.77/0.93                         B ) ) ) ) ) ) ) ) ) ))).
% 0.77/0.93  thf('49', plain,
% 0.77/0.93      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.77/0.93         (~ (v2_pre_topc @ X42)
% 0.77/0.93          | ~ (l1_pre_topc @ X42)
% 0.77/0.93          | ~ (v1_funct_1 @ X43)
% 0.77/0.93          | ~ (v1_funct_2 @ X43 @ 
% 0.77/0.93               (u1_struct_0 @ 
% 0.77/0.93                (g1_pre_topc @ (u1_struct_0 @ X44) @ (u1_pre_topc @ X44))) @ 
% 0.77/0.93               (u1_struct_0 @ X42))
% 0.77/0.93          | ~ (m1_subset_1 @ X43 @ 
% 0.77/0.93               (k1_zfmisc_1 @ 
% 0.77/0.93                (k2_zfmisc_1 @ 
% 0.77/0.93                 (u1_struct_0 @ 
% 0.77/0.93                  (g1_pre_topc @ (u1_struct_0 @ X44) @ (u1_pre_topc @ X44))) @ 
% 0.77/0.93                 (u1_struct_0 @ X42))))
% 0.77/0.93          | ~ (v5_pre_topc @ X45 @ X44 @ X42)
% 0.77/0.93          | (v5_pre_topc @ X43 @ 
% 0.77/0.93             (g1_pre_topc @ (u1_struct_0 @ X44) @ (u1_pre_topc @ X44)) @ X42)
% 0.77/0.93          | ((X45) != (X43))
% 0.77/0.93          | ~ (m1_subset_1 @ X45 @ 
% 0.77/0.93               (k1_zfmisc_1 @ 
% 0.77/0.93                (k2_zfmisc_1 @ (u1_struct_0 @ X44) @ (u1_struct_0 @ X42))))
% 0.77/0.93          | ~ (v1_funct_2 @ X45 @ (u1_struct_0 @ X44) @ (u1_struct_0 @ X42))
% 0.77/0.93          | ~ (v1_funct_1 @ X45)
% 0.77/0.93          | ~ (l1_pre_topc @ X44)
% 0.77/0.93          | ~ (v2_pre_topc @ X44))),
% 0.77/0.93      inference('cnf', [status(esa)], [t62_pre_topc])).
% 0.77/0.93  thf('50', plain,
% 0.77/0.93      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.77/0.93         (~ (v2_pre_topc @ X44)
% 0.77/0.93          | ~ (l1_pre_topc @ X44)
% 0.77/0.93          | ~ (v1_funct_2 @ X43 @ (u1_struct_0 @ X44) @ (u1_struct_0 @ X42))
% 0.77/0.93          | ~ (m1_subset_1 @ X43 @ 
% 0.77/0.93               (k1_zfmisc_1 @ 
% 0.77/0.93                (k2_zfmisc_1 @ (u1_struct_0 @ X44) @ (u1_struct_0 @ X42))))
% 0.77/0.93          | (v5_pre_topc @ X43 @ 
% 0.77/0.93             (g1_pre_topc @ (u1_struct_0 @ X44) @ (u1_pre_topc @ X44)) @ X42)
% 0.77/0.93          | ~ (v5_pre_topc @ X43 @ X44 @ X42)
% 0.77/0.93          | ~ (m1_subset_1 @ X43 @ 
% 0.77/0.93               (k1_zfmisc_1 @ 
% 0.77/0.93                (k2_zfmisc_1 @ 
% 0.77/0.93                 (u1_struct_0 @ 
% 0.77/0.93                  (g1_pre_topc @ (u1_struct_0 @ X44) @ (u1_pre_topc @ X44))) @ 
% 0.77/0.93                 (u1_struct_0 @ X42))))
% 0.77/0.93          | ~ (v1_funct_2 @ X43 @ 
% 0.77/0.93               (u1_struct_0 @ 
% 0.77/0.93                (g1_pre_topc @ (u1_struct_0 @ X44) @ (u1_pre_topc @ X44))) @ 
% 0.77/0.93               (u1_struct_0 @ X42))
% 0.77/0.93          | ~ (v1_funct_1 @ X43)
% 0.77/0.93          | ~ (l1_pre_topc @ X42)
% 0.77/0.93          | ~ (v2_pre_topc @ X42))),
% 0.77/0.93      inference('simplify', [status(thm)], ['49'])).
% 0.77/0.93  thf('51', plain,
% 0.77/0.93      ((~ (v2_pre_topc @ 
% 0.77/0.93           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.93        | ~ (l1_pre_topc @ 
% 0.77/0.93             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.93        | ~ (v1_funct_1 @ sk_C)
% 0.77/0.93        | ~ (v1_funct_2 @ sk_C @ 
% 0.77/0.93             (u1_struct_0 @ 
% 0.77/0.93              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.77/0.93             (u1_struct_0 @ 
% 0.77/0.93              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 0.77/0.93        | ~ (v5_pre_topc @ sk_C @ sk_A @ 
% 0.77/0.93             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.93        | (v5_pre_topc @ sk_C @ 
% 0.77/0.93           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.93           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.93        | ~ (m1_subset_1 @ sk_C @ 
% 0.77/0.93             (k1_zfmisc_1 @ 
% 0.77/0.93              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.94               (u1_struct_0 @ 
% 0.77/0.94                (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))
% 0.77/0.94        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.94             (u1_struct_0 @ 
% 0.77/0.94              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 0.77/0.94        | ~ (l1_pre_topc @ sk_A)
% 0.77/0.94        | ~ (v2_pre_topc @ sk_A))),
% 0.77/0.94      inference('sup-', [status(thm)], ['48', '50'])).
% 0.77/0.94  thf('52', plain, ((v1_funct_1 @ sk_C)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('53', plain,
% 0.77/0.94      ((v1_funct_2 @ sk_D @ 
% 0.77/0.94        (u1_struct_0 @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.77/0.94        (u1_struct_0 @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('54', plain, (((sk_C) = (sk_D))),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('55', plain,
% 0.77/0.94      ((v1_funct_2 @ sk_C @ 
% 0.77/0.94        (u1_struct_0 @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.77/0.94        (u1_struct_0 @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 0.77/0.94      inference('demod', [status(thm)], ['53', '54'])).
% 0.77/0.94  thf('56', plain,
% 0.77/0.94      ((m1_subset_1 @ sk_C @ 
% 0.77/0.94        (k1_zfmisc_1 @ 
% 0.77/0.94         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.94          (u1_struct_0 @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['23', '26'])).
% 0.77/0.94  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('58', plain, ((v2_pre_topc @ sk_A)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('59', plain,
% 0.77/0.94      ((~ (v2_pre_topc @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94        | ~ (l1_pre_topc @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94        | ~ (v5_pre_topc @ sk_C @ sk_A @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94        | (v5_pre_topc @ sk_C @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.94             (u1_struct_0 @ 
% 0.77/0.94              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('demod', [status(thm)], ['51', '52', '55', '56', '57', '58'])).
% 0.77/0.94  thf('60', plain,
% 0.77/0.94      ((((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 0.77/0.94        | (v5_pre_topc @ sk_C @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94        | ~ (v5_pre_topc @ sk_C @ sk_A @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94        | ~ (l1_pre_topc @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94        | ~ (v2_pre_topc @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['47', '59'])).
% 0.77/0.94  thf('61', plain,
% 0.77/0.94      (((((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 0.77/0.94         | ~ (v2_pre_topc @ 
% 0.77/0.94              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94         | ~ (l1_pre_topc @ 
% 0.77/0.94              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94         | (v5_pre_topc @ sk_C @ 
% 0.77/0.94            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94         | ((u1_struct_0 @ sk_B_1) = (k1_xboole_0))))
% 0.77/0.94         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('sup-', [status(thm)], ['46', '60'])).
% 0.77/0.94  thf('62', plain,
% 0.77/0.94      ((((v5_pre_topc @ sk_C @ 
% 0.77/0.94          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94         | ~ (l1_pre_topc @ 
% 0.77/0.94              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94         | ~ (v2_pre_topc @ 
% 0.77/0.94              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94         | ((u1_struct_0 @ sk_B_1) = (k1_xboole_0))))
% 0.77/0.94         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('simplify', [status(thm)], ['61'])).
% 0.77/0.94  thf('63', plain,
% 0.77/0.94      (((~ (l1_pre_topc @ sk_B_1)
% 0.77/0.94         | ((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 0.77/0.94         | ~ (v2_pre_topc @ 
% 0.77/0.94              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94         | (v5_pre_topc @ sk_C @ 
% 0.77/0.94            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))
% 0.77/0.94         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('sup-', [status(thm)], ['3', '62'])).
% 0.77/0.94  thf('64', plain, ((l1_pre_topc @ sk_B_1)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('65', plain,
% 0.77/0.94      (((((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 0.77/0.94         | ~ (v2_pre_topc @ 
% 0.77/0.94              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94         | (v5_pre_topc @ sk_C @ 
% 0.77/0.94            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))
% 0.77/0.94         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('demod', [status(thm)], ['63', '64'])).
% 0.77/0.94  thf('66', plain,
% 0.77/0.94      (((~ (v2_pre_topc @ sk_B_1)
% 0.77/0.94         | ~ (l1_pre_topc @ sk_B_1)
% 0.77/0.94         | (v5_pre_topc @ sk_C @ 
% 0.77/0.94            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94         | ((u1_struct_0 @ sk_B_1) = (k1_xboole_0))))
% 0.77/0.94         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('sup-', [status(thm)], ['0', '65'])).
% 0.77/0.94  thf('67', plain, ((v2_pre_topc @ sk_B_1)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('68', plain, ((l1_pre_topc @ sk_B_1)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('69', plain,
% 0.77/0.94      ((((v5_pre_topc @ sk_C @ 
% 0.77/0.94          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94         | ((u1_struct_0 @ sk_B_1) = (k1_xboole_0))))
% 0.77/0.94         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.77/0.94  thf('70', plain,
% 0.77/0.94      ((~ (v5_pre_topc @ sk_D @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B_1))),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('71', plain,
% 0.77/0.94      ((~ (v5_pre_topc @ sk_D @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 0.77/0.94         <= (~
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('split', [status(esa)], ['70'])).
% 0.77/0.94  thf('72', plain, (((sk_C) = (sk_D))),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('73', plain,
% 0.77/0.94      ((~ (v5_pre_topc @ sk_C @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 0.77/0.94         <= (~
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('demod', [status(thm)], ['71', '72'])).
% 0.77/0.94  thf('74', plain,
% 0.77/0.94      ((((u1_struct_0 @ sk_B_1) = (k1_xboole_0)))
% 0.77/0.94         <= (~
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) & 
% 0.77/0.94             ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('sup-', [status(thm)], ['69', '73'])).
% 0.77/0.94  thf('75', plain,
% 0.77/0.94      ((~ (v2_pre_topc @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94        | ~ (l1_pre_topc @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94        | ~ (v5_pre_topc @ sk_C @ sk_A @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94        | (v5_pre_topc @ sk_C @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.94             (u1_struct_0 @ 
% 0.77/0.94              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('demod', [status(thm)], ['51', '52', '55', '56', '57', '58'])).
% 0.77/0.94  thf('76', plain,
% 0.77/0.94      (((~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.94            (u1_struct_0 @ (g1_pre_topc @ k1_xboole_0 @ (u1_pre_topc @ sk_B_1))))
% 0.77/0.94         | (v5_pre_topc @ sk_C @ 
% 0.77/0.94            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94         | ~ (v5_pre_topc @ sk_C @ sk_A @ 
% 0.77/0.94              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94         | ~ (l1_pre_topc @ 
% 0.77/0.94              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94         | ~ (v2_pre_topc @ 
% 0.77/0.94              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))
% 0.77/0.94         <= (~
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) & 
% 0.77/0.94             ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('sup-', [status(thm)], ['74', '75'])).
% 0.77/0.94  thf('77', plain,
% 0.77/0.94      ((((u1_struct_0 @ sk_B_1) = (k1_xboole_0)))
% 0.77/0.94         <= (~
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) & 
% 0.77/0.94             ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('sup-', [status(thm)], ['69', '73'])).
% 0.77/0.94  thf('78', plain,
% 0.77/0.94      ((((u1_struct_0 @ sk_B_1) = (k1_xboole_0)))
% 0.77/0.94         <= (~
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) & 
% 0.77/0.94             ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('sup-', [status(thm)], ['69', '73'])).
% 0.77/0.94  thf('79', plain,
% 0.77/0.94      ((((u1_struct_0 @ sk_B_1) = (k1_xboole_0)))
% 0.77/0.94         <= (~
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) & 
% 0.77/0.94             ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('sup-', [status(thm)], ['69', '73'])).
% 0.77/0.94  thf('80', plain,
% 0.77/0.94      ((((u1_struct_0 @ sk_B_1) = (k1_xboole_0)))
% 0.77/0.94         <= (~
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) & 
% 0.77/0.94             ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('sup-', [status(thm)], ['69', '73'])).
% 0.77/0.94  thf('81', plain,
% 0.77/0.94      (((~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.94            (u1_struct_0 @ (g1_pre_topc @ k1_xboole_0 @ (u1_pre_topc @ sk_B_1))))
% 0.77/0.94         | (v5_pre_topc @ sk_C @ 
% 0.77/0.94            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94            (g1_pre_topc @ k1_xboole_0 @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94         | ~ (v5_pre_topc @ sk_C @ sk_A @ 
% 0.77/0.94              (g1_pre_topc @ k1_xboole_0 @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94         | ~ (l1_pre_topc @ 
% 0.77/0.94              (g1_pre_topc @ k1_xboole_0 @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94         | ~ (v2_pre_topc @ 
% 0.77/0.94              (g1_pre_topc @ k1_xboole_0 @ (u1_pre_topc @ sk_B_1)))))
% 0.77/0.94         <= (~
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) & 
% 0.77/0.94             ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('demod', [status(thm)], ['76', '77', '78', '79', '80'])).
% 0.77/0.94  thf(t29_mcart_1, axiom,
% 0.77/0.94    (![A:$i]:
% 0.77/0.94     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.77/0.94          ( ![B:$i]:
% 0.77/0.94            ( ~( ( r2_hidden @ B @ A ) & 
% 0.77/0.94                 ( ![C:$i,D:$i,E:$i]:
% 0.77/0.94                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.77/0.94                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 0.77/0.94  thf('82', plain,
% 0.77/0.94      (![X28 : $i]:
% 0.77/0.94         (((X28) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X28) @ X28))),
% 0.77/0.94      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.77/0.94  thf('83', plain,
% 0.77/0.94      ((((u1_struct_0 @ sk_B_1) = (k1_xboole_0)))
% 0.77/0.94         <= (~
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) & 
% 0.77/0.94             ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('sup-', [status(thm)], ['69', '73'])).
% 0.77/0.94  thf('84', plain,
% 0.77/0.94      ((m1_subset_1 @ sk_C @ 
% 0.77/0.94        (k1_zfmisc_1 @ 
% 0.77/0.94         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf(t5_subset, axiom,
% 0.77/0.94    (![A:$i,B:$i,C:$i]:
% 0.77/0.94     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.77/0.94          ( v1_xboole_0 @ C ) ) ))).
% 0.77/0.94  thf('85', plain,
% 0.77/0.94      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.77/0.94         (~ (r2_hidden @ X7 @ X8)
% 0.77/0.94          | ~ (v1_xboole_0 @ X9)
% 0.77/0.94          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.77/0.94      inference('cnf', [status(esa)], [t5_subset])).
% 0.77/0.94  thf('86', plain,
% 0.77/0.94      (![X0 : $i]:
% 0.77/0.94         (~ (v1_xboole_0 @ 
% 0.77/0.94             (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1)))
% 0.77/0.94          | ~ (r2_hidden @ X0 @ sk_C))),
% 0.77/0.94      inference('sup-', [status(thm)], ['84', '85'])).
% 0.77/0.94  thf('87', plain,
% 0.77/0.94      ((![X0 : $i]:
% 0.77/0.94          (~ (v1_xboole_0 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0))
% 0.77/0.94           | ~ (r2_hidden @ X0 @ sk_C)))
% 0.77/0.94         <= (~
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) & 
% 0.77/0.94             ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('sup-', [status(thm)], ['83', '86'])).
% 0.77/0.94  thf(t113_zfmisc_1, axiom,
% 0.77/0.94    (![A:$i,B:$i]:
% 0.77/0.94     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.77/0.94       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.77/0.94  thf('88', plain,
% 0.77/0.94      (![X1 : $i, X2 : $i]:
% 0.77/0.94         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.77/0.94      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.77/0.94  thf('89', plain,
% 0.77/0.94      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.77/0.94      inference('simplify', [status(thm)], ['88'])).
% 0.77/0.94  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.77/0.94  thf('90', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.77/0.94      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.77/0.94  thf('91', plain,
% 0.77/0.94      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C))
% 0.77/0.94         <= (~
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) & 
% 0.77/0.94             ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('demod', [status(thm)], ['87', '89', '90'])).
% 0.77/0.94  thf('92', plain,
% 0.77/0.94      ((((sk_C) = (k1_xboole_0)))
% 0.77/0.94         <= (~
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) & 
% 0.77/0.94             ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('sup-', [status(thm)], ['82', '91'])).
% 0.77/0.94  thf('93', plain,
% 0.77/0.94      (((v5_pre_topc @ sk_D @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94        | (v5_pre_topc @ sk_C @ sk_A @ sk_B_1))),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('94', plain, (((sk_C) = (sk_D))),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('95', plain,
% 0.77/0.94      (((v5_pre_topc @ sk_C @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94        | (v5_pre_topc @ sk_C @ sk_A @ sk_B_1))),
% 0.77/0.94      inference('demod', [status(thm)], ['93', '94'])).
% 0.77/0.94  thf('96', plain,
% 0.77/0.94      (((v5_pre_topc @ sk_C @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 0.77/0.94         <= (((v5_pre_topc @ sk_C @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('split', [status(esa)], ['95'])).
% 0.77/0.94  thf('97', plain,
% 0.77/0.94      ((~ (v5_pre_topc @ sk_C @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 0.77/0.94         <= (~
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('demod', [status(thm)], ['71', '72'])).
% 0.77/0.94  thf('98', plain,
% 0.77/0.94      (~
% 0.77/0.94       ((v5_pre_topc @ sk_C @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) | 
% 0.77/0.94       ((v5_pre_topc @ sk_D @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['96', '97'])).
% 0.77/0.94  thf('99', plain,
% 0.77/0.94      ((~ (v5_pre_topc @ sk_D @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B_1))),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('100', plain, (((sk_C) = (sk_D))),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('101', plain,
% 0.77/0.94      ((~ (v5_pre_topc @ sk_C @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B_1))),
% 0.77/0.94      inference('demod', [status(thm)], ['99', '100'])).
% 0.77/0.94  thf('102', plain,
% 0.77/0.94      (~
% 0.77/0.94       ((v5_pre_topc @ sk_C @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) | 
% 0.77/0.94       ~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1))),
% 0.77/0.94      inference('split', [status(esa)], ['101'])).
% 0.77/0.94  thf('103', plain,
% 0.77/0.94      (![X0 : $i]:
% 0.77/0.94         (~ (l1_pre_topc @ X0)
% 0.77/0.94          | (l1_pre_topc @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['1', '2'])).
% 0.77/0.94  thf('104', plain,
% 0.77/0.94      (![X41 : $i]:
% 0.77/0.94         ((v2_pre_topc @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ X41) @ (u1_pre_topc @ X41)))
% 0.77/0.94          | ~ (l1_pre_topc @ X41)
% 0.77/0.94          | ~ (v2_pre_topc @ X41))),
% 0.77/0.94      inference('cnf', [status(esa)], [fc6_pre_topc])).
% 0.77/0.94  thf('105', plain,
% 0.77/0.94      ((((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 0.77/0.94        | (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.94           (u1_struct_0 @ 
% 0.77/0.94            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['12', '31'])).
% 0.77/0.94  thf('106', plain,
% 0.77/0.94      (((v5_pre_topc @ sk_D @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 0.77/0.94         <= (((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('split', [status(esa)], ['4'])).
% 0.77/0.94  thf('107', plain, (((sk_C) = (sk_D))),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('108', plain,
% 0.77/0.94      (((v5_pre_topc @ sk_C @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 0.77/0.94         <= (((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('demod', [status(thm)], ['106', '107'])).
% 0.77/0.94  thf('109', plain,
% 0.77/0.94      ((m1_subset_1 @ sk_C @ 
% 0.77/0.94        (k1_zfmisc_1 @ 
% 0.77/0.94         (k2_zfmisc_1 @ 
% 0.77/0.94          (u1_struct_0 @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.77/0.94          (u1_struct_0 @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))),
% 0.77/0.94      inference('demod', [status(thm)], ['13', '14'])).
% 0.77/0.94  thf('110', plain,
% 0.77/0.94      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.77/0.94         (~ (v2_pre_topc @ X42)
% 0.77/0.94          | ~ (l1_pre_topc @ X42)
% 0.77/0.94          | ~ (v1_funct_1 @ X43)
% 0.77/0.94          | ~ (v1_funct_2 @ X43 @ 
% 0.77/0.94               (u1_struct_0 @ 
% 0.77/0.94                (g1_pre_topc @ (u1_struct_0 @ X44) @ (u1_pre_topc @ X44))) @ 
% 0.77/0.94               (u1_struct_0 @ X42))
% 0.77/0.94          | ~ (m1_subset_1 @ X43 @ 
% 0.77/0.94               (k1_zfmisc_1 @ 
% 0.77/0.94                (k2_zfmisc_1 @ 
% 0.77/0.94                 (u1_struct_0 @ 
% 0.77/0.94                  (g1_pre_topc @ (u1_struct_0 @ X44) @ (u1_pre_topc @ X44))) @ 
% 0.77/0.94                 (u1_struct_0 @ X42))))
% 0.77/0.94          | ~ (v5_pre_topc @ X43 @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ X44) @ (u1_pre_topc @ X44)) @ X42)
% 0.77/0.94          | (v5_pre_topc @ X45 @ X44 @ X42)
% 0.77/0.94          | ((X45) != (X43))
% 0.77/0.94          | ~ (m1_subset_1 @ X45 @ 
% 0.77/0.94               (k1_zfmisc_1 @ 
% 0.77/0.94                (k2_zfmisc_1 @ (u1_struct_0 @ X44) @ (u1_struct_0 @ X42))))
% 0.77/0.94          | ~ (v1_funct_2 @ X45 @ (u1_struct_0 @ X44) @ (u1_struct_0 @ X42))
% 0.77/0.94          | ~ (v1_funct_1 @ X45)
% 0.77/0.94          | ~ (l1_pre_topc @ X44)
% 0.77/0.94          | ~ (v2_pre_topc @ X44))),
% 0.77/0.94      inference('cnf', [status(esa)], [t62_pre_topc])).
% 0.77/0.94  thf('111', plain,
% 0.77/0.94      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.77/0.94         (~ (v2_pre_topc @ X44)
% 0.77/0.94          | ~ (l1_pre_topc @ X44)
% 0.77/0.94          | ~ (v1_funct_2 @ X43 @ (u1_struct_0 @ X44) @ (u1_struct_0 @ X42))
% 0.77/0.94          | ~ (m1_subset_1 @ X43 @ 
% 0.77/0.94               (k1_zfmisc_1 @ 
% 0.77/0.94                (k2_zfmisc_1 @ (u1_struct_0 @ X44) @ (u1_struct_0 @ X42))))
% 0.77/0.94          | (v5_pre_topc @ X43 @ X44 @ X42)
% 0.77/0.94          | ~ (v5_pre_topc @ X43 @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ X44) @ (u1_pre_topc @ X44)) @ X42)
% 0.77/0.94          | ~ (m1_subset_1 @ X43 @ 
% 0.77/0.94               (k1_zfmisc_1 @ 
% 0.77/0.94                (k2_zfmisc_1 @ 
% 0.77/0.94                 (u1_struct_0 @ 
% 0.77/0.94                  (g1_pre_topc @ (u1_struct_0 @ X44) @ (u1_pre_topc @ X44))) @ 
% 0.77/0.94                 (u1_struct_0 @ X42))))
% 0.77/0.94          | ~ (v1_funct_2 @ X43 @ 
% 0.77/0.94               (u1_struct_0 @ 
% 0.77/0.94                (g1_pre_topc @ (u1_struct_0 @ X44) @ (u1_pre_topc @ X44))) @ 
% 0.77/0.94               (u1_struct_0 @ X42))
% 0.77/0.94          | ~ (v1_funct_1 @ X43)
% 0.77/0.94          | ~ (l1_pre_topc @ X42)
% 0.77/0.94          | ~ (v2_pre_topc @ X42))),
% 0.77/0.94      inference('simplify', [status(thm)], ['110'])).
% 0.77/0.94  thf('112', plain,
% 0.77/0.94      ((~ (v2_pre_topc @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94        | ~ (l1_pre_topc @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94        | ~ (v1_funct_1 @ sk_C)
% 0.77/0.94        | ~ (v1_funct_2 @ sk_C @ 
% 0.77/0.94             (u1_struct_0 @ 
% 0.77/0.94              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.77/0.94             (u1_struct_0 @ 
% 0.77/0.94              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 0.77/0.94        | ~ (v5_pre_topc @ sk_C @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94        | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94        | ~ (m1_subset_1 @ sk_C @ 
% 0.77/0.94             (k1_zfmisc_1 @ 
% 0.77/0.94              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.94               (u1_struct_0 @ 
% 0.77/0.94                (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))
% 0.77/0.94        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.94             (u1_struct_0 @ 
% 0.77/0.94              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 0.77/0.94        | ~ (l1_pre_topc @ sk_A)
% 0.77/0.94        | ~ (v2_pre_topc @ sk_A))),
% 0.77/0.94      inference('sup-', [status(thm)], ['109', '111'])).
% 0.77/0.94  thf('113', plain, ((v1_funct_1 @ sk_C)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('114', plain,
% 0.77/0.94      ((v1_funct_2 @ sk_C @ 
% 0.77/0.94        (u1_struct_0 @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.77/0.94        (u1_struct_0 @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 0.77/0.94      inference('demod', [status(thm)], ['53', '54'])).
% 0.77/0.94  thf('115', plain,
% 0.77/0.94      ((m1_subset_1 @ sk_C @ 
% 0.77/0.94        (k1_zfmisc_1 @ 
% 0.77/0.94         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.94          (u1_struct_0 @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['23', '26'])).
% 0.77/0.94  thf('116', plain, ((l1_pre_topc @ sk_A)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('117', plain, ((v2_pre_topc @ sk_A)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('118', plain,
% 0.77/0.94      ((~ (v2_pre_topc @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94        | ~ (l1_pre_topc @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94        | ~ (v5_pre_topc @ sk_C @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94        | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.94             (u1_struct_0 @ 
% 0.77/0.94              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('demod', [status(thm)],
% 0.77/0.94                ['112', '113', '114', '115', '116', '117'])).
% 0.77/0.94  thf('119', plain,
% 0.77/0.94      (((~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.94            (u1_struct_0 @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 0.77/0.94         | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.77/0.94            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94         | ~ (l1_pre_topc @ 
% 0.77/0.94              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94         | ~ (v2_pre_topc @ 
% 0.77/0.94              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))
% 0.77/0.94         <= (((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['108', '118'])).
% 0.77/0.94  thf('120', plain,
% 0.77/0.94      (((((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 0.77/0.94         | ~ (v2_pre_topc @ 
% 0.77/0.94              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94         | ~ (l1_pre_topc @ 
% 0.77/0.94              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94         | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.77/0.94            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))
% 0.77/0.94         <= (((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['105', '119'])).
% 0.77/0.94  thf('121', plain,
% 0.77/0.94      (((~ (v2_pre_topc @ sk_B_1)
% 0.77/0.94         | ~ (l1_pre_topc @ sk_B_1)
% 0.77/0.94         | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.77/0.94            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94         | ~ (l1_pre_topc @ 
% 0.77/0.94              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94         | ((u1_struct_0 @ sk_B_1) = (k1_xboole_0))))
% 0.77/0.94         <= (((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['104', '120'])).
% 0.77/0.94  thf('122', plain, ((v2_pre_topc @ sk_B_1)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('123', plain, ((l1_pre_topc @ sk_B_1)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('124', plain,
% 0.77/0.94      ((((v5_pre_topc @ sk_C @ sk_A @ 
% 0.77/0.94          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94         | ~ (l1_pre_topc @ 
% 0.77/0.94              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94         | ((u1_struct_0 @ sk_B_1) = (k1_xboole_0))))
% 0.77/0.94         <= (((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('demod', [status(thm)], ['121', '122', '123'])).
% 0.77/0.94  thf('125', plain,
% 0.77/0.94      (((~ (l1_pre_topc @ sk_B_1)
% 0.77/0.94         | ((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 0.77/0.94         | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.77/0.94            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))
% 0.77/0.94         <= (((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['103', '124'])).
% 0.77/0.94  thf('126', plain, ((l1_pre_topc @ sk_B_1)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('127', plain,
% 0.77/0.94      (((((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 0.77/0.94         | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.77/0.94            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))
% 0.77/0.94         <= (((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('demod', [status(thm)], ['125', '126'])).
% 0.77/0.94  thf('128', plain,
% 0.77/0.94      ((((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 0.77/0.94        | (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.94           (u1_struct_0 @ 
% 0.77/0.94            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['12', '31'])).
% 0.77/0.94  thf('129', plain,
% 0.77/0.94      ((m1_subset_1 @ sk_C @ 
% 0.77/0.94        (k1_zfmisc_1 @ 
% 0.77/0.94         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.94          (u1_struct_0 @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['23', '26'])).
% 0.77/0.94  thf('130', plain,
% 0.77/0.94      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.77/0.94         (~ (v2_pre_topc @ X46)
% 0.77/0.94          | ~ (l1_pre_topc @ X46)
% 0.77/0.94          | ~ (v1_funct_1 @ X47)
% 0.77/0.94          | ~ (v1_funct_2 @ X47 @ (u1_struct_0 @ X48) @ 
% 0.77/0.94               (u1_struct_0 @ 
% 0.77/0.94                (g1_pre_topc @ (u1_struct_0 @ X46) @ (u1_pre_topc @ X46))))
% 0.77/0.94          | ~ (m1_subset_1 @ X47 @ 
% 0.77/0.94               (k1_zfmisc_1 @ 
% 0.77/0.94                (k2_zfmisc_1 @ (u1_struct_0 @ X48) @ 
% 0.77/0.94                 (u1_struct_0 @ 
% 0.77/0.94                  (g1_pre_topc @ (u1_struct_0 @ X46) @ (u1_pre_topc @ X46))))))
% 0.77/0.94          | ~ (v5_pre_topc @ X47 @ X48 @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ X46) @ (u1_pre_topc @ X46)))
% 0.77/0.94          | (v5_pre_topc @ X49 @ X48 @ X46)
% 0.77/0.94          | ((X49) != (X47))
% 0.77/0.94          | ~ (m1_subset_1 @ X49 @ 
% 0.77/0.94               (k1_zfmisc_1 @ 
% 0.77/0.94                (k2_zfmisc_1 @ (u1_struct_0 @ X48) @ (u1_struct_0 @ X46))))
% 0.77/0.94          | ~ (v1_funct_2 @ X49 @ (u1_struct_0 @ X48) @ (u1_struct_0 @ X46))
% 0.77/0.94          | ~ (v1_funct_1 @ X49)
% 0.77/0.94          | ~ (l1_pre_topc @ X48)
% 0.77/0.94          | ~ (v2_pre_topc @ X48))),
% 0.77/0.94      inference('cnf', [status(esa)], [t63_pre_topc])).
% 0.77/0.94  thf('131', plain,
% 0.77/0.94      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.77/0.94         (~ (v2_pre_topc @ X48)
% 0.77/0.94          | ~ (l1_pre_topc @ X48)
% 0.77/0.94          | ~ (v1_funct_2 @ X47 @ (u1_struct_0 @ X48) @ (u1_struct_0 @ X46))
% 0.77/0.94          | ~ (m1_subset_1 @ X47 @ 
% 0.77/0.94               (k1_zfmisc_1 @ 
% 0.77/0.94                (k2_zfmisc_1 @ (u1_struct_0 @ X48) @ (u1_struct_0 @ X46))))
% 0.77/0.94          | (v5_pre_topc @ X47 @ X48 @ X46)
% 0.77/0.94          | ~ (v5_pre_topc @ X47 @ X48 @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ X46) @ (u1_pre_topc @ X46)))
% 0.77/0.94          | ~ (m1_subset_1 @ X47 @ 
% 0.77/0.94               (k1_zfmisc_1 @ 
% 0.77/0.94                (k2_zfmisc_1 @ (u1_struct_0 @ X48) @ 
% 0.77/0.94                 (u1_struct_0 @ 
% 0.77/0.94                  (g1_pre_topc @ (u1_struct_0 @ X46) @ (u1_pre_topc @ X46))))))
% 0.77/0.94          | ~ (v1_funct_2 @ X47 @ (u1_struct_0 @ X48) @ 
% 0.77/0.94               (u1_struct_0 @ 
% 0.77/0.94                (g1_pre_topc @ (u1_struct_0 @ X46) @ (u1_pre_topc @ X46))))
% 0.77/0.94          | ~ (v1_funct_1 @ X47)
% 0.77/0.94          | ~ (l1_pre_topc @ X46)
% 0.77/0.94          | ~ (v2_pre_topc @ X46))),
% 0.77/0.94      inference('simplify', [status(thm)], ['130'])).
% 0.77/0.94  thf('132', plain,
% 0.77/0.94      ((~ (v2_pre_topc @ sk_B_1)
% 0.77/0.94        | ~ (l1_pre_topc @ sk_B_1)
% 0.77/0.94        | ~ (v1_funct_1 @ sk_C)
% 0.77/0.94        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.94             (u1_struct_0 @ 
% 0.77/0.94              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 0.77/0.94        | ~ (v5_pre_topc @ sk_C @ sk_A @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94        | (v5_pre_topc @ sk_C @ sk_A @ sk_B_1)
% 0.77/0.94        | ~ (m1_subset_1 @ sk_C @ 
% 0.77/0.94             (k1_zfmisc_1 @ 
% 0.77/0.94              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))
% 0.77/0.94        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))
% 0.77/0.94        | ~ (l1_pre_topc @ sk_A)
% 0.77/0.94        | ~ (v2_pre_topc @ sk_A))),
% 0.77/0.94      inference('sup-', [status(thm)], ['129', '131'])).
% 0.77/0.94  thf('133', plain, ((v2_pre_topc @ sk_B_1)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('134', plain, ((l1_pre_topc @ sk_B_1)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('135', plain, ((v1_funct_1 @ sk_C)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('136', plain,
% 0.77/0.94      ((m1_subset_1 @ sk_C @ 
% 0.77/0.94        (k1_zfmisc_1 @ 
% 0.77/0.94         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('137', plain,
% 0.77/0.94      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('138', plain, ((l1_pre_topc @ sk_A)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('139', plain, ((v2_pre_topc @ sk_A)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('140', plain,
% 0.77/0.94      ((~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.94           (u1_struct_0 @ 
% 0.77/0.94            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 0.77/0.94        | ~ (v5_pre_topc @ sk_C @ sk_A @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94        | (v5_pre_topc @ sk_C @ sk_A @ sk_B_1))),
% 0.77/0.94      inference('demod', [status(thm)],
% 0.77/0.94                ['132', '133', '134', '135', '136', '137', '138', '139'])).
% 0.77/0.94  thf('141', plain,
% 0.77/0.94      ((((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 0.77/0.94        | (v5_pre_topc @ sk_C @ sk_A @ sk_B_1)
% 0.77/0.94        | ~ (v5_pre_topc @ sk_C @ sk_A @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['128', '140'])).
% 0.77/0.94  thf('142', plain,
% 0.77/0.94      (((((u1_struct_0 @ sk_B_1) = (k1_xboole_0))
% 0.77/0.94         | (v5_pre_topc @ sk_C @ sk_A @ sk_B_1)
% 0.77/0.94         | ((u1_struct_0 @ sk_B_1) = (k1_xboole_0))))
% 0.77/0.94         <= (((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['127', '141'])).
% 0.77/0.94  thf('143', plain,
% 0.77/0.94      ((((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)
% 0.77/0.94         | ((u1_struct_0 @ sk_B_1) = (k1_xboole_0))))
% 0.77/0.94         <= (((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('simplify', [status(thm)], ['142'])).
% 0.77/0.94  thf('144', plain,
% 0.77/0.94      ((~ (v5_pre_topc @ sk_C @ sk_A @ sk_B_1))
% 0.77/0.94         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('split', [status(esa)], ['70'])).
% 0.77/0.94  thf('145', plain,
% 0.77/0.94      ((((u1_struct_0 @ sk_B_1) = (k1_xboole_0)))
% 0.77/0.94         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)) & 
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['143', '144'])).
% 0.77/0.94  thf('146', plain,
% 0.77/0.94      (![X28 : $i]:
% 0.77/0.94         (((X28) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X28) @ X28))),
% 0.77/0.94      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.77/0.94  thf('147', plain,
% 0.77/0.94      ((((u1_struct_0 @ sk_B_1) = (k1_xboole_0)))
% 0.77/0.94         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)) & 
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['143', '144'])).
% 0.77/0.94  thf('148', plain,
% 0.77/0.94      (![X0 : $i]:
% 0.77/0.94         (~ (v1_xboole_0 @ 
% 0.77/0.94             (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1)))
% 0.77/0.94          | ~ (r2_hidden @ X0 @ sk_C))),
% 0.77/0.94      inference('sup-', [status(thm)], ['84', '85'])).
% 0.77/0.94  thf('149', plain,
% 0.77/0.94      ((![X0 : $i]:
% 0.77/0.94          (~ (v1_xboole_0 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0))
% 0.77/0.94           | ~ (r2_hidden @ X0 @ sk_C)))
% 0.77/0.94         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)) & 
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['147', '148'])).
% 0.77/0.94  thf('150', plain,
% 0.77/0.94      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.77/0.94      inference('simplify', [status(thm)], ['88'])).
% 0.77/0.94  thf('151', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.77/0.94      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.77/0.94  thf('152', plain,
% 0.77/0.94      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C))
% 0.77/0.94         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)) & 
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('demod', [status(thm)], ['149', '150', '151'])).
% 0.77/0.94  thf('153', plain,
% 0.77/0.94      ((((sk_C) = (k1_xboole_0)))
% 0.77/0.94         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)) & 
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['146', '152'])).
% 0.77/0.94  thf('154', plain,
% 0.77/0.94      ((((u1_struct_0 @ sk_B_1) = (sk_C)))
% 0.77/0.94         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)) & 
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('demod', [status(thm)], ['145', '153'])).
% 0.77/0.94  thf('155', plain,
% 0.77/0.94      (![X41 : $i]:
% 0.77/0.94         ((v2_pre_topc @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ X41) @ (u1_pre_topc @ X41)))
% 0.77/0.94          | ~ (l1_pre_topc @ X41)
% 0.77/0.94          | ~ (v2_pre_topc @ X41))),
% 0.77/0.94      inference('cnf', [status(esa)], [fc6_pre_topc])).
% 0.77/0.94  thf('156', plain,
% 0.77/0.94      (![X0 : $i]:
% 0.77/0.94         (~ (l1_pre_topc @ X0)
% 0.77/0.94          | (l1_pre_topc @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['1', '2'])).
% 0.77/0.94  thf('157', plain,
% 0.77/0.94      ((m1_subset_1 @ sk_C @ 
% 0.77/0.94        (k1_zfmisc_1 @ 
% 0.77/0.94         (k2_zfmisc_1 @ 
% 0.77/0.94          (u1_struct_0 @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.77/0.94          (u1_struct_0 @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))),
% 0.77/0.94      inference('demod', [status(thm)], ['13', '14'])).
% 0.77/0.94  thf('158', plain,
% 0.77/0.94      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.77/0.94         (~ (v1_funct_2 @ X36 @ X37 @ X35)
% 0.77/0.94          | (v1_partfun1 @ X36 @ X37)
% 0.77/0.94          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X35)))
% 0.77/0.94          | ~ (v1_funct_1 @ X36)
% 0.77/0.94          | ((X35) = (k1_xboole_0)))),
% 0.77/0.94      inference('simplify', [status(thm)], ['7'])).
% 0.77/0.94  thf('159', plain,
% 0.77/0.94      ((((u1_struct_0 @ 
% 0.77/0.94          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94          = (k1_xboole_0))
% 0.77/0.94        | ~ (v1_funct_1 @ sk_C)
% 0.77/0.94        | (v1_partfun1 @ sk_C @ 
% 0.77/0.94           (u1_struct_0 @ 
% 0.77/0.94            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.77/0.94        | ~ (v1_funct_2 @ sk_C @ 
% 0.77/0.94             (u1_struct_0 @ 
% 0.77/0.94              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.77/0.94             (u1_struct_0 @ 
% 0.77/0.94              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['157', '158'])).
% 0.77/0.94  thf('160', plain, ((v1_funct_1 @ sk_C)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('161', plain,
% 0.77/0.94      ((v1_funct_2 @ sk_C @ 
% 0.77/0.94        (u1_struct_0 @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.77/0.94        (u1_struct_0 @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 0.77/0.94      inference('demod', [status(thm)], ['53', '54'])).
% 0.77/0.94  thf('162', plain,
% 0.77/0.94      ((((u1_struct_0 @ 
% 0.77/0.94          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94          = (k1_xboole_0))
% 0.77/0.94        | (v1_partfun1 @ sk_C @ 
% 0.77/0.94           (u1_struct_0 @ 
% 0.77/0.94            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 0.77/0.94      inference('demod', [status(thm)], ['159', '160', '161'])).
% 0.77/0.94  thf('163', plain,
% 0.77/0.94      ((m1_subset_1 @ sk_C @ 
% 0.77/0.94        (k1_zfmisc_1 @ 
% 0.77/0.94         (k2_zfmisc_1 @ 
% 0.77/0.94          (u1_struct_0 @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.77/0.94          (u1_struct_0 @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))),
% 0.77/0.94      inference('demod', [status(thm)], ['13', '14'])).
% 0.77/0.94  thf('164', plain,
% 0.77/0.94      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.77/0.94         ((v4_relat_1 @ X17 @ X18)
% 0.77/0.94          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.77/0.94      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.77/0.94  thf('165', plain,
% 0.77/0.94      ((v4_relat_1 @ sk_C @ 
% 0.77/0.94        (u1_struct_0 @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['163', '164'])).
% 0.77/0.94  thf(d18_relat_1, axiom,
% 0.77/0.94    (![A:$i,B:$i]:
% 0.77/0.94     ( ( v1_relat_1 @ B ) =>
% 0.77/0.94       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.77/0.94  thf('166', plain,
% 0.77/0.94      (![X10 : $i, X11 : $i]:
% 0.77/0.94         (~ (v4_relat_1 @ X10 @ X11)
% 0.77/0.94          | (r1_tarski @ (k1_relat_1 @ X10) @ X11)
% 0.77/0.94          | ~ (v1_relat_1 @ X10))),
% 0.77/0.94      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.77/0.94  thf('167', plain,
% 0.77/0.94      ((~ (v1_relat_1 @ sk_C)
% 0.77/0.94        | (r1_tarski @ (k1_relat_1 @ sk_C) @ 
% 0.77/0.94           (u1_struct_0 @ 
% 0.77/0.94            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['165', '166'])).
% 0.77/0.94  thf('168', plain, ((v1_relat_1 @ sk_C)),
% 0.77/0.94      inference('sup-', [status(thm)], ['20', '21'])).
% 0.77/0.94  thf('169', plain,
% 0.77/0.94      ((r1_tarski @ (k1_relat_1 @ sk_C) @ 
% 0.77/0.94        (u1_struct_0 @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 0.77/0.94      inference('demod', [status(thm)], ['167', '168'])).
% 0.77/0.94  thf('170', plain,
% 0.77/0.94      ((m1_subset_1 @ sk_C @ 
% 0.77/0.94        (k1_zfmisc_1 @ 
% 0.77/0.94         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf(t13_relset_1, axiom,
% 0.77/0.94    (![A:$i,B:$i,C:$i,D:$i]:
% 0.77/0.94     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.77/0.94       ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 0.77/0.94         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 0.77/0.94  thf('171', plain,
% 0.77/0.94      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.77/0.94         (~ (r1_tarski @ (k1_relat_1 @ X20) @ X21)
% 0.77/0.94          | (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.77/0.94          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 0.77/0.94      inference('cnf', [status(esa)], [t13_relset_1])).
% 0.77/0.94  thf('172', plain,
% 0.77/0.94      (![X0 : $i]:
% 0.77/0.94         ((m1_subset_1 @ sk_C @ 
% 0.77/0.94           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ (u1_struct_0 @ sk_B_1))))
% 0.77/0.94          | ~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0))),
% 0.77/0.94      inference('sup-', [status(thm)], ['170', '171'])).
% 0.77/0.94  thf('173', plain,
% 0.77/0.94      ((m1_subset_1 @ sk_C @ 
% 0.77/0.94        (k1_zfmisc_1 @ 
% 0.77/0.94         (k2_zfmisc_1 @ 
% 0.77/0.94          (u1_struct_0 @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.77/0.94          (u1_struct_0 @ sk_B_1))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['169', '172'])).
% 0.77/0.94  thf('174', plain,
% 0.77/0.94      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.77/0.94         (~ (v1_funct_1 @ X32)
% 0.77/0.94          | ~ (v1_partfun1 @ X32 @ X33)
% 0.77/0.94          | (v1_funct_2 @ X32 @ X33 @ X34)
% 0.77/0.94          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.77/0.94      inference('cnf', [status(esa)], [cc1_funct_2])).
% 0.77/0.94  thf('175', plain,
% 0.77/0.94      (((v1_funct_2 @ sk_C @ 
% 0.77/0.94         (u1_struct_0 @ 
% 0.77/0.94          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.77/0.94         (u1_struct_0 @ sk_B_1))
% 0.77/0.94        | ~ (v1_partfun1 @ sk_C @ 
% 0.77/0.94             (u1_struct_0 @ 
% 0.77/0.94              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.77/0.94        | ~ (v1_funct_1 @ sk_C))),
% 0.77/0.94      inference('sup-', [status(thm)], ['173', '174'])).
% 0.77/0.94  thf('176', plain, ((v1_funct_1 @ sk_C)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('177', plain,
% 0.77/0.94      (((v1_funct_2 @ sk_C @ 
% 0.77/0.94         (u1_struct_0 @ 
% 0.77/0.94          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.77/0.94         (u1_struct_0 @ sk_B_1))
% 0.77/0.94        | ~ (v1_partfun1 @ sk_C @ 
% 0.77/0.94             (u1_struct_0 @ 
% 0.77/0.94              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 0.77/0.94      inference('demod', [status(thm)], ['175', '176'])).
% 0.77/0.94  thf('178', plain,
% 0.77/0.94      ((((u1_struct_0 @ 
% 0.77/0.94          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94          = (k1_xboole_0))
% 0.77/0.94        | (v1_funct_2 @ sk_C @ 
% 0.77/0.94           (u1_struct_0 @ 
% 0.77/0.94            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.77/0.94           (u1_struct_0 @ sk_B_1)))),
% 0.77/0.94      inference('sup-', [status(thm)], ['162', '177'])).
% 0.77/0.94  thf('179', plain,
% 0.77/0.94      (((v5_pre_topc @ sk_C @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 0.77/0.94         <= (((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('demod', [status(thm)], ['106', '107'])).
% 0.77/0.94  thf('180', plain,
% 0.77/0.94      ((m1_subset_1 @ sk_C @ 
% 0.77/0.94        (k1_zfmisc_1 @ 
% 0.77/0.94         (k2_zfmisc_1 @ 
% 0.77/0.94          (u1_struct_0 @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.77/0.94          (u1_struct_0 @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))),
% 0.77/0.94      inference('demod', [status(thm)], ['13', '14'])).
% 0.77/0.94  thf('181', plain,
% 0.77/0.94      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.77/0.94         (~ (v2_pre_topc @ X48)
% 0.77/0.94          | ~ (l1_pre_topc @ X48)
% 0.77/0.94          | ~ (v1_funct_2 @ X47 @ (u1_struct_0 @ X48) @ (u1_struct_0 @ X46))
% 0.77/0.94          | ~ (m1_subset_1 @ X47 @ 
% 0.77/0.94               (k1_zfmisc_1 @ 
% 0.77/0.94                (k2_zfmisc_1 @ (u1_struct_0 @ X48) @ (u1_struct_0 @ X46))))
% 0.77/0.94          | (v5_pre_topc @ X47 @ X48 @ X46)
% 0.77/0.94          | ~ (v5_pre_topc @ X47 @ X48 @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ X46) @ (u1_pre_topc @ X46)))
% 0.77/0.94          | ~ (m1_subset_1 @ X47 @ 
% 0.77/0.94               (k1_zfmisc_1 @ 
% 0.77/0.94                (k2_zfmisc_1 @ (u1_struct_0 @ X48) @ 
% 0.77/0.94                 (u1_struct_0 @ 
% 0.77/0.94                  (g1_pre_topc @ (u1_struct_0 @ X46) @ (u1_pre_topc @ X46))))))
% 0.77/0.94          | ~ (v1_funct_2 @ X47 @ (u1_struct_0 @ X48) @ 
% 0.77/0.94               (u1_struct_0 @ 
% 0.77/0.94                (g1_pre_topc @ (u1_struct_0 @ X46) @ (u1_pre_topc @ X46))))
% 0.77/0.94          | ~ (v1_funct_1 @ X47)
% 0.77/0.94          | ~ (l1_pre_topc @ X46)
% 0.77/0.94          | ~ (v2_pre_topc @ X46))),
% 0.77/0.94      inference('simplify', [status(thm)], ['130'])).
% 0.77/0.94  thf('182', plain,
% 0.77/0.94      ((~ (v2_pre_topc @ sk_B_1)
% 0.77/0.94        | ~ (l1_pre_topc @ sk_B_1)
% 0.77/0.94        | ~ (v1_funct_1 @ sk_C)
% 0.77/0.94        | ~ (v1_funct_2 @ sk_C @ 
% 0.77/0.94             (u1_struct_0 @ 
% 0.77/0.94              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.77/0.94             (u1_struct_0 @ 
% 0.77/0.94              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 0.77/0.94        | ~ (v5_pre_topc @ sk_C @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94        | (v5_pre_topc @ sk_C @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_1)
% 0.77/0.94        | ~ (m1_subset_1 @ sk_C @ 
% 0.77/0.94             (k1_zfmisc_1 @ 
% 0.77/0.94              (k2_zfmisc_1 @ 
% 0.77/0.94               (u1_struct_0 @ 
% 0.77/0.94                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.77/0.94               (u1_struct_0 @ sk_B_1))))
% 0.77/0.94        | ~ (v1_funct_2 @ sk_C @ 
% 0.77/0.94             (u1_struct_0 @ 
% 0.77/0.94              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.77/0.94             (u1_struct_0 @ sk_B_1))
% 0.77/0.94        | ~ (l1_pre_topc @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.77/0.94        | ~ (v2_pre_topc @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['180', '181'])).
% 0.77/0.94  thf('183', plain, ((v2_pre_topc @ sk_B_1)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('184', plain, ((l1_pre_topc @ sk_B_1)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('185', plain, ((v1_funct_1 @ sk_C)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('186', plain,
% 0.77/0.94      ((v1_funct_2 @ sk_C @ 
% 0.77/0.94        (u1_struct_0 @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.77/0.94        (u1_struct_0 @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 0.77/0.94      inference('demod', [status(thm)], ['53', '54'])).
% 0.77/0.94  thf('187', plain,
% 0.77/0.94      ((m1_subset_1 @ sk_C @ 
% 0.77/0.94        (k1_zfmisc_1 @ 
% 0.77/0.94         (k2_zfmisc_1 @ 
% 0.77/0.94          (u1_struct_0 @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.77/0.94          (u1_struct_0 @ sk_B_1))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['169', '172'])).
% 0.77/0.94  thf('188', plain,
% 0.77/0.94      ((~ (v5_pre_topc @ sk_C @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94        | (v5_pre_topc @ sk_C @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_1)
% 0.77/0.94        | ~ (v1_funct_2 @ sk_C @ 
% 0.77/0.94             (u1_struct_0 @ 
% 0.77/0.94              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.77/0.94             (u1_struct_0 @ sk_B_1))
% 0.77/0.94        | ~ (l1_pre_topc @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.77/0.94        | ~ (v2_pre_topc @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 0.77/0.94      inference('demod', [status(thm)],
% 0.77/0.94                ['182', '183', '184', '185', '186', '187'])).
% 0.77/0.94  thf('189', plain,
% 0.77/0.94      (((~ (v2_pre_topc @ 
% 0.77/0.94            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.77/0.94         | ~ (l1_pre_topc @ 
% 0.77/0.94              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.77/0.94         | ~ (v1_funct_2 @ sk_C @ 
% 0.77/0.94              (u1_struct_0 @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.77/0.94              (u1_struct_0 @ sk_B_1))
% 0.77/0.94         | (v5_pre_topc @ sk_C @ 
% 0.77/0.94            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94            sk_B_1)))
% 0.77/0.94         <= (((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['179', '188'])).
% 0.77/0.94  thf('190', plain,
% 0.77/0.94      (((((u1_struct_0 @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94           = (k1_xboole_0))
% 0.77/0.94         | (v5_pre_topc @ sk_C @ 
% 0.77/0.94            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94            sk_B_1)
% 0.77/0.94         | ~ (l1_pre_topc @ 
% 0.77/0.94              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.77/0.94         | ~ (v2_pre_topc @ 
% 0.77/0.94              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.77/0.94         <= (((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['178', '189'])).
% 0.77/0.94  thf('191', plain,
% 0.77/0.94      (((~ (l1_pre_topc @ sk_A)
% 0.77/0.94         | ~ (v2_pre_topc @ 
% 0.77/0.94              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.77/0.94         | (v5_pre_topc @ sk_C @ 
% 0.77/0.94            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94            sk_B_1)
% 0.77/0.94         | ((u1_struct_0 @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94             = (k1_xboole_0))))
% 0.77/0.94         <= (((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['156', '190'])).
% 0.77/0.94  thf('192', plain, ((l1_pre_topc @ sk_A)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('193', plain,
% 0.77/0.94      (((~ (v2_pre_topc @ 
% 0.77/0.94            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.77/0.94         | (v5_pre_topc @ sk_C @ 
% 0.77/0.94            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94            sk_B_1)
% 0.77/0.94         | ((u1_struct_0 @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94             = (k1_xboole_0))))
% 0.77/0.94         <= (((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('demod', [status(thm)], ['191', '192'])).
% 0.77/0.94  thf('194', plain,
% 0.77/0.94      (((~ (v2_pre_topc @ sk_A)
% 0.77/0.94         | ~ (l1_pre_topc @ sk_A)
% 0.77/0.94         | ((u1_struct_0 @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94             = (k1_xboole_0))
% 0.77/0.94         | (v5_pre_topc @ sk_C @ 
% 0.77/0.94            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94            sk_B_1)))
% 0.77/0.94         <= (((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['155', '193'])).
% 0.77/0.94  thf('195', plain, ((v2_pre_topc @ sk_A)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('196', plain, ((l1_pre_topc @ sk_A)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('197', plain,
% 0.77/0.94      (((((u1_struct_0 @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94           = (k1_xboole_0))
% 0.77/0.94         | (v5_pre_topc @ sk_C @ 
% 0.77/0.94            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94            sk_B_1)))
% 0.77/0.94         <= (((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('demod', [status(thm)], ['194', '195', '196'])).
% 0.77/0.94  thf('198', plain,
% 0.77/0.94      ((((u1_struct_0 @ 
% 0.77/0.94          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94          = (k1_xboole_0))
% 0.77/0.94        | (v1_funct_2 @ sk_C @ 
% 0.77/0.94           (u1_struct_0 @ 
% 0.77/0.94            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.77/0.94           (u1_struct_0 @ sk_B_1)))),
% 0.77/0.94      inference('sup-', [status(thm)], ['162', '177'])).
% 0.77/0.94  thf('199', plain,
% 0.77/0.94      ((m1_subset_1 @ sk_C @ 
% 0.77/0.94        (k1_zfmisc_1 @ 
% 0.77/0.94         (k2_zfmisc_1 @ 
% 0.77/0.94          (u1_struct_0 @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.77/0.94          (u1_struct_0 @ sk_B_1))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['169', '172'])).
% 0.77/0.94  thf('200', plain,
% 0.77/0.94      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.77/0.94         (~ (v2_pre_topc @ X44)
% 0.77/0.94          | ~ (l1_pre_topc @ X44)
% 0.77/0.94          | ~ (v1_funct_2 @ X43 @ (u1_struct_0 @ X44) @ (u1_struct_0 @ X42))
% 0.77/0.94          | ~ (m1_subset_1 @ X43 @ 
% 0.77/0.94               (k1_zfmisc_1 @ 
% 0.77/0.94                (k2_zfmisc_1 @ (u1_struct_0 @ X44) @ (u1_struct_0 @ X42))))
% 0.77/0.94          | (v5_pre_topc @ X43 @ X44 @ X42)
% 0.77/0.94          | ~ (v5_pre_topc @ X43 @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ X44) @ (u1_pre_topc @ X44)) @ X42)
% 0.77/0.94          | ~ (m1_subset_1 @ X43 @ 
% 0.77/0.94               (k1_zfmisc_1 @ 
% 0.77/0.94                (k2_zfmisc_1 @ 
% 0.77/0.94                 (u1_struct_0 @ 
% 0.77/0.94                  (g1_pre_topc @ (u1_struct_0 @ X44) @ (u1_pre_topc @ X44))) @ 
% 0.77/0.94                 (u1_struct_0 @ X42))))
% 0.77/0.94          | ~ (v1_funct_2 @ X43 @ 
% 0.77/0.94               (u1_struct_0 @ 
% 0.77/0.94                (g1_pre_topc @ (u1_struct_0 @ X44) @ (u1_pre_topc @ X44))) @ 
% 0.77/0.94               (u1_struct_0 @ X42))
% 0.77/0.94          | ~ (v1_funct_1 @ X43)
% 0.77/0.94          | ~ (l1_pre_topc @ X42)
% 0.77/0.94          | ~ (v2_pre_topc @ X42))),
% 0.77/0.94      inference('simplify', [status(thm)], ['110'])).
% 0.77/0.94  thf('201', plain,
% 0.77/0.94      ((~ (v2_pre_topc @ sk_B_1)
% 0.77/0.94        | ~ (l1_pre_topc @ sk_B_1)
% 0.77/0.94        | ~ (v1_funct_1 @ sk_C)
% 0.77/0.94        | ~ (v1_funct_2 @ sk_C @ 
% 0.77/0.94             (u1_struct_0 @ 
% 0.77/0.94              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.77/0.94             (u1_struct_0 @ sk_B_1))
% 0.77/0.94        | ~ (v5_pre_topc @ sk_C @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94             sk_B_1)
% 0.77/0.94        | (v5_pre_topc @ sk_C @ sk_A @ sk_B_1)
% 0.77/0.94        | ~ (m1_subset_1 @ sk_C @ 
% 0.77/0.94             (k1_zfmisc_1 @ 
% 0.77/0.94              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))
% 0.77/0.94        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))
% 0.77/0.94        | ~ (l1_pre_topc @ sk_A)
% 0.77/0.94        | ~ (v2_pre_topc @ sk_A))),
% 0.77/0.94      inference('sup-', [status(thm)], ['199', '200'])).
% 0.77/0.94  thf('202', plain, ((v2_pre_topc @ sk_B_1)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('203', plain, ((l1_pre_topc @ sk_B_1)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('204', plain, ((v1_funct_1 @ sk_C)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('205', plain,
% 0.77/0.94      ((m1_subset_1 @ sk_C @ 
% 0.77/0.94        (k1_zfmisc_1 @ 
% 0.77/0.94         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('206', plain,
% 0.77/0.94      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('207', plain, ((l1_pre_topc @ sk_A)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('208', plain, ((v2_pre_topc @ sk_A)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('209', plain,
% 0.77/0.94      ((~ (v1_funct_2 @ sk_C @ 
% 0.77/0.94           (u1_struct_0 @ 
% 0.77/0.94            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.77/0.94           (u1_struct_0 @ sk_B_1))
% 0.77/0.94        | ~ (v5_pre_topc @ sk_C @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94             sk_B_1)
% 0.77/0.94        | (v5_pre_topc @ sk_C @ sk_A @ sk_B_1))),
% 0.77/0.94      inference('demod', [status(thm)],
% 0.77/0.94                ['201', '202', '203', '204', '205', '206', '207', '208'])).
% 0.77/0.94  thf('210', plain,
% 0.77/0.94      ((((u1_struct_0 @ 
% 0.77/0.94          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94          = (k1_xboole_0))
% 0.77/0.94        | (v5_pre_topc @ sk_C @ sk_A @ sk_B_1)
% 0.77/0.94        | ~ (v5_pre_topc @ sk_C @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94             sk_B_1))),
% 0.77/0.94      inference('sup-', [status(thm)], ['198', '209'])).
% 0.77/0.94  thf('211', plain,
% 0.77/0.94      (((((u1_struct_0 @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94           = (k1_xboole_0))
% 0.77/0.94         | (v5_pre_topc @ sk_C @ sk_A @ sk_B_1)
% 0.77/0.94         | ((u1_struct_0 @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94             = (k1_xboole_0))))
% 0.77/0.94         <= (((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['197', '210'])).
% 0.77/0.94  thf('212', plain,
% 0.77/0.94      ((((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)
% 0.77/0.94         | ((u1_struct_0 @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94             = (k1_xboole_0))))
% 0.77/0.94         <= (((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('simplify', [status(thm)], ['211'])).
% 0.77/0.94  thf('213', plain,
% 0.77/0.94      ((~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.94           (u1_struct_0 @ 
% 0.77/0.94            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 0.77/0.94        | ~ (v5_pre_topc @ sk_C @ sk_A @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94        | (v5_pre_topc @ sk_C @ sk_A @ sk_B_1))),
% 0.77/0.94      inference('demod', [status(thm)],
% 0.77/0.94                ['132', '133', '134', '135', '136', '137', '138', '139'])).
% 0.77/0.94  thf('214', plain,
% 0.77/0.94      (((~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.77/0.94         | (v5_pre_topc @ sk_C @ sk_A @ sk_B_1)
% 0.77/0.94         | (v5_pre_topc @ sk_C @ sk_A @ sk_B_1)
% 0.77/0.94         | ~ (v5_pre_topc @ sk_C @ sk_A @ 
% 0.77/0.94              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))
% 0.77/0.94         <= (((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['212', '213'])).
% 0.77/0.94  thf('215', plain,
% 0.77/0.94      (((~ (v5_pre_topc @ sk_C @ sk_A @ 
% 0.77/0.94            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94         | (v5_pre_topc @ sk_C @ sk_A @ sk_B_1)
% 0.77/0.94         | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ k1_xboole_0)))
% 0.77/0.94         <= (((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('simplify', [status(thm)], ['214'])).
% 0.77/0.94  thf('216', plain,
% 0.77/0.94      (((~ (v5_pre_topc @ sk_C @ sk_A @ 
% 0.77/0.94            (g1_pre_topc @ sk_C @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94         | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.77/0.94         | (v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))
% 0.77/0.94         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)) & 
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['154', '215'])).
% 0.77/0.94  thf('217', plain,
% 0.77/0.94      ((((u1_struct_0 @ sk_B_1) = (k1_xboole_0)))
% 0.77/0.94         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)) & 
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['143', '144'])).
% 0.77/0.94  thf('218', plain,
% 0.77/0.94      (((~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.94            (u1_struct_0 @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 0.77/0.94         | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.77/0.94            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94         | ~ (l1_pre_topc @ 
% 0.77/0.94              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94         | ~ (v2_pre_topc @ 
% 0.77/0.94              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))
% 0.77/0.94         <= (((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['108', '118'])).
% 0.77/0.94  thf('219', plain,
% 0.77/0.94      (((~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.94            (u1_struct_0 @ (g1_pre_topc @ k1_xboole_0 @ (u1_pre_topc @ sk_B_1))))
% 0.77/0.94         | ~ (v2_pre_topc @ 
% 0.77/0.94              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94         | ~ (l1_pre_topc @ 
% 0.77/0.94              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94         | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.77/0.94            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))
% 0.77/0.94         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)) & 
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['217', '218'])).
% 0.77/0.94  thf('220', plain,
% 0.77/0.94      ((((u1_struct_0 @ sk_B_1) = (k1_xboole_0)))
% 0.77/0.94         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)) & 
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['143', '144'])).
% 0.77/0.94  thf('221', plain,
% 0.77/0.94      ((((u1_struct_0 @ sk_B_1) = (k1_xboole_0)))
% 0.77/0.94         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)) & 
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['143', '144'])).
% 0.77/0.94  thf('222', plain,
% 0.77/0.94      ((((u1_struct_0 @ sk_B_1) = (k1_xboole_0)))
% 0.77/0.94         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)) & 
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['143', '144'])).
% 0.77/0.94  thf('223', plain,
% 0.77/0.94      (((~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.94            (u1_struct_0 @ (g1_pre_topc @ k1_xboole_0 @ (u1_pre_topc @ sk_B_1))))
% 0.77/0.94         | ~ (v2_pre_topc @ 
% 0.77/0.94              (g1_pre_topc @ k1_xboole_0 @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94         | ~ (l1_pre_topc @ 
% 0.77/0.94              (g1_pre_topc @ k1_xboole_0 @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94         | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.77/0.94            (g1_pre_topc @ k1_xboole_0 @ (u1_pre_topc @ sk_B_1)))))
% 0.77/0.94         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)) & 
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('demod', [status(thm)], ['219', '220', '221', '222'])).
% 0.77/0.94  thf('224', plain,
% 0.77/0.94      ((((sk_C) = (k1_xboole_0)))
% 0.77/0.94         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)) & 
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['146', '152'])).
% 0.77/0.94  thf('225', plain,
% 0.77/0.94      ((((sk_C) = (k1_xboole_0)))
% 0.77/0.94         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)) & 
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['146', '152'])).
% 0.77/0.94  thf('226', plain,
% 0.77/0.94      ((((u1_struct_0 @ sk_B_1) = (sk_C)))
% 0.77/0.94         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)) & 
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('demod', [status(thm)], ['145', '153'])).
% 0.77/0.94  thf('227', plain,
% 0.77/0.94      (![X41 : $i]:
% 0.77/0.94         ((v2_pre_topc @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ X41) @ (u1_pre_topc @ X41)))
% 0.77/0.94          | ~ (l1_pre_topc @ X41)
% 0.77/0.94          | ~ (v2_pre_topc @ X41))),
% 0.77/0.94      inference('cnf', [status(esa)], [fc6_pre_topc])).
% 0.77/0.94  thf('228', plain,
% 0.77/0.94      ((((v2_pre_topc @ (g1_pre_topc @ sk_C @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94         | ~ (v2_pre_topc @ sk_B_1)
% 0.77/0.94         | ~ (l1_pre_topc @ sk_B_1)))
% 0.77/0.94         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)) & 
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('sup+', [status(thm)], ['226', '227'])).
% 0.77/0.94  thf('229', plain, ((v2_pre_topc @ sk_B_1)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('230', plain, ((l1_pre_topc @ sk_B_1)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('231', plain,
% 0.77/0.94      (((v2_pre_topc @ (g1_pre_topc @ sk_C @ (u1_pre_topc @ sk_B_1))))
% 0.77/0.94         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)) & 
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('demod', [status(thm)], ['228', '229', '230'])).
% 0.77/0.94  thf('232', plain,
% 0.77/0.94      ((((sk_C) = (k1_xboole_0)))
% 0.77/0.94         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)) & 
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['146', '152'])).
% 0.77/0.94  thf('233', plain,
% 0.77/0.94      ((((u1_struct_0 @ sk_B_1) = (sk_C)))
% 0.77/0.94         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)) & 
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('demod', [status(thm)], ['145', '153'])).
% 0.77/0.94  thf('234', plain,
% 0.77/0.94      (![X0 : $i]:
% 0.77/0.94         (~ (l1_pre_topc @ X0)
% 0.77/0.94          | (l1_pre_topc @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['1', '2'])).
% 0.77/0.94  thf('235', plain,
% 0.77/0.94      ((((l1_pre_topc @ (g1_pre_topc @ sk_C @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94         | ~ (l1_pre_topc @ sk_B_1)))
% 0.77/0.94         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)) & 
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('sup+', [status(thm)], ['233', '234'])).
% 0.77/0.94  thf('236', plain, ((l1_pre_topc @ sk_B_1)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('237', plain,
% 0.77/0.94      (((l1_pre_topc @ (g1_pre_topc @ sk_C @ (u1_pre_topc @ sk_B_1))))
% 0.77/0.94         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)) & 
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('demod', [status(thm)], ['235', '236'])).
% 0.77/0.94  thf('238', plain,
% 0.77/0.94      ((((sk_C) = (k1_xboole_0)))
% 0.77/0.94         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)) & 
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['146', '152'])).
% 0.77/0.94  thf('239', plain,
% 0.77/0.94      (((~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.94            (u1_struct_0 @ (g1_pre_topc @ sk_C @ (u1_pre_topc @ sk_B_1))))
% 0.77/0.94         | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.77/0.94            (g1_pre_topc @ sk_C @ (u1_pre_topc @ sk_B_1)))))
% 0.77/0.94         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)) & 
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('demod', [status(thm)],
% 0.77/0.94                ['223', '224', '225', '231', '232', '237', '238'])).
% 0.77/0.94  thf('240', plain,
% 0.77/0.94      ((((u1_struct_0 @ sk_B_1) = (sk_C)))
% 0.77/0.94         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)) & 
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('demod', [status(thm)], ['145', '153'])).
% 0.77/0.94  thf('241', plain,
% 0.77/0.94      ((((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)
% 0.77/0.94         | ((u1_struct_0 @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94             = (k1_xboole_0))))
% 0.77/0.94         <= (((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('simplify', [status(thm)], ['211'])).
% 0.77/0.94  thf('242', plain,
% 0.77/0.94      (((((u1_struct_0 @ (g1_pre_topc @ sk_C @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94           = (k1_xboole_0))
% 0.77/0.94         | (v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))
% 0.77/0.94         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)) & 
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('sup+', [status(thm)], ['240', '241'])).
% 0.77/0.94  thf('243', plain,
% 0.77/0.94      ((((sk_C) = (k1_xboole_0)))
% 0.77/0.94         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)) & 
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['146', '152'])).
% 0.77/0.94  thf('244', plain,
% 0.77/0.94      (((((u1_struct_0 @ (g1_pre_topc @ sk_C @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94           = (sk_C))
% 0.77/0.94         | (v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))
% 0.77/0.94         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)) & 
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('demod', [status(thm)], ['242', '243'])).
% 0.77/0.94  thf('245', plain,
% 0.77/0.94      ((~ (v5_pre_topc @ sk_C @ sk_A @ sk_B_1))
% 0.77/0.94         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('split', [status(esa)], ['70'])).
% 0.77/0.94  thf('246', plain,
% 0.77/0.94      ((((u1_struct_0 @ (g1_pre_topc @ sk_C @ (u1_pre_topc @ sk_B_1))) = (sk_C)))
% 0.77/0.94         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)) & 
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('clc', [status(thm)], ['244', '245'])).
% 0.77/0.94  thf('247', plain,
% 0.77/0.94      ((((u1_struct_0 @ sk_B_1) = (sk_C)))
% 0.77/0.94         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)) & 
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('demod', [status(thm)], ['145', '153'])).
% 0.77/0.94  thf('248', plain,
% 0.77/0.94      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('249', plain,
% 0.77/0.94      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.77/0.94         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)) & 
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('sup+', [status(thm)], ['247', '248'])).
% 0.77/0.94  thf('250', plain,
% 0.77/0.94      (((v5_pre_topc @ sk_C @ sk_A @ 
% 0.77/0.94         (g1_pre_topc @ sk_C @ (u1_pre_topc @ sk_B_1))))
% 0.77/0.94         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)) & 
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('demod', [status(thm)], ['239', '246', '249'])).
% 0.77/0.94  thf('251', plain,
% 0.77/0.94      ((((sk_C) = (k1_xboole_0)))
% 0.77/0.94         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)) & 
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['146', '152'])).
% 0.77/0.94  thf('252', plain,
% 0.77/0.94      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.77/0.94         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)) & 
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('sup+', [status(thm)], ['247', '248'])).
% 0.77/0.94  thf('253', plain,
% 0.77/0.94      (((v5_pre_topc @ sk_C @ sk_A @ sk_B_1))
% 0.77/0.94         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)) & 
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('demod', [status(thm)], ['216', '250', '251', '252'])).
% 0.77/0.94  thf('254', plain,
% 0.77/0.94      ((~ (v5_pre_topc @ sk_C @ sk_A @ sk_B_1))
% 0.77/0.94         <= (~ ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('split', [status(esa)], ['70'])).
% 0.77/0.94  thf('255', plain,
% 0.77/0.94      (~
% 0.77/0.94       ((v5_pre_topc @ sk_D @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) | 
% 0.77/0.94       ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1))),
% 0.77/0.94      inference('sup-', [status(thm)], ['253', '254'])).
% 0.77/0.94  thf('256', plain,
% 0.77/0.94      (((v5_pre_topc @ sk_C @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 0.77/0.94         <= (((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('demod', [status(thm)], ['106', '107'])).
% 0.77/0.94  thf('257', plain,
% 0.77/0.94      ((~ (v5_pre_topc @ sk_C @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 0.77/0.94         <= (~
% 0.77/0.94             ((v5_pre_topc @ sk_C @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('split', [status(esa)], ['101'])).
% 0.77/0.94  thf('258', plain,
% 0.77/0.94      (~
% 0.77/0.94       ((v5_pre_topc @ sk_D @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) | 
% 0.77/0.94       ((v5_pre_topc @ sk_C @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['256', '257'])).
% 0.77/0.94  thf('259', plain,
% 0.77/0.94      (~
% 0.77/0.94       ((v5_pre_topc @ sk_D @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 0.77/0.94      inference('sat_resolution*', [status(thm)], ['98', '102', '255', '258'])).
% 0.77/0.94  thf('260', plain,
% 0.77/0.94      (((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)) | 
% 0.77/0.94       ((v5_pre_topc @ sk_C @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 0.77/0.94      inference('split', [status(esa)], ['95'])).
% 0.77/0.94  thf('261', plain, (((v5_pre_topc @ sk_C @ sk_A @ sk_B_1))),
% 0.77/0.94      inference('sat_resolution*', [status(thm)], ['98', '102', '255', '260'])).
% 0.77/0.94  thf('262', plain, (((sk_C) = (k1_xboole_0))),
% 0.77/0.94      inference('simpl_trail', [status(thm)], ['92', '259', '261'])).
% 0.77/0.94  thf('263', plain, (((sk_C) = (k1_xboole_0))),
% 0.77/0.94      inference('simpl_trail', [status(thm)], ['92', '259', '261'])).
% 0.77/0.94  thf('264', plain, (((sk_C) = (k1_xboole_0))),
% 0.77/0.94      inference('simpl_trail', [status(thm)], ['92', '259', '261'])).
% 0.77/0.94  thf('265', plain, (((sk_C) = (k1_xboole_0))),
% 0.77/0.94      inference('simpl_trail', [status(thm)], ['92', '259', '261'])).
% 0.77/0.94  thf('266', plain,
% 0.77/0.94      ((((u1_struct_0 @ sk_B_1) = (k1_xboole_0)))
% 0.77/0.94         <= (~
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) & 
% 0.77/0.94             ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('sup-', [status(thm)], ['69', '73'])).
% 0.77/0.94  thf('267', plain,
% 0.77/0.94      ((((sk_C) = (k1_xboole_0)))
% 0.77/0.94         <= (~
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) & 
% 0.77/0.94             ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('sup-', [status(thm)], ['82', '91'])).
% 0.77/0.94  thf('268', plain,
% 0.77/0.94      ((((u1_struct_0 @ sk_B_1) = (sk_C)))
% 0.77/0.94         <= (~
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) & 
% 0.77/0.94             ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('demod', [status(thm)], ['266', '267'])).
% 0.77/0.94  thf('269', plain,
% 0.77/0.94      (![X0 : $i]:
% 0.77/0.94         (~ (l1_pre_topc @ X0)
% 0.77/0.94          | (l1_pre_topc @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['1', '2'])).
% 0.77/0.94  thf('270', plain,
% 0.77/0.94      ((((l1_pre_topc @ (g1_pre_topc @ sk_C @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94         | ~ (l1_pre_topc @ sk_B_1)))
% 0.77/0.94         <= (~
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) & 
% 0.77/0.94             ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('sup+', [status(thm)], ['268', '269'])).
% 0.77/0.94  thf('271', plain, ((l1_pre_topc @ sk_B_1)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('272', plain,
% 0.77/0.94      (((l1_pre_topc @ (g1_pre_topc @ sk_C @ (u1_pre_topc @ sk_B_1))))
% 0.77/0.94         <= (~
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) & 
% 0.77/0.94             ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('demod', [status(thm)], ['270', '271'])).
% 0.77/0.94  thf('273', plain,
% 0.77/0.94      (~
% 0.77/0.94       ((v5_pre_topc @ sk_D @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 0.77/0.94      inference('sat_resolution*', [status(thm)], ['98', '102', '255', '258'])).
% 0.77/0.94  thf('274', plain, (((v5_pre_topc @ sk_C @ sk_A @ sk_B_1))),
% 0.77/0.94      inference('sat_resolution*', [status(thm)], ['98', '102', '255', '260'])).
% 0.77/0.94  thf('275', plain,
% 0.77/0.94      ((l1_pre_topc @ (g1_pre_topc @ sk_C @ (u1_pre_topc @ sk_B_1)))),
% 0.77/0.94      inference('simpl_trail', [status(thm)], ['272', '273', '274'])).
% 0.77/0.94  thf('276', plain, (((sk_C) = (k1_xboole_0))),
% 0.77/0.94      inference('simpl_trail', [status(thm)], ['92', '259', '261'])).
% 0.77/0.94  thf('277', plain,
% 0.77/0.94      ((((u1_struct_0 @ sk_B_1) = (sk_C)))
% 0.77/0.94         <= (~
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) & 
% 0.77/0.94             ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('demod', [status(thm)], ['266', '267'])).
% 0.77/0.94  thf('278', plain,
% 0.77/0.94      (![X41 : $i]:
% 0.77/0.94         ((v2_pre_topc @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ X41) @ (u1_pre_topc @ X41)))
% 0.77/0.94          | ~ (l1_pre_topc @ X41)
% 0.77/0.94          | ~ (v2_pre_topc @ X41))),
% 0.77/0.94      inference('cnf', [status(esa)], [fc6_pre_topc])).
% 0.77/0.94  thf('279', plain,
% 0.77/0.94      ((((v2_pre_topc @ (g1_pre_topc @ sk_C @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94         | ~ (v2_pre_topc @ sk_B_1)
% 0.77/0.94         | ~ (l1_pre_topc @ sk_B_1)))
% 0.77/0.94         <= (~
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) & 
% 0.77/0.94             ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('sup+', [status(thm)], ['277', '278'])).
% 0.77/0.94  thf('280', plain, ((v2_pre_topc @ sk_B_1)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('281', plain, ((l1_pre_topc @ sk_B_1)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('282', plain,
% 0.77/0.94      (((v2_pre_topc @ (g1_pre_topc @ sk_C @ (u1_pre_topc @ sk_B_1))))
% 0.77/0.94         <= (~
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) & 
% 0.77/0.94             ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('demod', [status(thm)], ['279', '280', '281'])).
% 0.77/0.94  thf('283', plain,
% 0.77/0.94      (~
% 0.77/0.94       ((v5_pre_topc @ sk_D @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 0.77/0.94      inference('sat_resolution*', [status(thm)], ['98', '102', '255', '258'])).
% 0.77/0.94  thf('284', plain, (((v5_pre_topc @ sk_C @ sk_A @ sk_B_1))),
% 0.77/0.94      inference('sat_resolution*', [status(thm)], ['98', '102', '255', '260'])).
% 0.77/0.94  thf('285', plain,
% 0.77/0.94      ((v2_pre_topc @ (g1_pre_topc @ sk_C @ (u1_pre_topc @ sk_B_1)))),
% 0.77/0.94      inference('simpl_trail', [status(thm)], ['282', '283', '284'])).
% 0.77/0.94  thf('286', plain,
% 0.77/0.94      (((~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.94            (u1_struct_0 @ (g1_pre_topc @ sk_C @ (u1_pre_topc @ sk_B_1))))
% 0.77/0.94         | (v5_pre_topc @ sk_C @ 
% 0.77/0.94            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94            (g1_pre_topc @ sk_C @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94         | ~ (v5_pre_topc @ sk_C @ sk_A @ 
% 0.77/0.94              (g1_pre_topc @ sk_C @ (u1_pre_topc @ sk_B_1)))))
% 0.77/0.94         <= (~
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) & 
% 0.77/0.94             ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('demod', [status(thm)],
% 0.77/0.94                ['81', '262', '263', '264', '265', '275', '276', '285'])).
% 0.77/0.94  thf('287', plain,
% 0.77/0.94      (~
% 0.77/0.94       ((v5_pre_topc @ sk_D @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 0.77/0.94      inference('sat_resolution*', [status(thm)], ['98', '102', '255', '258'])).
% 0.77/0.94  thf('288', plain, (((v5_pre_topc @ sk_C @ sk_A @ sk_B_1))),
% 0.77/0.94      inference('sat_resolution*', [status(thm)], ['98', '102', '255', '260'])).
% 0.77/0.94  thf('289', plain,
% 0.77/0.94      ((~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.94           (u1_struct_0 @ (g1_pre_topc @ sk_C @ (u1_pre_topc @ sk_B_1))))
% 0.77/0.94        | (v5_pre_topc @ sk_C @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94           (g1_pre_topc @ sk_C @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94        | ~ (v5_pre_topc @ sk_C @ sk_A @ 
% 0.77/0.94             (g1_pre_topc @ sk_C @ (u1_pre_topc @ sk_B_1))))),
% 0.77/0.94      inference('simpl_trail', [status(thm)], ['286', '287', '288'])).
% 0.77/0.94  thf('290', plain,
% 0.77/0.94      ((((u1_struct_0 @ sk_B_1) = (sk_C)))
% 0.77/0.94         <= (~
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) & 
% 0.77/0.94             ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('demod', [status(thm)], ['266', '267'])).
% 0.77/0.94  thf('291', plain,
% 0.77/0.94      ((~ (v5_pre_topc @ sk_C @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 0.77/0.94         <= (~
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('demod', [status(thm)], ['71', '72'])).
% 0.77/0.94  thf('292', plain,
% 0.77/0.94      ((~ (v5_pre_topc @ sk_C @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94           (g1_pre_topc @ sk_C @ (u1_pre_topc @ sk_B_1))))
% 0.77/0.94         <= (~
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) & 
% 0.77/0.94             ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('sup-', [status(thm)], ['290', '291'])).
% 0.77/0.94  thf('293', plain,
% 0.77/0.94      (~
% 0.77/0.94       ((v5_pre_topc @ sk_D @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 0.77/0.94      inference('sat_resolution*', [status(thm)], ['98', '102', '255', '258'])).
% 0.77/0.94  thf('294', plain, (((v5_pre_topc @ sk_C @ sk_A @ sk_B_1))),
% 0.77/0.94      inference('sat_resolution*', [status(thm)], ['98', '102', '255', '260'])).
% 0.77/0.94  thf('295', plain,
% 0.77/0.94      (~ (v5_pre_topc @ sk_C @ 
% 0.77/0.94          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94          (g1_pre_topc @ sk_C @ (u1_pre_topc @ sk_B_1)))),
% 0.77/0.94      inference('simpl_trail', [status(thm)], ['292', '293', '294'])).
% 0.77/0.94  thf('296', plain,
% 0.77/0.94      ((~ (v5_pre_topc @ sk_C @ sk_A @ 
% 0.77/0.94           (g1_pre_topc @ sk_C @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.94             (u1_struct_0 @ (g1_pre_topc @ sk_C @ (u1_pre_topc @ sk_B_1)))))),
% 0.77/0.94      inference('clc', [status(thm)], ['289', '295'])).
% 0.77/0.94  thf('297', plain,
% 0.77/0.94      ((((u1_struct_0 @ sk_B_1) = (sk_C)))
% 0.77/0.94         <= (~
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) & 
% 0.77/0.94             ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('demod', [status(thm)], ['266', '267'])).
% 0.77/0.94  thf('298', plain,
% 0.77/0.94      ((~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.94           (u1_struct_0 @ 
% 0.77/0.94            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 0.77/0.94        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B_1)
% 0.77/0.94        | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 0.77/0.94      inference('demod', [status(thm)],
% 0.77/0.94                ['36', '37', '38', '39', '40', '41', '42', '43'])).
% 0.77/0.94  thf('299', plain,
% 0.77/0.94      (((~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.94            (u1_struct_0 @ (g1_pre_topc @ sk_C @ (u1_pre_topc @ sk_B_1))))
% 0.77/0.94         | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.77/0.94            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94         | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))
% 0.77/0.94         <= (~
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) & 
% 0.77/0.94             ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('sup-', [status(thm)], ['297', '298'])).
% 0.77/0.94  thf('300', plain,
% 0.77/0.94      ((((u1_struct_0 @ sk_B_1) = (sk_C)))
% 0.77/0.94         <= (~
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) & 
% 0.77/0.94             ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('demod', [status(thm)], ['266', '267'])).
% 0.77/0.94  thf('301', plain,
% 0.77/0.94      (((v5_pre_topc @ sk_C @ sk_A @ sk_B_1))
% 0.77/0.94         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('split', [status(esa)], ['4'])).
% 0.77/0.94  thf('302', plain,
% 0.77/0.94      (((~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.94            (u1_struct_0 @ (g1_pre_topc @ sk_C @ (u1_pre_topc @ sk_B_1))))
% 0.77/0.94         | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.77/0.94            (g1_pre_topc @ sk_C @ (u1_pre_topc @ sk_B_1)))))
% 0.77/0.94         <= (~
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) & 
% 0.77/0.94             ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('demod', [status(thm)], ['299', '300', '301'])).
% 0.77/0.94  thf('303', plain,
% 0.77/0.94      (~
% 0.77/0.94       ((v5_pre_topc @ sk_D @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 0.77/0.94      inference('sat_resolution*', [status(thm)], ['98', '102', '255', '258'])).
% 0.77/0.94  thf('304', plain, (((v5_pre_topc @ sk_C @ sk_A @ sk_B_1))),
% 0.77/0.94      inference('sat_resolution*', [status(thm)], ['98', '102', '255', '260'])).
% 0.77/0.94  thf('305', plain,
% 0.77/0.94      ((~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.94           (u1_struct_0 @ (g1_pre_topc @ sk_C @ (u1_pre_topc @ sk_B_1))))
% 0.77/0.94        | (v5_pre_topc @ sk_C @ sk_A @ 
% 0.77/0.94           (g1_pre_topc @ sk_C @ (u1_pre_topc @ sk_B_1))))),
% 0.77/0.94      inference('simpl_trail', [status(thm)], ['302', '303', '304'])).
% 0.77/0.94  thf('306', plain,
% 0.77/0.94      (~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.94          (u1_struct_0 @ (g1_pre_topc @ sk_C @ (u1_pre_topc @ sk_B_1))))),
% 0.77/0.94      inference('clc', [status(thm)], ['296', '305'])).
% 0.77/0.94  thf('307', plain,
% 0.77/0.94      (![X41 : $i]:
% 0.77/0.94         ((v2_pre_topc @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ X41) @ (u1_pre_topc @ X41)))
% 0.77/0.94          | ~ (l1_pre_topc @ X41)
% 0.77/0.94          | ~ (v2_pre_topc @ X41))),
% 0.77/0.94      inference('cnf', [status(esa)], [fc6_pre_topc])).
% 0.77/0.94  thf('308', plain,
% 0.77/0.94      (![X0 : $i]:
% 0.77/0.94         (~ (l1_pre_topc @ X0)
% 0.77/0.94          | (l1_pre_topc @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['1', '2'])).
% 0.77/0.94  thf('309', plain,
% 0.77/0.94      (((v5_pre_topc @ sk_C @ sk_A @ sk_B_1))
% 0.77/0.94         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('split', [status(esa)], ['4'])).
% 0.77/0.94  thf('310', plain,
% 0.77/0.94      ((((u1_struct_0 @ 
% 0.77/0.94          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94          = (k1_xboole_0))
% 0.77/0.94        | (v1_funct_2 @ sk_C @ 
% 0.77/0.94           (u1_struct_0 @ 
% 0.77/0.94            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.77/0.94           (u1_struct_0 @ sk_B_1)))),
% 0.77/0.94      inference('sup-', [status(thm)], ['162', '177'])).
% 0.77/0.94  thf('311', plain,
% 0.77/0.94      ((m1_subset_1 @ sk_C @ 
% 0.77/0.94        (k1_zfmisc_1 @ 
% 0.77/0.94         (k2_zfmisc_1 @ 
% 0.77/0.94          (u1_struct_0 @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.77/0.94          (u1_struct_0 @ sk_B_1))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['169', '172'])).
% 0.77/0.94  thf('312', plain,
% 0.77/0.94      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.77/0.94         (~ (v2_pre_topc @ X44)
% 0.77/0.94          | ~ (l1_pre_topc @ X44)
% 0.77/0.94          | ~ (v1_funct_2 @ X43 @ (u1_struct_0 @ X44) @ (u1_struct_0 @ X42))
% 0.77/0.94          | ~ (m1_subset_1 @ X43 @ 
% 0.77/0.94               (k1_zfmisc_1 @ 
% 0.77/0.94                (k2_zfmisc_1 @ (u1_struct_0 @ X44) @ (u1_struct_0 @ X42))))
% 0.77/0.94          | (v5_pre_topc @ X43 @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ X44) @ (u1_pre_topc @ X44)) @ X42)
% 0.77/0.94          | ~ (v5_pre_topc @ X43 @ X44 @ X42)
% 0.77/0.94          | ~ (m1_subset_1 @ X43 @ 
% 0.77/0.94               (k1_zfmisc_1 @ 
% 0.77/0.94                (k2_zfmisc_1 @ 
% 0.77/0.94                 (u1_struct_0 @ 
% 0.77/0.94                  (g1_pre_topc @ (u1_struct_0 @ X44) @ (u1_pre_topc @ X44))) @ 
% 0.77/0.94                 (u1_struct_0 @ X42))))
% 0.77/0.94          | ~ (v1_funct_2 @ X43 @ 
% 0.77/0.94               (u1_struct_0 @ 
% 0.77/0.94                (g1_pre_topc @ (u1_struct_0 @ X44) @ (u1_pre_topc @ X44))) @ 
% 0.77/0.94               (u1_struct_0 @ X42))
% 0.77/0.94          | ~ (v1_funct_1 @ X43)
% 0.77/0.94          | ~ (l1_pre_topc @ X42)
% 0.77/0.94          | ~ (v2_pre_topc @ X42))),
% 0.77/0.94      inference('simplify', [status(thm)], ['49'])).
% 0.77/0.94  thf('313', plain,
% 0.77/0.94      ((~ (v2_pre_topc @ sk_B_1)
% 0.77/0.94        | ~ (l1_pre_topc @ sk_B_1)
% 0.77/0.94        | ~ (v1_funct_1 @ sk_C)
% 0.77/0.94        | ~ (v1_funct_2 @ sk_C @ 
% 0.77/0.94             (u1_struct_0 @ 
% 0.77/0.94              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.77/0.94             (u1_struct_0 @ sk_B_1))
% 0.77/0.94        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B_1)
% 0.77/0.94        | (v5_pre_topc @ sk_C @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_1)
% 0.77/0.94        | ~ (m1_subset_1 @ sk_C @ 
% 0.77/0.94             (k1_zfmisc_1 @ 
% 0.77/0.94              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))
% 0.77/0.94        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))
% 0.77/0.94        | ~ (l1_pre_topc @ sk_A)
% 0.77/0.94        | ~ (v2_pre_topc @ sk_A))),
% 0.77/0.94      inference('sup-', [status(thm)], ['311', '312'])).
% 0.77/0.94  thf('314', plain, ((v2_pre_topc @ sk_B_1)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('315', plain, ((l1_pre_topc @ sk_B_1)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('316', plain, ((v1_funct_1 @ sk_C)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('317', plain,
% 0.77/0.94      ((m1_subset_1 @ sk_C @ 
% 0.77/0.94        (k1_zfmisc_1 @ 
% 0.77/0.94         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))))),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('318', plain,
% 0.77/0.94      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('319', plain, ((l1_pre_topc @ sk_A)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('320', plain, ((v2_pre_topc @ sk_A)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('321', plain,
% 0.77/0.94      ((~ (v1_funct_2 @ sk_C @ 
% 0.77/0.94           (u1_struct_0 @ 
% 0.77/0.94            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.77/0.94           (u1_struct_0 @ sk_B_1))
% 0.77/0.94        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B_1)
% 0.77/0.94        | (v5_pre_topc @ sk_C @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_1))),
% 0.77/0.94      inference('demod', [status(thm)],
% 0.77/0.94                ['313', '314', '315', '316', '317', '318', '319', '320'])).
% 0.77/0.94  thf('322', plain,
% 0.77/0.94      ((((u1_struct_0 @ 
% 0.77/0.94          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94          = (k1_xboole_0))
% 0.77/0.94        | (v5_pre_topc @ sk_C @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_1)
% 0.77/0.94        | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B_1))),
% 0.77/0.94      inference('sup-', [status(thm)], ['310', '321'])).
% 0.77/0.94  thf('323', plain,
% 0.77/0.94      ((((v5_pre_topc @ sk_C @ 
% 0.77/0.94          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_1)
% 0.77/0.94         | ((u1_struct_0 @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94             = (k1_xboole_0))))
% 0.77/0.94         <= (((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('sup-', [status(thm)], ['309', '322'])).
% 0.77/0.94  thf('324', plain, (((v5_pre_topc @ sk_C @ sk_A @ sk_B_1))),
% 0.77/0.94      inference('sat_resolution*', [status(thm)], ['98', '102', '255', '260'])).
% 0.77/0.94  thf('325', plain,
% 0.77/0.94      (((v5_pre_topc @ sk_C @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_1)
% 0.77/0.94        | ((u1_struct_0 @ 
% 0.77/0.94            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94            = (k1_xboole_0)))),
% 0.77/0.94      inference('simpl_trail', [status(thm)], ['323', '324'])).
% 0.77/0.94  thf('326', plain,
% 0.77/0.94      ((((u1_struct_0 @ sk_B_1) = (sk_C)))
% 0.77/0.94         <= (~
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) & 
% 0.77/0.94             ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('demod', [status(thm)], ['266', '267'])).
% 0.77/0.94  thf('327', plain,
% 0.77/0.94      (~
% 0.77/0.94       ((v5_pre_topc @ sk_D @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 0.77/0.94      inference('sat_resolution*', [status(thm)], ['98', '102', '255', '258'])).
% 0.77/0.94  thf('328', plain, (((v5_pre_topc @ sk_C @ sk_A @ sk_B_1))),
% 0.77/0.94      inference('sat_resolution*', [status(thm)], ['98', '102', '255', '260'])).
% 0.77/0.94  thf('329', plain, (((u1_struct_0 @ sk_B_1) = (sk_C))),
% 0.77/0.94      inference('simpl_trail', [status(thm)], ['326', '327', '328'])).
% 0.77/0.94  thf('330', plain, (((sk_C) = (k1_xboole_0))),
% 0.77/0.94      inference('simpl_trail', [status(thm)], ['92', '259', '261'])).
% 0.77/0.94  thf('331', plain,
% 0.77/0.94      (((v5_pre_topc @ sk_C @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_1)
% 0.77/0.94        | ((u1_struct_0 @ (g1_pre_topc @ sk_C @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94            = (sk_C)))),
% 0.77/0.94      inference('demod', [status(thm)], ['325', '329', '330'])).
% 0.77/0.94  thf('332', plain,
% 0.77/0.94      ((((u1_struct_0 @ 
% 0.77/0.94          (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94          = (k1_xboole_0))
% 0.77/0.94        | (v1_partfun1 @ sk_C @ 
% 0.77/0.94           (u1_struct_0 @ 
% 0.77/0.94            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 0.77/0.94      inference('demod', [status(thm)], ['159', '160', '161'])).
% 0.77/0.94  thf('333', plain,
% 0.77/0.94      ((((sk_C) = (k1_xboole_0)))
% 0.77/0.94         <= (~
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) & 
% 0.77/0.94             ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('sup-', [status(thm)], ['82', '91'])).
% 0.77/0.94  thf(t4_subset_1, axiom,
% 0.77/0.94    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.77/0.94  thf('334', plain,
% 0.77/0.94      (![X3 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X3))),
% 0.77/0.94      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.77/0.94  thf('335', plain,
% 0.77/0.94      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.77/0.94         (~ (v1_funct_1 @ X32)
% 0.77/0.94          | ~ (v1_partfun1 @ X32 @ X33)
% 0.77/0.94          | (v1_funct_2 @ X32 @ X33 @ X34)
% 0.77/0.94          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.77/0.94      inference('cnf', [status(esa)], [cc1_funct_2])).
% 0.77/0.94  thf('336', plain,
% 0.77/0.94      (![X0 : $i, X1 : $i]:
% 0.77/0.94         ((v1_funct_2 @ k1_xboole_0 @ X1 @ X0)
% 0.77/0.94          | ~ (v1_partfun1 @ k1_xboole_0 @ X1)
% 0.77/0.94          | ~ (v1_funct_1 @ k1_xboole_0))),
% 0.77/0.94      inference('sup-', [status(thm)], ['334', '335'])).
% 0.77/0.94  thf('337', plain,
% 0.77/0.94      ((![X0 : $i, X1 : $i]:
% 0.77/0.94          (~ (v1_funct_1 @ sk_C)
% 0.77/0.94           | ~ (v1_partfun1 @ k1_xboole_0 @ X0)
% 0.77/0.94           | (v1_funct_2 @ k1_xboole_0 @ X0 @ X1)))
% 0.77/0.94         <= (~
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) & 
% 0.77/0.94             ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('sup-', [status(thm)], ['333', '336'])).
% 0.77/0.94  thf('338', plain, ((v1_funct_1 @ sk_C)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('339', plain,
% 0.77/0.94      ((((sk_C) = (k1_xboole_0)))
% 0.77/0.94         <= (~
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) & 
% 0.77/0.94             ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('sup-', [status(thm)], ['82', '91'])).
% 0.77/0.94  thf('340', plain,
% 0.77/0.94      ((((sk_C) = (k1_xboole_0)))
% 0.77/0.94         <= (~
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) & 
% 0.77/0.94             ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('sup-', [status(thm)], ['82', '91'])).
% 0.77/0.94  thf('341', plain,
% 0.77/0.94      ((![X0 : $i, X1 : $i]:
% 0.77/0.94          (~ (v1_partfun1 @ sk_C @ X0) | (v1_funct_2 @ sk_C @ X0 @ X1)))
% 0.77/0.94         <= (~
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) & 
% 0.77/0.94             ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('demod', [status(thm)], ['337', '338', '339', '340'])).
% 0.77/0.94  thf('342', plain,
% 0.77/0.94      ((![X0 : $i]:
% 0.77/0.94          (((u1_struct_0 @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94             = (k1_xboole_0))
% 0.77/0.94           | (v1_funct_2 @ sk_C @ 
% 0.77/0.94              (u1_struct_0 @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.77/0.94              X0)))
% 0.77/0.94         <= (~
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) & 
% 0.77/0.94             ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('sup-', [status(thm)], ['332', '341'])).
% 0.77/0.94  thf('343', plain,
% 0.77/0.94      ((((u1_struct_0 @ sk_B_1) = (sk_C)))
% 0.77/0.94         <= (~
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) & 
% 0.77/0.94             ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('demod', [status(thm)], ['266', '267'])).
% 0.77/0.94  thf('344', plain,
% 0.77/0.94      ((((sk_C) = (k1_xboole_0)))
% 0.77/0.94         <= (~
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) & 
% 0.77/0.94             ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('sup-', [status(thm)], ['82', '91'])).
% 0.77/0.94  thf('345', plain,
% 0.77/0.94      ((![X0 : $i]:
% 0.77/0.94          (((u1_struct_0 @ (g1_pre_topc @ sk_C @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94             = (sk_C))
% 0.77/0.94           | (v1_funct_2 @ sk_C @ 
% 0.77/0.94              (u1_struct_0 @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.77/0.94              X0)))
% 0.77/0.94         <= (~
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) & 
% 0.77/0.94             ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('demod', [status(thm)], ['342', '343', '344'])).
% 0.77/0.94  thf('346', plain,
% 0.77/0.94      (~
% 0.77/0.94       ((v5_pre_topc @ sk_D @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 0.77/0.94      inference('sat_resolution*', [status(thm)], ['98', '102', '255', '258'])).
% 0.77/0.94  thf('347', plain, (((v5_pre_topc @ sk_C @ sk_A @ sk_B_1))),
% 0.77/0.94      inference('sat_resolution*', [status(thm)], ['98', '102', '255', '260'])).
% 0.77/0.94  thf('348', plain,
% 0.77/0.94      (![X0 : $i]:
% 0.77/0.94         (((u1_struct_0 @ (g1_pre_topc @ sk_C @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94            = (sk_C))
% 0.77/0.94          | (v1_funct_2 @ sk_C @ 
% 0.77/0.94             (u1_struct_0 @ 
% 0.77/0.94              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.77/0.94             X0))),
% 0.77/0.94      inference('simpl_trail', [status(thm)], ['345', '346', '347'])).
% 0.77/0.94  thf('349', plain,
% 0.77/0.94      ((((u1_struct_0 @ sk_B_1) = (sk_C)))
% 0.77/0.94         <= (~
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) & 
% 0.77/0.94             ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('demod', [status(thm)], ['266', '267'])).
% 0.77/0.94  thf('350', plain,
% 0.77/0.94      ((m1_subset_1 @ sk_C @ 
% 0.77/0.94        (k1_zfmisc_1 @ 
% 0.77/0.94         (k2_zfmisc_1 @ 
% 0.77/0.94          (u1_struct_0 @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.77/0.94          (u1_struct_0 @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))))),
% 0.77/0.94      inference('demod', [status(thm)], ['13', '14'])).
% 0.77/0.94  thf('351', plain,
% 0.77/0.94      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.77/0.94         (~ (v2_pre_topc @ X48)
% 0.77/0.94          | ~ (l1_pre_topc @ X48)
% 0.77/0.94          | ~ (v1_funct_2 @ X47 @ (u1_struct_0 @ X48) @ (u1_struct_0 @ X46))
% 0.77/0.94          | ~ (m1_subset_1 @ X47 @ 
% 0.77/0.94               (k1_zfmisc_1 @ 
% 0.77/0.94                (k2_zfmisc_1 @ (u1_struct_0 @ X48) @ (u1_struct_0 @ X46))))
% 0.77/0.94          | (v5_pre_topc @ X47 @ X48 @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ X46) @ (u1_pre_topc @ X46)))
% 0.77/0.94          | ~ (v5_pre_topc @ X47 @ X48 @ X46)
% 0.77/0.94          | ~ (m1_subset_1 @ X47 @ 
% 0.77/0.94               (k1_zfmisc_1 @ 
% 0.77/0.94                (k2_zfmisc_1 @ (u1_struct_0 @ X48) @ 
% 0.77/0.94                 (u1_struct_0 @ 
% 0.77/0.94                  (g1_pre_topc @ (u1_struct_0 @ X46) @ (u1_pre_topc @ X46))))))
% 0.77/0.94          | ~ (v1_funct_2 @ X47 @ (u1_struct_0 @ X48) @ 
% 0.77/0.94               (u1_struct_0 @ 
% 0.77/0.94                (g1_pre_topc @ (u1_struct_0 @ X46) @ (u1_pre_topc @ X46))))
% 0.77/0.94          | ~ (v1_funct_1 @ X47)
% 0.77/0.94          | ~ (l1_pre_topc @ X46)
% 0.77/0.94          | ~ (v2_pre_topc @ X46))),
% 0.77/0.94      inference('simplify', [status(thm)], ['34'])).
% 0.77/0.94  thf('352', plain,
% 0.77/0.94      ((~ (v2_pre_topc @ sk_B_1)
% 0.77/0.94        | ~ (l1_pre_topc @ sk_B_1)
% 0.77/0.94        | ~ (v1_funct_1 @ sk_C)
% 0.77/0.94        | ~ (v1_funct_2 @ sk_C @ 
% 0.77/0.94             (u1_struct_0 @ 
% 0.77/0.94              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.77/0.94             (u1_struct_0 @ 
% 0.77/0.94              (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))
% 0.77/0.94        | ~ (v5_pre_topc @ sk_C @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94             sk_B_1)
% 0.77/0.94        | (v5_pre_topc @ sk_C @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94        | ~ (m1_subset_1 @ sk_C @ 
% 0.77/0.94             (k1_zfmisc_1 @ 
% 0.77/0.94              (k2_zfmisc_1 @ 
% 0.77/0.94               (u1_struct_0 @ 
% 0.77/0.94                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.77/0.94               (u1_struct_0 @ sk_B_1))))
% 0.77/0.94        | ~ (v1_funct_2 @ sk_C @ 
% 0.77/0.94             (u1_struct_0 @ 
% 0.77/0.94              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.77/0.94             (u1_struct_0 @ sk_B_1))
% 0.77/0.94        | ~ (l1_pre_topc @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.77/0.94        | ~ (v2_pre_topc @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['350', '351'])).
% 0.77/0.94  thf('353', plain, ((v2_pre_topc @ sk_B_1)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('354', plain, ((l1_pre_topc @ sk_B_1)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('355', plain, ((v1_funct_1 @ sk_C)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('356', plain,
% 0.77/0.94      ((v1_funct_2 @ sk_C @ 
% 0.77/0.94        (u1_struct_0 @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.77/0.94        (u1_struct_0 @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 0.77/0.94      inference('demod', [status(thm)], ['53', '54'])).
% 0.77/0.94  thf('357', plain,
% 0.77/0.94      ((m1_subset_1 @ sk_C @ 
% 0.77/0.94        (k1_zfmisc_1 @ 
% 0.77/0.94         (k2_zfmisc_1 @ 
% 0.77/0.94          (u1_struct_0 @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.77/0.94          (u1_struct_0 @ sk_B_1))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['169', '172'])).
% 0.77/0.94  thf('358', plain,
% 0.77/0.94      ((~ (v5_pre_topc @ sk_C @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B_1)
% 0.77/0.94        | (v5_pre_topc @ sk_C @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94        | ~ (v1_funct_2 @ sk_C @ 
% 0.77/0.94             (u1_struct_0 @ 
% 0.77/0.94              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.77/0.94             (u1_struct_0 @ sk_B_1))
% 0.77/0.94        | ~ (l1_pre_topc @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.77/0.94        | ~ (v2_pre_topc @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 0.77/0.94      inference('demod', [status(thm)],
% 0.77/0.94                ['352', '353', '354', '355', '356', '357'])).
% 0.77/0.94  thf('359', plain,
% 0.77/0.94      (((~ (v1_funct_2 @ sk_C @ 
% 0.77/0.94            (u1_struct_0 @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.77/0.94            sk_C)
% 0.77/0.94         | ~ (v2_pre_topc @ 
% 0.77/0.94              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.77/0.94         | ~ (l1_pre_topc @ 
% 0.77/0.94              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.77/0.94         | (v5_pre_topc @ sk_C @ 
% 0.77/0.94            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94            (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94         | ~ (v5_pre_topc @ sk_C @ 
% 0.77/0.94              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94              sk_B_1)))
% 0.77/0.94         <= (~
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) & 
% 0.77/0.94             ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('sup-', [status(thm)], ['349', '358'])).
% 0.77/0.94  thf('360', plain,
% 0.77/0.94      ((((u1_struct_0 @ sk_B_1) = (sk_C)))
% 0.77/0.94         <= (~
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) & 
% 0.77/0.94             ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('demod', [status(thm)], ['266', '267'])).
% 0.77/0.94  thf('361', plain,
% 0.77/0.94      (((~ (v1_funct_2 @ sk_C @ 
% 0.77/0.94            (u1_struct_0 @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.77/0.94            sk_C)
% 0.77/0.94         | ~ (v2_pre_topc @ 
% 0.77/0.94              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.77/0.94         | ~ (l1_pre_topc @ 
% 0.77/0.94              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.77/0.94         | (v5_pre_topc @ sk_C @ 
% 0.77/0.94            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94            (g1_pre_topc @ sk_C @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94         | ~ (v5_pre_topc @ sk_C @ 
% 0.77/0.94              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94              sk_B_1)))
% 0.77/0.94         <= (~
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) & 
% 0.77/0.94             ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('demod', [status(thm)], ['359', '360'])).
% 0.77/0.94  thf('362', plain,
% 0.77/0.94      (~
% 0.77/0.94       ((v5_pre_topc @ sk_D @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 0.77/0.94      inference('sat_resolution*', [status(thm)], ['98', '102', '255', '258'])).
% 0.77/0.94  thf('363', plain, (((v5_pre_topc @ sk_C @ sk_A @ sk_B_1))),
% 0.77/0.94      inference('sat_resolution*', [status(thm)], ['98', '102', '255', '260'])).
% 0.77/0.94  thf('364', plain,
% 0.77/0.94      ((~ (v1_funct_2 @ sk_C @ 
% 0.77/0.94           (u1_struct_0 @ 
% 0.77/0.94            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))) @ 
% 0.77/0.94           sk_C)
% 0.77/0.94        | ~ (v2_pre_topc @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.77/0.94        | ~ (l1_pre_topc @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.77/0.94        | (v5_pre_topc @ sk_C @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94           (g1_pre_topc @ sk_C @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94        | ~ (v5_pre_topc @ sk_C @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94             sk_B_1))),
% 0.77/0.94      inference('simpl_trail', [status(thm)], ['361', '362', '363'])).
% 0.77/0.94  thf('365', plain,
% 0.77/0.94      ((((u1_struct_0 @ (g1_pre_topc @ sk_C @ (u1_pre_topc @ sk_B_1))) = (sk_C))
% 0.77/0.94        | ~ (v5_pre_topc @ sk_C @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94             sk_B_1)
% 0.77/0.94        | (v5_pre_topc @ sk_C @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94           (g1_pre_topc @ sk_C @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94        | ~ (l1_pre_topc @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.77/0.94        | ~ (v2_pre_topc @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['348', '364'])).
% 0.77/0.94  thf('366', plain,
% 0.77/0.94      ((((u1_struct_0 @ (g1_pre_topc @ sk_C @ (u1_pre_topc @ sk_B_1))) = (sk_C))
% 0.77/0.94        | ~ (v2_pre_topc @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.77/0.94        | ~ (l1_pre_topc @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.77/0.94        | (v5_pre_topc @ sk_C @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94           (g1_pre_topc @ sk_C @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94        | ((u1_struct_0 @ (g1_pre_topc @ sk_C @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94            = (sk_C)))),
% 0.77/0.94      inference('sup-', [status(thm)], ['331', '365'])).
% 0.77/0.94  thf('367', plain,
% 0.77/0.94      (((v5_pre_topc @ sk_C @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94         (g1_pre_topc @ sk_C @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94        | ~ (l1_pre_topc @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.77/0.94        | ~ (v2_pre_topc @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.77/0.94        | ((u1_struct_0 @ (g1_pre_topc @ sk_C @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94            = (sk_C)))),
% 0.77/0.94      inference('simplify', [status(thm)], ['366'])).
% 0.77/0.94  thf('368', plain,
% 0.77/0.94      ((~ (l1_pre_topc @ sk_A)
% 0.77/0.94        | ((u1_struct_0 @ (g1_pre_topc @ sk_C @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94            = (sk_C))
% 0.77/0.94        | ~ (v2_pre_topc @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.77/0.94        | (v5_pre_topc @ sk_C @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94           (g1_pre_topc @ sk_C @ (u1_pre_topc @ sk_B_1))))),
% 0.77/0.94      inference('sup-', [status(thm)], ['308', '367'])).
% 0.77/0.94  thf('369', plain, ((l1_pre_topc @ sk_A)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('370', plain,
% 0.77/0.94      ((((u1_struct_0 @ (g1_pre_topc @ sk_C @ (u1_pre_topc @ sk_B_1))) = (sk_C))
% 0.77/0.94        | ~ (v2_pre_topc @ 
% 0.77/0.94             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.77/0.94        | (v5_pre_topc @ sk_C @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94           (g1_pre_topc @ sk_C @ (u1_pre_topc @ sk_B_1))))),
% 0.77/0.94      inference('demod', [status(thm)], ['368', '369'])).
% 0.77/0.94  thf('371', plain,
% 0.77/0.94      (~ (v5_pre_topc @ sk_C @ 
% 0.77/0.94          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94          (g1_pre_topc @ sk_C @ (u1_pre_topc @ sk_B_1)))),
% 0.77/0.94      inference('simpl_trail', [status(thm)], ['292', '293', '294'])).
% 0.77/0.94  thf('372', plain,
% 0.77/0.94      ((~ (v2_pre_topc @ 
% 0.77/0.94           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.77/0.94        | ((u1_struct_0 @ (g1_pre_topc @ sk_C @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94            = (sk_C)))),
% 0.77/0.94      inference('clc', [status(thm)], ['370', '371'])).
% 0.77/0.94  thf('373', plain,
% 0.77/0.94      ((~ (v2_pre_topc @ sk_A)
% 0.77/0.94        | ~ (l1_pre_topc @ sk_A)
% 0.77/0.94        | ((u1_struct_0 @ (g1_pre_topc @ sk_C @ (u1_pre_topc @ sk_B_1)))
% 0.77/0.94            = (sk_C)))),
% 0.77/0.94      inference('sup-', [status(thm)], ['307', '372'])).
% 0.77/0.94  thf('374', plain, ((v2_pre_topc @ sk_A)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('375', plain, ((l1_pre_topc @ sk_A)),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('376', plain,
% 0.77/0.94      (((u1_struct_0 @ (g1_pre_topc @ sk_C @ (u1_pre_topc @ sk_B_1))) = (sk_C))),
% 0.77/0.94      inference('demod', [status(thm)], ['373', '374', '375'])).
% 0.77/0.94  thf('377', plain,
% 0.77/0.94      ((((u1_struct_0 @ sk_B_1) = (sk_C)))
% 0.77/0.94         <= (~
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) & 
% 0.77/0.94             ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('demod', [status(thm)], ['266', '267'])).
% 0.77/0.94  thf('378', plain,
% 0.77/0.94      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 0.77/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.94  thf('379', plain,
% 0.77/0.94      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.77/0.94         <= (~
% 0.77/0.94             ((v5_pre_topc @ sk_D @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94               (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))) & 
% 0.77/0.94             ((v5_pre_topc @ sk_C @ sk_A @ sk_B_1)))),
% 0.77/0.94      inference('sup+', [status(thm)], ['377', '378'])).
% 0.77/0.94  thf('380', plain,
% 0.77/0.94      (~
% 0.77/0.94       ((v5_pre_topc @ sk_D @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.77/0.94         (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1))))),
% 0.77/0.94      inference('sat_resolution*', [status(thm)], ['98', '102', '255', '258'])).
% 0.77/0.94  thf('381', plain, (((v5_pre_topc @ sk_C @ sk_A @ sk_B_1))),
% 0.77/0.94      inference('sat_resolution*', [status(thm)], ['98', '102', '255', '260'])).
% 0.77/0.94  thf('382', plain, ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ sk_C)),
% 0.77/0.94      inference('simpl_trail', [status(thm)], ['379', '380', '381'])).
% 0.77/0.94  thf('383', plain, ($false),
% 0.77/0.94      inference('demod', [status(thm)], ['306', '376', '382'])).
% 0.77/0.94  
% 0.77/0.94  % SZS output end Refutation
% 0.77/0.94  
% 0.77/0.95  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
