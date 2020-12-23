%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ylX1b354zs

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:43 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 780 expanded)
%              Number of leaves         :   44 ( 243 expanded)
%              Depth                    :   22
%              Number of atoms          : 1428 (19722 expanded)
%              Number of equality atoms :   33 ( 342 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

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
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_pre_topc @ X38 @ X39 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X38 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('8',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t4_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) )
              <=> ( m1_pre_topc @ B @ C ) ) ) ) ) )).

thf('14',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_pre_topc @ X40 @ X41 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X40 ) @ ( u1_struct_0 @ X42 ) )
      | ( m1_pre_topc @ X40 @ X42 )
      | ~ ( m1_pre_topc @ X42 @ X41 )
      | ~ ( l1_pre_topc @ X41 )
      | ~ ( v2_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_pre_topc @ X0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( m1_pre_topc @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_pre_topc @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['17','18','19'])).

thf(t11_tmap_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
            & ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) )).

thf('21',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_pre_topc @ X33 @ X34 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X33 ) @ ( u1_pre_topc @ X33 ) ) @ X34 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t11_tmap_1])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('24',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( l1_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('25',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) @ sk_C ),
    inference(demod,[status(thm)],['22','27'])).

thf('29',plain,
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

thf('30',plain,(
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

thf('31',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X36 )
      | ~ ( l1_pre_topc @ X36 )
      | ( m1_pre_topc @ X36 @ X37 )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X36 ) @ ( u1_pre_topc @ X36 ) ) @ X37 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X36 ) @ ( u1_pre_topc @ X36 ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X36 ) @ ( u1_pre_topc @ X36 ) ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) @ X0 )
      | ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_pre_topc @ X33 @ X34 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X33 ) @ ( u1_pre_topc @ X33 ) ) @ X34 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t11_tmap_1])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( l1_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('39',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc6_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
        & ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('44',plain,(
    ! [X22: $i] :
      ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X22 ) @ ( u1_pre_topc @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf('45',plain,
    ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) )
    | ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C ) @ ( u1_pre_topc @ sk_C ) ) @ X0 )
      | ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['32','41','42','48','49','50','51'])).

thf('53',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( m1_pre_topc @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['28','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['25','26'])).

thf('55',plain,(
    m1_pre_topc @ sk_B @ sk_C ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_pre_topc @ X38 @ X39 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X38 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('57',plain,
    ( ~ ( l1_pre_topc @ sk_C )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['25','26'])).

thf('59',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('61',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['10','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','62'])).

thf('64',plain,(
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

thf('65',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( r1_funct_2 @ X23 @ X24 @ X25 @ X26 @ X27 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X23 @ X24 )
      | ~ ( v1_funct_1 @ X27 )
      | ( v1_xboole_0 @ X26 )
      | ( v1_xboole_0 @ X24 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_2 @ X28 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r1_funct_2])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X1 @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ X1 @ X0 @ sk_D @ sk_D ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X1 @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ( r1_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ X1 @ X0 @ sk_D @ sk_D ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['10','61'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X1 @ X0 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ X1 @ X0 @ sk_D @ sk_D ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','71'])).

thf('73',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['10','61'])).

thf('76',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','73','76'])).

thf('78',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
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

thf('82',plain,(
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

thf('83',plain,(
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
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('89',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ( ( k2_partfun1 @ X15 @ X16 @ X14 @ X17 )
        = ( k7_relat_1 @ X14 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['83','84','85','86','87','92','93','94'])).

thf('96',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['80','95'])).

thf('97',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C )
    = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['79','100'])).

thf('102',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['10','61'])).

thf('103',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('105',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v4_relat_1 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('106',plain,(
    v4_relat_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('107',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X6
        = ( k7_relat_1 @ X6 @ X7 ) )
      | ~ ( v4_relat_1 @ X6 @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('108',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('110',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('111',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['108','111'])).

thf('113',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['10','61'])).

thf('114',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ),
    inference(demod,[status(thm)],['103','114'])).

thf('116',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['78','115'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('117',plain,(
    ! [X21: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('118',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('120',plain,(
    ! [X18: $i] :
      ( ( l1_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('121',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['118','121'])).

thf('123',plain,(
    $false ),
    inference(demod,[status(thm)],['0','122'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ylX1b354zs
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:57:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.57  % Solved by: fo/fo7.sh
% 0.22/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.57  % done 184 iterations in 0.106s
% 0.22/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.57  % SZS output start Refutation
% 0.22/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.57  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.57  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.57  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.22/0.57  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 0.22/0.57  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.22/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.57  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.22/0.57  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.22/0.57  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.57  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.22/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.57  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.22/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.57  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.57  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.22/0.57  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.22/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.57  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.22/0.57  thf(t60_tmap_1, conjecture,
% 0.22/0.57    (![A:$i]:
% 0.22/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.57       ( ![B:$i]:
% 0.22/0.57         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.57             ( l1_pre_topc @ B ) ) =>
% 0.22/0.57           ( ![C:$i]:
% 0.22/0.57             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.22/0.57               ( ![D:$i]:
% 0.22/0.57                 ( ( ( v1_funct_1 @ D ) & 
% 0.22/0.57                     ( v1_funct_2 @
% 0.22/0.57                       D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.22/0.57                     ( m1_subset_1 @
% 0.22/0.57                       D @ 
% 0.22/0.57                       ( k1_zfmisc_1 @
% 0.22/0.57                         ( k2_zfmisc_1 @
% 0.22/0.57                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.22/0.57                   ( ( ( g1_pre_topc @
% 0.22/0.57                         ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.22/0.57                       ( g1_pre_topc @
% 0.22/0.57                         ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.22/0.57                     ( r1_funct_2 @
% 0.22/0.57                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.22/0.57                       ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ 
% 0.22/0.57                       ( k2_tmap_1 @ B @ A @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.57    (~( ![A:$i]:
% 0.22/0.57        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.57            ( l1_pre_topc @ A ) ) =>
% 0.22/0.57          ( ![B:$i]:
% 0.22/0.57            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.57                ( l1_pre_topc @ B ) ) =>
% 0.22/0.57              ( ![C:$i]:
% 0.22/0.57                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.22/0.57                  ( ![D:$i]:
% 0.22/0.57                    ( ( ( v1_funct_1 @ D ) & 
% 0.22/0.57                        ( v1_funct_2 @
% 0.22/0.57                          D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.22/0.57                        ( m1_subset_1 @
% 0.22/0.57                          D @ 
% 0.22/0.57                          ( k1_zfmisc_1 @
% 0.22/0.57                            ( k2_zfmisc_1 @
% 0.22/0.57                              ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.22/0.57                      ( ( ( g1_pre_topc @
% 0.22/0.57                            ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.22/0.57                          ( g1_pre_topc @
% 0.22/0.57                            ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.22/0.57                        ( r1_funct_2 @
% 0.22/0.57                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.22/0.57                          ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ 
% 0.22/0.57                          ( k2_tmap_1 @ B @ A @ D @ C ) ) ) ) ) ) ) ) ) ) )),
% 0.22/0.57    inference('cnf.neg', [status(esa)], [t60_tmap_1])).
% 0.22/0.57  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('1', plain,
% 0.22/0.57      ((m1_subset_1 @ sk_D @ 
% 0.22/0.57        (k1_zfmisc_1 @ 
% 0.22/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('2', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(t1_tsep_1, axiom,
% 0.22/0.57    (![A:$i]:
% 0.22/0.57     ( ( l1_pre_topc @ A ) =>
% 0.22/0.57       ( ![B:$i]:
% 0.22/0.57         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.57           ( m1_subset_1 @
% 0.22/0.57             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.22/0.57  thf('3', plain,
% 0.22/0.57      (![X38 : $i, X39 : $i]:
% 0.22/0.57         (~ (m1_pre_topc @ X38 @ X39)
% 0.22/0.57          | (m1_subset_1 @ (u1_struct_0 @ X38) @ 
% 0.22/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 0.22/0.57          | ~ (l1_pre_topc @ X39))),
% 0.22/0.57      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.22/0.57  thf('4', plain,
% 0.22/0.57      ((~ (l1_pre_topc @ sk_B)
% 0.22/0.57        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.22/0.57           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.22/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.57  thf('5', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('6', plain,
% 0.22/0.57      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.22/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.57      inference('demod', [status(thm)], ['4', '5'])).
% 0.22/0.57  thf(t3_subset, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.57  thf('7', plain,
% 0.22/0.57      (![X3 : $i, X4 : $i]:
% 0.22/0.57         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.22/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.57  thf('8', plain, ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.22/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.57  thf(d10_xboole_0, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.57  thf('9', plain,
% 0.22/0.57      (![X0 : $i, X2 : $i]:
% 0.22/0.57         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.22/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.57  thf('10', plain,
% 0.22/0.57      ((~ (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))
% 0.22/0.57        | ((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.57  thf('11', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('12', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.22/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.57  thf('13', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.22/0.57      inference('simplify', [status(thm)], ['12'])).
% 0.22/0.57  thf(t4_tsep_1, axiom,
% 0.22/0.57    (![A:$i]:
% 0.22/0.57     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.57       ( ![B:$i]:
% 0.22/0.57         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.57           ( ![C:$i]:
% 0.22/0.57             ( ( m1_pre_topc @ C @ A ) =>
% 0.22/0.57               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 0.22/0.57                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 0.22/0.57  thf('14', plain,
% 0.22/0.57      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.22/0.57         (~ (m1_pre_topc @ X40 @ X41)
% 0.22/0.57          | ~ (r1_tarski @ (u1_struct_0 @ X40) @ (u1_struct_0 @ X42))
% 0.22/0.57          | (m1_pre_topc @ X40 @ X42)
% 0.22/0.57          | ~ (m1_pre_topc @ X42 @ X41)
% 0.22/0.57          | ~ (l1_pre_topc @ X41)
% 0.22/0.57          | ~ (v2_pre_topc @ X41))),
% 0.22/0.57      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.22/0.57  thf('15', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         (~ (v2_pre_topc @ X1)
% 0.22/0.57          | ~ (l1_pre_topc @ X1)
% 0.22/0.57          | ~ (m1_pre_topc @ X0 @ X1)
% 0.22/0.57          | (m1_pre_topc @ X0 @ X0)
% 0.22/0.57          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.22/0.57      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.57  thf('16', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         ((m1_pre_topc @ X0 @ X0)
% 0.22/0.57          | ~ (m1_pre_topc @ X0 @ X1)
% 0.22/0.57          | ~ (l1_pre_topc @ X1)
% 0.22/0.57          | ~ (v2_pre_topc @ X1))),
% 0.22/0.57      inference('simplify', [status(thm)], ['15'])).
% 0.22/0.57  thf('17', plain,
% 0.22/0.57      ((~ (v2_pre_topc @ sk_B)
% 0.22/0.57        | ~ (l1_pre_topc @ sk_B)
% 0.22/0.57        | (m1_pre_topc @ sk_C @ sk_C))),
% 0.22/0.57      inference('sup-', [status(thm)], ['11', '16'])).
% 0.22/0.57  thf('18', plain, ((v2_pre_topc @ sk_B)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('19', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('20', plain, ((m1_pre_topc @ sk_C @ sk_C)),
% 0.22/0.57      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.22/0.57  thf(t11_tmap_1, axiom,
% 0.22/0.57    (![A:$i]:
% 0.22/0.57     ( ( l1_pre_topc @ A ) =>
% 0.22/0.57       ( ![B:$i]:
% 0.22/0.57         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.57           ( ( v1_pre_topc @
% 0.22/0.57               ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.22/0.57             ( m1_pre_topc @
% 0.22/0.57               ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) ))).
% 0.22/0.57  thf('21', plain,
% 0.22/0.57      (![X33 : $i, X34 : $i]:
% 0.22/0.57         (~ (m1_pre_topc @ X33 @ X34)
% 0.22/0.57          | (m1_pre_topc @ 
% 0.22/0.57             (g1_pre_topc @ (u1_struct_0 @ X33) @ (u1_pre_topc @ X33)) @ X34)
% 0.22/0.57          | ~ (l1_pre_topc @ X34))),
% 0.22/0.57      inference('cnf', [status(esa)], [t11_tmap_1])).
% 0.22/0.57  thf('22', plain,
% 0.22/0.57      ((~ (l1_pre_topc @ sk_C)
% 0.22/0.57        | (m1_pre_topc @ 
% 0.22/0.57           (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ sk_C))),
% 0.22/0.57      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.57  thf('23', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(dt_m1_pre_topc, axiom,
% 0.22/0.57    (![A:$i]:
% 0.22/0.57     ( ( l1_pre_topc @ A ) =>
% 0.22/0.57       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.22/0.57  thf('24', plain,
% 0.22/0.57      (![X19 : $i, X20 : $i]:
% 0.22/0.57         (~ (m1_pre_topc @ X19 @ X20)
% 0.22/0.57          | (l1_pre_topc @ X19)
% 0.22/0.57          | ~ (l1_pre_topc @ X20))),
% 0.22/0.57      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.22/0.57  thf('25', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_C))),
% 0.22/0.57      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.57  thf('26', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('27', plain, ((l1_pre_topc @ sk_C)),
% 0.22/0.57      inference('demod', [status(thm)], ['25', '26'])).
% 0.22/0.57  thf('28', plain,
% 0.22/0.57      ((m1_pre_topc @ 
% 0.22/0.57        (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ sk_C)),
% 0.22/0.57      inference('demod', [status(thm)], ['22', '27'])).
% 0.22/0.57  thf('29', plain,
% 0.22/0.57      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.22/0.57         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(t12_tmap_1, axiom,
% 0.22/0.57    (![A:$i]:
% 0.22/0.57     ( ( l1_pre_topc @ A ) =>
% 0.22/0.57       ( ![B:$i]:
% 0.22/0.57         ( ( ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) ) =>
% 0.22/0.57           ( ![C:$i]:
% 0.22/0.57             ( ( ( v2_pre_topc @ C ) & ( l1_pre_topc @ C ) ) =>
% 0.22/0.57               ( ( ( B ) =
% 0.22/0.57                   ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) =>
% 0.22/0.57                 ( ( m1_pre_topc @ B @ A ) <=> ( m1_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.22/0.57  thf('30', plain,
% 0.22/0.57      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.22/0.57         (~ (v2_pre_topc @ X35)
% 0.22/0.57          | ~ (l1_pre_topc @ X35)
% 0.22/0.57          | ((X35) != (g1_pre_topc @ (u1_struct_0 @ X36) @ (u1_pre_topc @ X36)))
% 0.22/0.57          | ~ (m1_pre_topc @ X35 @ X37)
% 0.22/0.57          | (m1_pre_topc @ X36 @ X37)
% 0.22/0.57          | ~ (l1_pre_topc @ X36)
% 0.22/0.57          | ~ (v2_pre_topc @ X36)
% 0.22/0.57          | ~ (l1_pre_topc @ X37))),
% 0.22/0.57      inference('cnf', [status(esa)], [t12_tmap_1])).
% 0.22/0.57  thf('31', plain,
% 0.22/0.57      (![X36 : $i, X37 : $i]:
% 0.22/0.57         (~ (l1_pre_topc @ X37)
% 0.22/0.57          | ~ (v2_pre_topc @ X36)
% 0.22/0.57          | ~ (l1_pre_topc @ X36)
% 0.22/0.57          | (m1_pre_topc @ X36 @ X37)
% 0.22/0.57          | ~ (m1_pre_topc @ 
% 0.22/0.57               (g1_pre_topc @ (u1_struct_0 @ X36) @ (u1_pre_topc @ X36)) @ X37)
% 0.22/0.57          | ~ (l1_pre_topc @ 
% 0.22/0.57               (g1_pre_topc @ (u1_struct_0 @ X36) @ (u1_pre_topc @ X36)))
% 0.22/0.57          | ~ (v2_pre_topc @ 
% 0.22/0.57               (g1_pre_topc @ (u1_struct_0 @ X36) @ (u1_pre_topc @ X36))))),
% 0.22/0.57      inference('simplify', [status(thm)], ['30'])).
% 0.22/0.57  thf('32', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         (~ (l1_pre_topc @ 
% 0.22/0.57             (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.22/0.57          | ~ (v2_pre_topc @ 
% 0.22/0.57               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.22/0.57          | ~ (m1_pre_topc @ 
% 0.22/0.57               (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)) @ X0)
% 0.22/0.57          | (m1_pre_topc @ sk_B @ X0)
% 0.22/0.57          | ~ (l1_pre_topc @ sk_B)
% 0.22/0.57          | ~ (v2_pre_topc @ sk_B)
% 0.22/0.57          | ~ (l1_pre_topc @ X0))),
% 0.22/0.57      inference('sup-', [status(thm)], ['29', '31'])).
% 0.22/0.57  thf('33', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('34', plain,
% 0.22/0.57      (![X33 : $i, X34 : $i]:
% 0.22/0.57         (~ (m1_pre_topc @ X33 @ X34)
% 0.22/0.57          | (m1_pre_topc @ 
% 0.22/0.57             (g1_pre_topc @ (u1_struct_0 @ X33) @ (u1_pre_topc @ X33)) @ X34)
% 0.22/0.57          | ~ (l1_pre_topc @ X34))),
% 0.22/0.57      inference('cnf', [status(esa)], [t11_tmap_1])).
% 0.22/0.57  thf('35', plain,
% 0.22/0.57      ((~ (l1_pre_topc @ sk_B)
% 0.22/0.57        | (m1_pre_topc @ 
% 0.22/0.57           (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ sk_B))),
% 0.22/0.57      inference('sup-', [status(thm)], ['33', '34'])).
% 0.22/0.57  thf('36', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('37', plain,
% 0.22/0.57      ((m1_pre_topc @ 
% 0.22/0.57        (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ sk_B)),
% 0.22/0.57      inference('demod', [status(thm)], ['35', '36'])).
% 0.22/0.57  thf('38', plain,
% 0.22/0.57      (![X19 : $i, X20 : $i]:
% 0.22/0.57         (~ (m1_pre_topc @ X19 @ X20)
% 0.22/0.57          | (l1_pre_topc @ X19)
% 0.22/0.57          | ~ (l1_pre_topc @ X20))),
% 0.22/0.57      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.22/0.57  thf('39', plain,
% 0.22/0.57      ((~ (l1_pre_topc @ sk_B)
% 0.22/0.57        | (l1_pre_topc @ 
% 0.22/0.57           (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))))),
% 0.22/0.57      inference('sup-', [status(thm)], ['37', '38'])).
% 0.22/0.57  thf('40', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('41', plain,
% 0.22/0.57      ((l1_pre_topc @ 
% 0.22/0.57        (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.22/0.57      inference('demod', [status(thm)], ['39', '40'])).
% 0.22/0.57  thf('42', plain,
% 0.22/0.57      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.22/0.57         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('43', plain,
% 0.22/0.57      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.22/0.57         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(fc6_pre_topc, axiom,
% 0.22/0.57    (![A:$i]:
% 0.22/0.57     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.57       ( ( v1_pre_topc @
% 0.22/0.57           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.22/0.57         ( v2_pre_topc @
% 0.22/0.57           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.22/0.57  thf('44', plain,
% 0.22/0.57      (![X22 : $i]:
% 0.22/0.57         ((v2_pre_topc @ 
% 0.22/0.57           (g1_pre_topc @ (u1_struct_0 @ X22) @ (u1_pre_topc @ X22)))
% 0.22/0.57          | ~ (l1_pre_topc @ X22)
% 0.22/0.57          | ~ (v2_pre_topc @ X22))),
% 0.22/0.57      inference('cnf', [status(esa)], [fc6_pre_topc])).
% 0.22/0.57  thf('45', plain,
% 0.22/0.57      (((v2_pre_topc @ 
% 0.22/0.57         (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))
% 0.22/0.57        | ~ (v2_pre_topc @ sk_B)
% 0.22/0.57        | ~ (l1_pre_topc @ sk_B))),
% 0.22/0.57      inference('sup+', [status(thm)], ['43', '44'])).
% 0.22/0.57  thf('46', plain, ((v2_pre_topc @ sk_B)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('47', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('48', plain,
% 0.22/0.57      ((v2_pre_topc @ 
% 0.22/0.57        (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)))),
% 0.22/0.57      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.22/0.57  thf('49', plain,
% 0.22/0.57      (((g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C))
% 0.22/0.57         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('50', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('51', plain, ((v2_pre_topc @ sk_B)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('52', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         (~ (m1_pre_topc @ 
% 0.22/0.57             (g1_pre_topc @ (u1_struct_0 @ sk_C) @ (u1_pre_topc @ sk_C)) @ X0)
% 0.22/0.57          | (m1_pre_topc @ sk_B @ X0)
% 0.22/0.57          | ~ (l1_pre_topc @ X0))),
% 0.22/0.57      inference('demod', [status(thm)],
% 0.22/0.57                ['32', '41', '42', '48', '49', '50', '51'])).
% 0.22/0.57  thf('53', plain, ((~ (l1_pre_topc @ sk_C) | (m1_pre_topc @ sk_B @ sk_C))),
% 0.22/0.57      inference('sup-', [status(thm)], ['28', '52'])).
% 0.22/0.57  thf('54', plain, ((l1_pre_topc @ sk_C)),
% 0.22/0.57      inference('demod', [status(thm)], ['25', '26'])).
% 0.22/0.57  thf('55', plain, ((m1_pre_topc @ sk_B @ sk_C)),
% 0.22/0.57      inference('demod', [status(thm)], ['53', '54'])).
% 0.22/0.57  thf('56', plain,
% 0.22/0.57      (![X38 : $i, X39 : $i]:
% 0.22/0.57         (~ (m1_pre_topc @ X38 @ X39)
% 0.22/0.57          | (m1_subset_1 @ (u1_struct_0 @ X38) @ 
% 0.22/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 0.22/0.57          | ~ (l1_pre_topc @ X39))),
% 0.22/0.57      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.22/0.57  thf('57', plain,
% 0.22/0.57      ((~ (l1_pre_topc @ sk_C)
% 0.22/0.57        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.57           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C))))),
% 0.22/0.57      inference('sup-', [status(thm)], ['55', '56'])).
% 0.22/0.57  thf('58', plain, ((l1_pre_topc @ sk_C)),
% 0.22/0.57      inference('demod', [status(thm)], ['25', '26'])).
% 0.22/0.57  thf('59', plain,
% 0.22/0.57      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.22/0.57      inference('demod', [status(thm)], ['57', '58'])).
% 0.22/0.57  thf('60', plain,
% 0.22/0.57      (![X3 : $i, X4 : $i]:
% 0.22/0.57         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.22/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.57  thf('61', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C))),
% 0.22/0.57      inference('sup-', [status(thm)], ['59', '60'])).
% 0.22/0.57  thf('62', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.22/0.57      inference('demod', [status(thm)], ['10', '61'])).
% 0.22/0.57  thf('63', plain,
% 0.22/0.57      ((m1_subset_1 @ sk_D @ 
% 0.22/0.57        (k1_zfmisc_1 @ 
% 0.22/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.57      inference('demod', [status(thm)], ['1', '62'])).
% 0.22/0.57  thf('64', plain,
% 0.22/0.57      ((m1_subset_1 @ sk_D @ 
% 0.22/0.57        (k1_zfmisc_1 @ 
% 0.22/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(reflexivity_r1_funct_2, axiom,
% 0.22/0.57    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.22/0.57     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 0.22/0.57         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 0.22/0.57         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.22/0.57         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 0.22/0.57         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.22/0.57       ( r1_funct_2 @ A @ B @ C @ D @ E @ E ) ))).
% 0.22/0.57  thf('65', plain,
% 0.22/0.57      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.22/0.57         ((r1_funct_2 @ X23 @ X24 @ X25 @ X26 @ X27 @ X27)
% 0.22/0.57          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.22/0.57          | ~ (v1_funct_2 @ X27 @ X23 @ X24)
% 0.22/0.57          | ~ (v1_funct_1 @ X27)
% 0.22/0.57          | (v1_xboole_0 @ X26)
% 0.22/0.57          | (v1_xboole_0 @ X24)
% 0.22/0.57          | ~ (v1_funct_1 @ X28)
% 0.22/0.57          | ~ (v1_funct_2 @ X28 @ X25 @ X26)
% 0.22/0.57          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.22/0.57      inference('cnf', [status(esa)], [reflexivity_r1_funct_2])).
% 0.22/0.57  thf('66', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.57         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.22/0.57          | ~ (v1_funct_2 @ X2 @ X1 @ X0)
% 0.22/0.57          | ~ (v1_funct_1 @ X2)
% 0.22/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.57          | (v1_xboole_0 @ X0)
% 0.22/0.57          | ~ (v1_funct_1 @ sk_D)
% 0.22/0.57          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.22/0.57          | (r1_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ X1 @ 
% 0.22/0.57             X0 @ sk_D @ sk_D))),
% 0.22/0.57      inference('sup-', [status(thm)], ['64', '65'])).
% 0.22/0.57  thf('67', plain, ((v1_funct_1 @ sk_D)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('68', plain,
% 0.22/0.57      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('69', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.57         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.22/0.57          | ~ (v1_funct_2 @ X2 @ X1 @ X0)
% 0.22/0.57          | ~ (v1_funct_1 @ X2)
% 0.22/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.57          | (v1_xboole_0 @ X0)
% 0.22/0.57          | (r1_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ X1 @ 
% 0.22/0.57             X0 @ sk_D @ sk_D))),
% 0.22/0.57      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.22/0.57  thf('70', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.22/0.57      inference('demod', [status(thm)], ['10', '61'])).
% 0.22/0.57  thf('71', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.57         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.22/0.57          | ~ (v1_funct_2 @ X2 @ X1 @ X0)
% 0.22/0.57          | ~ (v1_funct_1 @ X2)
% 0.22/0.57          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.57          | (v1_xboole_0 @ X0)
% 0.22/0.57          | (r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ X1 @ 
% 0.22/0.57             X0 @ sk_D @ sk_D))),
% 0.22/0.57      inference('demod', [status(thm)], ['69', '70'])).
% 0.22/0.57  thf('72', plain,
% 0.22/0.57      (((r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.57         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)
% 0.22/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.57        | ~ (v1_funct_1 @ sk_D)
% 0.22/0.57        | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['63', '71'])).
% 0.22/0.57  thf('73', plain, ((v1_funct_1 @ sk_D)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('74', plain,
% 0.22/0.57      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('75', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.22/0.57      inference('demod', [status(thm)], ['10', '61'])).
% 0.22/0.57  thf('76', plain,
% 0.22/0.57      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.22/0.57      inference('demod', [status(thm)], ['74', '75'])).
% 0.22/0.57  thf('77', plain,
% 0.22/0.57      (((r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.57         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)
% 0.22/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.57      inference('demod', [status(thm)], ['72', '73', '76'])).
% 0.22/0.57  thf('78', plain,
% 0.22/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.57        | (r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.57           (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.22/0.57      inference('simplify', [status(thm)], ['77'])).
% 0.22/0.57  thf('79', plain,
% 0.22/0.57      (~ (r1_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.57          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.22/0.57          (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('80', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('81', plain,
% 0.22/0.57      ((m1_subset_1 @ sk_D @ 
% 0.22/0.57        (k1_zfmisc_1 @ 
% 0.22/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(d4_tmap_1, axiom,
% 0.22/0.57    (![A:$i]:
% 0.22/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.57       ( ![B:$i]:
% 0.22/0.57         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.22/0.57             ( l1_pre_topc @ B ) ) =>
% 0.22/0.57           ( ![C:$i]:
% 0.22/0.57             ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.57                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.22/0.57                 ( m1_subset_1 @
% 0.22/0.57                   C @ 
% 0.22/0.57                   ( k1_zfmisc_1 @
% 0.22/0.57                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.22/0.57               ( ![D:$i]:
% 0.22/0.57                 ( ( m1_pre_topc @ D @ A ) =>
% 0.22/0.57                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.22/0.57                     ( k2_partfun1 @
% 0.22/0.57                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.22/0.57                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.57  thf('82', plain,
% 0.22/0.57      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.22/0.57         ((v2_struct_0 @ X29)
% 0.22/0.57          | ~ (v2_pre_topc @ X29)
% 0.22/0.57          | ~ (l1_pre_topc @ X29)
% 0.22/0.57          | ~ (m1_pre_topc @ X30 @ X31)
% 0.22/0.57          | ((k2_tmap_1 @ X31 @ X29 @ X32 @ X30)
% 0.22/0.57              = (k2_partfun1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X29) @ 
% 0.22/0.57                 X32 @ (u1_struct_0 @ X30)))
% 0.22/0.57          | ~ (m1_subset_1 @ X32 @ 
% 0.22/0.57               (k1_zfmisc_1 @ 
% 0.22/0.57                (k2_zfmisc_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X29))))
% 0.22/0.57          | ~ (v1_funct_2 @ X32 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X29))
% 0.22/0.57          | ~ (v1_funct_1 @ X32)
% 0.22/0.57          | ~ (l1_pre_topc @ X31)
% 0.22/0.57          | ~ (v2_pre_topc @ X31)
% 0.22/0.57          | (v2_struct_0 @ X31))),
% 0.22/0.57      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.22/0.57  thf('83', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         ((v2_struct_0 @ sk_B)
% 0.22/0.57          | ~ (v2_pre_topc @ sk_B)
% 0.22/0.57          | ~ (l1_pre_topc @ sk_B)
% 0.22/0.57          | ~ (v1_funct_1 @ sk_D)
% 0.22/0.57          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.22/0.57          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.22/0.57              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.57                 sk_D @ (u1_struct_0 @ X0)))
% 0.22/0.57          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.22/0.57          | ~ (l1_pre_topc @ sk_A)
% 0.22/0.57          | ~ (v2_pre_topc @ sk_A)
% 0.22/0.57          | (v2_struct_0 @ sk_A))),
% 0.22/0.57      inference('sup-', [status(thm)], ['81', '82'])).
% 0.22/0.57  thf('84', plain, ((v2_pre_topc @ sk_B)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('85', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('86', plain, ((v1_funct_1 @ sk_D)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('87', plain,
% 0.22/0.57      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('88', plain,
% 0.22/0.57      ((m1_subset_1 @ sk_D @ 
% 0.22/0.57        (k1_zfmisc_1 @ 
% 0.22/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(redefinition_k2_partfun1, axiom,
% 0.22/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.57     ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.57       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.22/0.57  thf('89', plain,
% 0.22/0.57      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.22/0.57         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.22/0.57          | ~ (v1_funct_1 @ X14)
% 0.22/0.57          | ((k2_partfun1 @ X15 @ X16 @ X14 @ X17) = (k7_relat_1 @ X14 @ X17)))),
% 0.22/0.57      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.22/0.57  thf('90', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         (((k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.22/0.57            X0) = (k7_relat_1 @ sk_D @ X0))
% 0.22/0.57          | ~ (v1_funct_1 @ sk_D))),
% 0.22/0.57      inference('sup-', [status(thm)], ['88', '89'])).
% 0.22/0.57  thf('91', plain, ((v1_funct_1 @ sk_D)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('92', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         ((k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.22/0.57           X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.22/0.57      inference('demod', [status(thm)], ['90', '91'])).
% 0.22/0.57  thf('93', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('94', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('95', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         ((v2_struct_0 @ sk_B)
% 0.22/0.57          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.22/0.57              = (k7_relat_1 @ sk_D @ (u1_struct_0 @ X0)))
% 0.22/0.57          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.22/0.57          | (v2_struct_0 @ sk_A))),
% 0.22/0.57      inference('demod', [status(thm)],
% 0.22/0.57                ['83', '84', '85', '86', '87', '92', '93', '94'])).
% 0.22/0.57  thf('96', plain,
% 0.22/0.57      (((v2_struct_0 @ sk_A)
% 0.22/0.57        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.22/0.57            = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))
% 0.22/0.57        | (v2_struct_0 @ sk_B))),
% 0.22/0.57      inference('sup-', [status(thm)], ['80', '95'])).
% 0.22/0.57  thf('97', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('98', plain,
% 0.22/0.57      (((v2_struct_0 @ sk_B)
% 0.22/0.57        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.22/0.57            = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C))))),
% 0.22/0.57      inference('clc', [status(thm)], ['96', '97'])).
% 0.22/0.57  thf('99', plain, (~ (v2_struct_0 @ sk_B)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('100', plain,
% 0.22/0.57      (((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C)
% 0.22/0.57         = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.22/0.57      inference('clc', [status(thm)], ['98', '99'])).
% 0.22/0.57  thf('101', plain,
% 0.22/0.57      (~ (r1_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.57          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.22/0.57          (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.22/0.57      inference('demod', [status(thm)], ['79', '100'])).
% 0.22/0.57  thf('102', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.22/0.57      inference('demod', [status(thm)], ['10', '61'])).
% 0.22/0.57  thf('103', plain,
% 0.22/0.57      (~ (r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.57          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.22/0.57          (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.22/0.57      inference('demod', [status(thm)], ['101', '102'])).
% 0.22/0.57  thf('104', plain,
% 0.22/0.57      ((m1_subset_1 @ sk_D @ 
% 0.22/0.57        (k1_zfmisc_1 @ 
% 0.22/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(cc2_relset_1, axiom,
% 0.22/0.57    (![A:$i,B:$i,C:$i]:
% 0.22/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.57       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.22/0.57  thf('105', plain,
% 0.22/0.57      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.57         ((v4_relat_1 @ X11 @ X12)
% 0.22/0.57          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.22/0.57      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.57  thf('106', plain, ((v4_relat_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.22/0.57      inference('sup-', [status(thm)], ['104', '105'])).
% 0.22/0.57  thf(t209_relat_1, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.22/0.57       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.22/0.57  thf('107', plain,
% 0.22/0.57      (![X6 : $i, X7 : $i]:
% 0.22/0.57         (((X6) = (k7_relat_1 @ X6 @ X7))
% 0.22/0.57          | ~ (v4_relat_1 @ X6 @ X7)
% 0.22/0.57          | ~ (v1_relat_1 @ X6))),
% 0.22/0.57      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.22/0.57  thf('108', plain,
% 0.22/0.57      ((~ (v1_relat_1 @ sk_D)
% 0.22/0.57        | ((sk_D) = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_B))))),
% 0.22/0.57      inference('sup-', [status(thm)], ['106', '107'])).
% 0.22/0.57  thf('109', plain,
% 0.22/0.57      ((m1_subset_1 @ sk_D @ 
% 0.22/0.57        (k1_zfmisc_1 @ 
% 0.22/0.57         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(cc1_relset_1, axiom,
% 0.22/0.57    (![A:$i,B:$i,C:$i]:
% 0.22/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.57       ( v1_relat_1 @ C ) ))).
% 0.22/0.57  thf('110', plain,
% 0.22/0.57      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.57         ((v1_relat_1 @ X8)
% 0.22/0.57          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.22/0.57      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.22/0.57  thf('111', plain, ((v1_relat_1 @ sk_D)),
% 0.22/0.57      inference('sup-', [status(thm)], ['109', '110'])).
% 0.22/0.57  thf('112', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_B)))),
% 0.22/0.57      inference('demod', [status(thm)], ['108', '111'])).
% 0.22/0.57  thf('113', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C))),
% 0.22/0.57      inference('demod', [status(thm)], ['10', '61'])).
% 0.22/0.57  thf('114', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C)))),
% 0.22/0.57      inference('demod', [status(thm)], ['112', '113'])).
% 0.22/0.57  thf('115', plain,
% 0.22/0.57      (~ (r1_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.22/0.57          (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)),
% 0.22/0.57      inference('demod', [status(thm)], ['103', '114'])).
% 0.22/0.57  thf('116', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.22/0.57      inference('clc', [status(thm)], ['78', '115'])).
% 0.22/0.57  thf(fc2_struct_0, axiom,
% 0.22/0.57    (![A:$i]:
% 0.22/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.57       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.22/0.57  thf('117', plain,
% 0.22/0.57      (![X21 : $i]:
% 0.22/0.57         (~ (v1_xboole_0 @ (u1_struct_0 @ X21))
% 0.22/0.57          | ~ (l1_struct_0 @ X21)
% 0.22/0.57          | (v2_struct_0 @ X21))),
% 0.22/0.57      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.22/0.57  thf('118', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.22/0.57      inference('sup-', [status(thm)], ['116', '117'])).
% 0.22/0.57  thf('119', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(dt_l1_pre_topc, axiom,
% 0.22/0.57    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.22/0.57  thf('120', plain,
% 0.22/0.57      (![X18 : $i]: ((l1_struct_0 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.22/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.57  thf('121', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.57      inference('sup-', [status(thm)], ['119', '120'])).
% 0.22/0.57  thf('122', plain, ((v2_struct_0 @ sk_A)),
% 0.22/0.57      inference('demod', [status(thm)], ['118', '121'])).
% 0.22/0.57  thf('123', plain, ($false), inference('demod', [status(thm)], ['0', '122'])).
% 0.22/0.57  
% 0.22/0.57  % SZS output end Refutation
% 0.22/0.57  
% 0.22/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
