%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Zpx5oXFS8J

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  153 (1056 expanded)
%              Number of leaves         :   45 ( 321 expanded)
%              Depth                    :   26
%              Number of atoms          : 1311 (19819 expanded)
%              Number of equality atoms :   36 ( 365 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

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
    m1_pre_topc @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_pre_topc @ X41 @ X42 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X41 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( l1_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('9',plain,(
    ! [X8: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('10',plain,(
    r2_hidden @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r1_tarski @ X6 @ X4 )
      | ( X5
       != ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('12',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('17',plain,(
    ! [X43: $i] :
      ( ( m1_pre_topc @ X43 @ X43 )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('18',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_pre_topc @ X29 )
      | ~ ( m1_pre_topc @ X30 @ X29 )
      | ( m1_pre_topc @ X30 @ ( g1_pre_topc @ ( u1_struct_0 @ X29 ) @ ( u1_pre_topc @ X29 ) ) )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ( m1_pre_topc @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['16','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_pre_topc @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_pre_topc @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_pre_topc @ X27 @ ( g1_pre_topc @ ( u1_struct_0 @ X28 ) @ ( u1_pre_topc @ X28 ) ) )
      | ( m1_pre_topc @ X27 @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('25',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( m1_pre_topc @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_pre_topc @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('27',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_pre_topc @ X24 @ X25 )
      | ( l1_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('28',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    m1_pre_topc @ sk_B @ sk_C_1 ),
    inference(demod,[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_pre_topc @ X41 @ X42 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X41 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( l1_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('33',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['28','29'])).

thf('35',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X8: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('39',plain,(
    r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('41',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['15','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','42'])).

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

thf('45',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X31 @ X32 @ X33 )
      | ~ ( v1_funct_1 @ X31 )
      | ( v1_xboole_0 @ X34 )
      | ( v1_xboole_0 @ X33 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X34 ) ) )
      | ( r1_funct_2 @ X32 @ X33 @ X36 @ X34 @ X31 @ X35 )
      | ( X31 != X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_funct_2])).

thf('46',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( r1_funct_2 @ X32 @ X33 @ X36 @ X34 @ X35 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X34 )
      | ( v1_xboole_0 @ X33 )
      | ( v1_xboole_0 @ X34 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_D @ X1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_funct_2 @ X1 @ X0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ) ),
    inference('sup-',[status(thm)],['44','46'])).

thf('48',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['15','41'])).

thf('51',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_D @ X1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X0 )
      | ( r1_funct_2 @ X1 @ X0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ) ),
    inference(demod,[status(thm)],['47','48','51'])).

thf('53',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','52'])).

thf('54',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('55',plain,
    ( ( r1_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['15','41'])).

thf('59',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    m1_pre_topc @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','42'])).

thf('62',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['15','41'])).

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

thf('63',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( v2_struct_0 @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( m1_pre_topc @ X38 @ X39 )
      | ( ( k2_tmap_1 @ X39 @ X37 @ X40 @ X38 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X37 ) @ X40 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X37 ) ) ) )
      | ~ ( v1_funct_2 @ X40 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X37 ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ( v2_struct_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_tmap_1 @ sk_B @ X0 @ X1 @ X2 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) @ X1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( m1_pre_topc @ X2 @ sk_B )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['15','41'])).

thf('68',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['15','41'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_tmap_1 @ sk_B @ X0 @ X1 @ X2 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ X0 ) @ X1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( m1_pre_topc @ X2 @ sk_B )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['64','65','66','67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['61','69'])).

thf('71',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','42'])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('74',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ( ( k2_partfun1 @ X20 @ X21 @ X19 @ X22 )
        = ( k7_relat_1 @ X19 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    v1_funct_2 @ sk_D @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('79',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['70','71','72','77','78','79'])).

thf('81',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 )
      = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['60','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('83',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v4_relat_1 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('84',plain,(
    v4_relat_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('85',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11
        = ( k7_relat_1 @ X11 @ X12 ) )
      | ~ ( v4_relat_1 @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('86',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('88',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('89',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['86','89'])).

thf('91',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['15','41'])).

thf('92',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 )
      = sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['81','92'])).

thf('94',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 )
      = sk_D ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1 )
    = sk_D ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,(
    ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) @ sk_D @ sk_D ) ),
    inference(demod,[status(thm)],['59','97'])).

thf('99',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['56','98'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('100',plain,(
    ! [X26: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('101',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('103',plain,(
    ! [X23: $i] :
      ( ( l1_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('104',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['101','104'])).

thf('106',plain,(
    $false ),
    inference(demod,[status(thm)],['0','105'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Zpx5oXFS8J
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:20:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 143 iterations in 0.056s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.50  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.20/0.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.50  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.50  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.20/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.50  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.20/0.50  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.20/0.50  thf(r1_funct_2_type, type, r1_funct_2: $i > $i > $i > $i > $i > $i > $o).
% 0.20/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.50  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.50  thf(t60_tmap_1, conjecture,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.50             ( l1_pre_topc @ B ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.20/0.50               ( ![D:$i]:
% 0.20/0.50                 ( ( ( v1_funct_1 @ D ) & 
% 0.20/0.50                     ( v1_funct_2 @
% 0.20/0.50                       D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.50                     ( m1_subset_1 @
% 0.20/0.50                       D @ 
% 0.20/0.50                       ( k1_zfmisc_1 @
% 0.20/0.50                         ( k2_zfmisc_1 @
% 0.20/0.50                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.50                   ( ( ( g1_pre_topc @
% 0.20/0.50                         ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.20/0.50                       ( g1_pre_topc @
% 0.20/0.50                         ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.20/0.50                     ( r1_funct_2 @
% 0.20/0.50                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.20/0.50                       ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ 
% 0.20/0.50                       ( k2_tmap_1 @ B @ A @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]:
% 0.20/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.50            ( l1_pre_topc @ A ) ) =>
% 0.20/0.50          ( ![B:$i]:
% 0.20/0.50            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.50                ( l1_pre_topc @ B ) ) =>
% 0.20/0.50              ( ![C:$i]:
% 0.20/0.50                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.20/0.50                  ( ![D:$i]:
% 0.20/0.50                    ( ( ( v1_funct_1 @ D ) & 
% 0.20/0.50                        ( v1_funct_2 @
% 0.20/0.50                          D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.50                        ( m1_subset_1 @
% 0.20/0.50                          D @ 
% 0.20/0.50                          ( k1_zfmisc_1 @
% 0.20/0.50                            ( k2_zfmisc_1 @
% 0.20/0.50                              ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.50                      ( ( ( g1_pre_topc @
% 0.20/0.50                            ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) =
% 0.20/0.50                          ( g1_pre_topc @
% 0.20/0.50                            ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) =>
% 0.20/0.50                        ( r1_funct_2 @
% 0.20/0.50                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.20/0.50                          ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ D @ 
% 0.20/0.50                          ( k2_tmap_1 @ B @ A @ D @ C ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t60_tmap_1])).
% 0.20/0.50  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_D @ 
% 0.20/0.50        (k1_zfmisc_1 @ 
% 0.20/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('2', plain, ((m1_pre_topc @ sk_C_1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t1_tsep_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.50           ( m1_subset_1 @
% 0.20/0.50             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (![X41 : $i, X42 : $i]:
% 0.20/0.50         (~ (m1_pre_topc @ X41 @ X42)
% 0.20/0.50          | (m1_subset_1 @ (u1_struct_0 @ X41) @ 
% 0.20/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 0.20/0.50          | ~ (l1_pre_topc @ X42))),
% 0.20/0.50      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      ((~ (l1_pre_topc @ sk_B)
% 0.20/0.50        | (m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.20/0.50           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.50  thf('5', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      ((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 0.20/0.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.50      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.50  thf(t2_subset, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ A @ B ) =>
% 0.20/0.50       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (![X9 : $i, X10 : $i]:
% 0.20/0.50         ((r2_hidden @ X9 @ X10)
% 0.20/0.50          | (v1_xboole_0 @ X10)
% 0.20/0.50          | ~ (m1_subset_1 @ X9 @ X10))),
% 0.20/0.50      inference('cnf', [status(esa)], [t2_subset])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (((v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.50        | (r2_hidden @ (u1_struct_0 @ sk_C_1) @ 
% 0.20/0.50           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.50  thf(fc1_subset_1, axiom,
% 0.20/0.50    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.50  thf('9', plain, (![X8 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      ((r2_hidden @ (u1_struct_0 @ sk_C_1) @ 
% 0.20/0.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.50      inference('clc', [status(thm)], ['8', '9'])).
% 0.20/0.50  thf(d1_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.20/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X6 @ X5)
% 0.20/0.50          | (r1_tarski @ X6 @ X4)
% 0.20/0.50          | ((X5) != (k1_zfmisc_1 @ X4)))),
% 0.20/0.50      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (![X4 : $i, X6 : $i]:
% 0.20/0.50         ((r1_tarski @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k1_zfmisc_1 @ X4)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      ((r1_tarski @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['10', '12'])).
% 0.20/0.50  thf(d10_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (![X0 : $i, X2 : $i]:
% 0.20/0.50         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      ((~ (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))
% 0.20/0.50        | ((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C_1)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (((g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1))
% 0.20/0.50         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t2_tsep_1, axiom,
% 0.20/0.50    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      (![X43 : $i]: ((m1_pre_topc @ X43 @ X43) | ~ (l1_pre_topc @ X43))),
% 0.20/0.50      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.20/0.50  thf(t65_pre_topc, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( l1_pre_topc @ B ) =>
% 0.20/0.50           ( ( m1_pre_topc @ A @ B ) <=>
% 0.20/0.50             ( m1_pre_topc @
% 0.20/0.50               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (![X29 : $i, X30 : $i]:
% 0.20/0.50         (~ (l1_pre_topc @ X29)
% 0.20/0.50          | ~ (m1_pre_topc @ X30 @ X29)
% 0.20/0.50          | (m1_pre_topc @ X30 @ 
% 0.20/0.50             (g1_pre_topc @ (u1_struct_0 @ X29) @ (u1_pre_topc @ X29)))
% 0.20/0.50          | ~ (l1_pre_topc @ X30))),
% 0.20/0.50      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (l1_pre_topc @ X0)
% 0.20/0.50          | ~ (l1_pre_topc @ X0)
% 0.20/0.50          | (m1_pre_topc @ X0 @ 
% 0.20/0.50             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.50          | ~ (l1_pre_topc @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((m1_pre_topc @ X0 @ 
% 0.20/0.50           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.50          | ~ (l1_pre_topc @ X0))),
% 0.20/0.50      inference('simplify', [status(thm)], ['19'])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      (((m1_pre_topc @ sk_B @ 
% 0.20/0.50         (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))
% 0.20/0.50        | ~ (l1_pre_topc @ sk_B))),
% 0.20/0.50      inference('sup+', [status(thm)], ['16', '20'])).
% 0.20/0.50  thf('22', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      ((m1_pre_topc @ sk_B @ 
% 0.20/0.50        (g1_pre_topc @ (u1_struct_0 @ sk_C_1) @ (u1_pre_topc @ sk_C_1)))),
% 0.20/0.50      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.50  thf(t59_pre_topc, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_pre_topc @
% 0.20/0.50             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.20/0.50           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      (![X27 : $i, X28 : $i]:
% 0.20/0.50         (~ (m1_pre_topc @ X27 @ 
% 0.20/0.50             (g1_pre_topc @ (u1_struct_0 @ X28) @ (u1_pre_topc @ X28)))
% 0.20/0.50          | (m1_pre_topc @ X27 @ X28)
% 0.20/0.50          | ~ (l1_pre_topc @ X28))),
% 0.20/0.50      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      ((~ (l1_pre_topc @ sk_C_1) | (m1_pre_topc @ sk_B @ sk_C_1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.50  thf('26', plain, ((m1_pre_topc @ sk_C_1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(dt_m1_pre_topc, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      (![X24 : $i, X25 : $i]:
% 0.20/0.50         (~ (m1_pre_topc @ X24 @ X25)
% 0.20/0.50          | (l1_pre_topc @ X24)
% 0.20/0.50          | ~ (l1_pre_topc @ X25))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.50  thf('28', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_C_1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.50  thf('29', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('30', plain, ((l1_pre_topc @ sk_C_1)),
% 0.20/0.50      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.50  thf('31', plain, ((m1_pre_topc @ sk_B @ sk_C_1)),
% 0.20/0.50      inference('demod', [status(thm)], ['25', '30'])).
% 0.20/0.50  thf('32', plain,
% 0.20/0.50      (![X41 : $i, X42 : $i]:
% 0.20/0.50         (~ (m1_pre_topc @ X41 @ X42)
% 0.20/0.50          | (m1_subset_1 @ (u1_struct_0 @ X41) @ 
% 0.20/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 0.20/0.50          | ~ (l1_pre_topc @ X42))),
% 0.20/0.50      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.20/0.50  thf('33', plain,
% 0.20/0.50      ((~ (l1_pre_topc @ sk_C_1)
% 0.20/0.50        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.50           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.50  thf('34', plain, ((l1_pre_topc @ sk_C_1)),
% 0.20/0.50      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.20/0.50      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      (![X9 : $i, X10 : $i]:
% 0.20/0.50         ((r2_hidden @ X9 @ X10)
% 0.20/0.50          | (v1_xboole_0 @ X10)
% 0.20/0.50          | ~ (m1_subset_1 @ X9 @ X10))),
% 0.20/0.50      inference('cnf', [status(esa)], [t2_subset])).
% 0.20/0.50  thf('37', plain,
% 0.20/0.50      (((v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.20/0.50        | (r2_hidden @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.50           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.50  thf('38', plain, (![X8 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.20/0.51  thf('39', plain,
% 0.20/0.51      ((r2_hidden @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.20/0.51      inference('clc', [status(thm)], ['37', '38'])).
% 0.20/0.51  thf('40', plain,
% 0.20/0.51      (![X4 : $i, X6 : $i]:
% 0.20/0.51         ((r1_tarski @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k1_zfmisc_1 @ X4)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.51  thf('41', plain,
% 0.20/0.51      ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.51  thf('42', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C_1))),
% 0.20/0.51      inference('demod', [status(thm)], ['15', '41'])).
% 0.20/0.51  thf('43', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_D @ 
% 0.20/0.51        (k1_zfmisc_1 @ 
% 0.20/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.51      inference('demod', [status(thm)], ['1', '42'])).
% 0.20/0.51  thf('44', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_D @ 
% 0.20/0.51        (k1_zfmisc_1 @ 
% 0.20/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.51      inference('demod', [status(thm)], ['1', '42'])).
% 0.20/0.51  thf(redefinition_r1_funct_2, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.51     ( ( ( ~( v1_xboole_0 @ B ) ) & ( ~( v1_xboole_0 @ D ) ) & 
% 0.20/0.51         ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 0.20/0.51         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.51         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ C @ D ) & 
% 0.20/0.51         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.20/0.51       ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F ) <=> ( ( E ) = ( F ) ) ) ))).
% 0.20/0.51  thf('45', plain,
% 0.20/0.51      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.20/0.51          | ~ (v1_funct_2 @ X31 @ X32 @ X33)
% 0.20/0.51          | ~ (v1_funct_1 @ X31)
% 0.20/0.51          | (v1_xboole_0 @ X34)
% 0.20/0.51          | (v1_xboole_0 @ X33)
% 0.20/0.51          | ~ (v1_funct_1 @ X35)
% 0.20/0.51          | ~ (v1_funct_2 @ X35 @ X36 @ X34)
% 0.20/0.51          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X34)))
% 0.20/0.51          | (r1_funct_2 @ X32 @ X33 @ X36 @ X34 @ X31 @ X35)
% 0.20/0.51          | ((X31) != (X35)))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_r1_funct_2])).
% 0.20/0.51  thf('46', plain,
% 0.20/0.51      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.20/0.51         ((r1_funct_2 @ X32 @ X33 @ X36 @ X34 @ X35 @ X35)
% 0.20/0.51          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X34)))
% 0.20/0.51          | ~ (v1_funct_2 @ X35 @ X36 @ X34)
% 0.20/0.51          | (v1_xboole_0 @ X33)
% 0.20/0.51          | (v1_xboole_0 @ X34)
% 0.20/0.51          | ~ (v1_funct_1 @ X35)
% 0.20/0.51          | ~ (v1_funct_2 @ X35 @ X32 @ X33)
% 0.20/0.51          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.20/0.51      inference('simplify', [status(thm)], ['45'])).
% 0.20/0.51  thf('47', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.20/0.51          | ~ (v1_funct_2 @ sk_D @ X1 @ X0)
% 0.20/0.51          | ~ (v1_funct_1 @ sk_D)
% 0.20/0.51          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51          | (v1_xboole_0 @ X0)
% 0.20/0.51          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C_1) @ 
% 0.20/0.51               (u1_struct_0 @ sk_A))
% 0.20/0.51          | (r1_funct_2 @ X1 @ X0 @ (u1_struct_0 @ sk_C_1) @ 
% 0.20/0.51             (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.20/0.51      inference('sup-', [status(thm)], ['44', '46'])).
% 0.20/0.51  thf('48', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('49', plain,
% 0.20/0.51      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('50', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C_1))),
% 0.20/0.51      inference('demod', [status(thm)], ['15', '41'])).
% 0.20/0.51  thf('51', plain,
% 0.20/0.51      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['49', '50'])).
% 0.20/0.51  thf('52', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.20/0.51          | ~ (v1_funct_2 @ sk_D @ X1 @ X0)
% 0.20/0.51          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51          | (v1_xboole_0 @ X0)
% 0.20/0.51          | (r1_funct_2 @ X1 @ X0 @ (u1_struct_0 @ sk_C_1) @ 
% 0.20/0.51             (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.20/0.51      inference('demod', [status(thm)], ['47', '48', '51'])).
% 0.20/0.51  thf('53', plain,
% 0.20/0.51      (((r1_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.51         (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)
% 0.20/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51        | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['43', '52'])).
% 0.20/0.51  thf('54', plain,
% 0.20/0.51      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['49', '50'])).
% 0.20/0.51  thf('55', plain,
% 0.20/0.51      (((r1_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.51         (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)
% 0.20/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('demod', [status(thm)], ['53', '54'])).
% 0.20/0.51  thf('56', plain,
% 0.20/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51        | (r1_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.51           (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D))),
% 0.20/0.51      inference('simplify', [status(thm)], ['55'])).
% 0.20/0.51  thf('57', plain,
% 0.20/0.51      (~ (r1_funct_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.51          (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.20/0.51          (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('58', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C_1))),
% 0.20/0.51      inference('demod', [status(thm)], ['15', '41'])).
% 0.20/0.51  thf('59', plain,
% 0.20/0.51      (~ (r1_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.51          (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A) @ sk_D @ 
% 0.20/0.51          (k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1))),
% 0.20/0.51      inference('demod', [status(thm)], ['57', '58'])).
% 0.20/0.51  thf('60', plain, ((m1_pre_topc @ sk_C_1 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('61', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_D @ 
% 0.20/0.51        (k1_zfmisc_1 @ 
% 0.20/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.51      inference('demod', [status(thm)], ['1', '42'])).
% 0.20/0.51  thf('62', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C_1))),
% 0.20/0.51      inference('demod', [status(thm)], ['15', '41'])).
% 0.20/0.51  thf(d4_tmap_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.51             ( l1_pre_topc @ B ) ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.51                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.51                 ( m1_subset_1 @
% 0.20/0.51                   C @ 
% 0.20/0.51                   ( k1_zfmisc_1 @
% 0.20/0.51                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.51               ( ![D:$i]:
% 0.20/0.51                 ( ( m1_pre_topc @ D @ A ) =>
% 0.20/0.51                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.20/0.51                     ( k2_partfun1 @
% 0.20/0.51                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.20/0.51                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf('63', plain,
% 0.20/0.51      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.20/0.51         ((v2_struct_0 @ X37)
% 0.20/0.51          | ~ (v2_pre_topc @ X37)
% 0.20/0.51          | ~ (l1_pre_topc @ X37)
% 0.20/0.51          | ~ (m1_pre_topc @ X38 @ X39)
% 0.20/0.51          | ((k2_tmap_1 @ X39 @ X37 @ X40 @ X38)
% 0.20/0.51              = (k2_partfun1 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X37) @ 
% 0.20/0.51                 X40 @ (u1_struct_0 @ X38)))
% 0.20/0.51          | ~ (m1_subset_1 @ X40 @ 
% 0.20/0.51               (k1_zfmisc_1 @ 
% 0.20/0.51                (k2_zfmisc_1 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X37))))
% 0.20/0.51          | ~ (v1_funct_2 @ X40 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X37))
% 0.20/0.51          | ~ (v1_funct_1 @ X40)
% 0.20/0.51          | ~ (l1_pre_topc @ X39)
% 0.20/0.51          | ~ (v2_pre_topc @ X39)
% 0.20/0.51          | (v2_struct_0 @ X39))),
% 0.20/0.51      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.20/0.51  thf('64', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X1 @ 
% 0.20/0.51             (k1_zfmisc_1 @ 
% 0.20/0.51              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))))
% 0.20/0.51          | (v2_struct_0 @ sk_B)
% 0.20/0.51          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.51          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.51          | ~ (v1_funct_1 @ X1)
% 0.20/0.51          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0))
% 0.20/0.51          | ((k2_tmap_1 @ sk_B @ X0 @ X1 @ X2)
% 0.20/0.51              = (k2_partfun1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ X0) @ 
% 0.20/0.51                 X1 @ (u1_struct_0 @ X2)))
% 0.20/0.51          | ~ (m1_pre_topc @ X2 @ sk_B)
% 0.20/0.51          | ~ (l1_pre_topc @ X0)
% 0.20/0.51          | ~ (v2_pre_topc @ X0)
% 0.20/0.51          | (v2_struct_0 @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['62', '63'])).
% 0.20/0.51  thf('65', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('66', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('67', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C_1))),
% 0.20/0.51      inference('demod', [status(thm)], ['15', '41'])).
% 0.20/0.51  thf('68', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C_1))),
% 0.20/0.51      inference('demod', [status(thm)], ['15', '41'])).
% 0.20/0.51  thf('69', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X1 @ 
% 0.20/0.51             (k1_zfmisc_1 @ 
% 0.20/0.51              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))))
% 0.20/0.51          | (v2_struct_0 @ sk_B)
% 0.20/0.51          | ~ (v1_funct_1 @ X1)
% 0.20/0.51          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0))
% 0.20/0.51          | ((k2_tmap_1 @ sk_B @ X0 @ X1 @ X2)
% 0.20/0.51              = (k2_partfun1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ X0) @ 
% 0.20/0.51                 X1 @ (u1_struct_0 @ X2)))
% 0.20/0.51          | ~ (m1_pre_topc @ X2 @ sk_B)
% 0.20/0.51          | ~ (l1_pre_topc @ X0)
% 0.20/0.51          | ~ (v2_pre_topc @ X0)
% 0.20/0.51          | (v2_struct_0 @ X0))),
% 0.20/0.51      inference('demod', [status(thm)], ['64', '65', '66', '67', '68'])).
% 0.20/0.51  thf('70', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_A)
% 0.20/0.51          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.51          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.51          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.20/0.51          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.20/0.51              = (k2_partfun1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.51                 sk_D @ (u1_struct_0 @ X0)))
% 0.20/0.51          | ~ (v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C_1) @ 
% 0.20/0.51               (u1_struct_0 @ sk_A))
% 0.20/0.51          | ~ (v1_funct_1 @ sk_D)
% 0.20/0.51          | (v2_struct_0 @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['61', '69'])).
% 0.20/0.51  thf('71', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('73', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_D @ 
% 0.20/0.51        (k1_zfmisc_1 @ 
% 0.20/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.51      inference('demod', [status(thm)], ['1', '42'])).
% 0.20/0.51  thf(redefinition_k2_partfun1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.51     ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.51         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.51       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.20/0.51  thf('74', plain,
% 0.20/0.51      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.20/0.51          | ~ (v1_funct_1 @ X19)
% 0.20/0.51          | ((k2_partfun1 @ X20 @ X21 @ X19 @ X22) = (k7_relat_1 @ X19 @ X22)))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.20/0.51  thf('75', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((k2_partfun1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.51            sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))
% 0.20/0.51          | ~ (v1_funct_1 @ sk_D))),
% 0.20/0.51      inference('sup-', [status(thm)], ['73', '74'])).
% 0.20/0.51  thf('76', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('77', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((k2_partfun1 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.51           sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.20/0.51      inference('demod', [status(thm)], ['75', '76'])).
% 0.20/0.51  thf('78', plain,
% 0.20/0.51      ((v1_funct_2 @ sk_D @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['49', '50'])).
% 0.20/0.51  thf('79', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('80', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v2_struct_0 @ sk_A)
% 0.20/0.51          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.20/0.51          | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ X0)
% 0.20/0.51              = (k7_relat_1 @ sk_D @ (u1_struct_0 @ X0)))
% 0.20/0.51          | (v2_struct_0 @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['70', '71', '72', '77', '78', '79'])).
% 0.20/0.51  thf('81', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_B)
% 0.20/0.51        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1)
% 0.20/0.51            = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C_1)))
% 0.20/0.51        | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['60', '80'])).
% 0.20/0.51  thf('82', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_D @ 
% 0.20/0.51        (k1_zfmisc_1 @ 
% 0.20/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(cc2_relset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.51  thf('83', plain,
% 0.20/0.51      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.51         ((v4_relat_1 @ X16 @ X17)
% 0.20/0.51          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.20/0.51      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.51  thf('84', plain, ((v4_relat_1 @ sk_D @ (u1_struct_0 @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['82', '83'])).
% 0.20/0.51  thf(t209_relat_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.20/0.51       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.20/0.51  thf('85', plain,
% 0.20/0.51      (![X11 : $i, X12 : $i]:
% 0.20/0.51         (((X11) = (k7_relat_1 @ X11 @ X12))
% 0.20/0.51          | ~ (v4_relat_1 @ X11 @ X12)
% 0.20/0.51          | ~ (v1_relat_1 @ X11))),
% 0.20/0.51      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.20/0.51  thf('86', plain,
% 0.20/0.51      ((~ (v1_relat_1 @ sk_D)
% 0.20/0.51        | ((sk_D) = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_B))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['84', '85'])).
% 0.20/0.51  thf('87', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_D @ 
% 0.20/0.51        (k1_zfmisc_1 @ 
% 0.20/0.51         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(cc1_relset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51       ( v1_relat_1 @ C ) ))).
% 0.20/0.51  thf('88', plain,
% 0.20/0.51      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.51         ((v1_relat_1 @ X13)
% 0.20/0.51          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.20/0.51      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.51  thf('89', plain, ((v1_relat_1 @ sk_D)),
% 0.20/0.51      inference('sup-', [status(thm)], ['87', '88'])).
% 0.20/0.51  thf('90', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['86', '89'])).
% 0.20/0.51  thf('91', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_C_1))),
% 0.20/0.51      inference('demod', [status(thm)], ['15', '41'])).
% 0.20/0.51  thf('92', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (u1_struct_0 @ sk_C_1)))),
% 0.20/0.51      inference('demod', [status(thm)], ['90', '91'])).
% 0.20/0.51  thf('93', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_B)
% 0.20/0.51        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1) = (sk_D))
% 0.20/0.51        | (v2_struct_0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['81', '92'])).
% 0.20/0.51  thf('94', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('95', plain,
% 0.20/0.51      (((v2_struct_0 @ sk_A)
% 0.20/0.51        | ((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1) = (sk_D)))),
% 0.20/0.51      inference('clc', [status(thm)], ['93', '94'])).
% 0.20/0.51  thf('96', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('97', plain, (((k2_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C_1) = (sk_D))),
% 0.20/0.51      inference('clc', [status(thm)], ['95', '96'])).
% 0.20/0.51  thf('98', plain,
% 0.20/0.51      (~ (r1_funct_2 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.51          (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_A) @ sk_D @ sk_D)),
% 0.20/0.51      inference('demod', [status(thm)], ['59', '97'])).
% 0.20/0.51  thf('99', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['56', '98'])).
% 0.20/0.51  thf(fc2_struct_0, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.51       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.51  thf('100', plain,
% 0.20/0.51      (![X26 : $i]:
% 0.20/0.51         (~ (v1_xboole_0 @ (u1_struct_0 @ X26))
% 0.20/0.51          | ~ (l1_struct_0 @ X26)
% 0.20/0.51          | (v2_struct_0 @ X26))),
% 0.20/0.51      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.20/0.51  thf('101', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['99', '100'])).
% 0.20/0.51  thf('102', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(dt_l1_pre_topc, axiom,
% 0.20/0.51    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.51  thf('103', plain,
% 0.20/0.51      (![X23 : $i]: ((l1_struct_0 @ X23) | ~ (l1_pre_topc @ X23))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.51  thf('104', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.51      inference('sup-', [status(thm)], ['102', '103'])).
% 0.20/0.51  thf('105', plain, ((v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('demod', [status(thm)], ['101', '104'])).
% 0.20/0.51  thf('106', plain, ($false), inference('demod', [status(thm)], ['0', '105'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
