%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ATErrn9E0g

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:44 EST 2020

% Result     : Theorem 0.62s
% Output     : Refutation 0.62s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 279 expanded)
%              Number of leaves         :   29 (  95 expanded)
%              Depth                    :   14
%              Number of atoms          :  706 (4021 expanded)
%              Number of equality atoms :   24 ( 111 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t42_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tex_2 @ B @ A )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( r2_hidden @ C @ B )
                 => ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) )
                    = ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v2_tex_2 @ B @ A )
             => ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
                 => ( ( r2_hidden @ C @ B )
                   => ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) )
                      = ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t42_tex_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i] :
      ( ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ X21 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X21 @ X22 ) @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('3',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('5',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ X23 )
      | ( ( k6_domain_1 @ X23 @ X24 )
        = ( k1_tarski @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('6',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 )
      = ( k1_tarski @ sk_C_2 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    r2_hidden @ sk_C_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('9',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ( r2_hidden @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r2_hidden @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('13',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 )
    = ( k1_tarski @ sk_C_2 ) ),
    inference(clc,[status(thm)],['6','13'])).

thf('15',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','14'])).

thf('16',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('17',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t41_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( r1_tarski @ C @ B )
                 => ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) )
                    = C ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v2_tex_2 @ X25 @ X26 )
      | ~ ( r1_tarski @ X27 @ X25 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X26 ) @ X25 @ ( k2_pre_topc @ X26 @ X27 ) )
        = X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t41_tex_2])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_B_1 )
      | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ X0 ) )
        = X0 )
      | ~ ( r1_tarski @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['20','21','22','23'])).

thf('25',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B_1 )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_2 ) ) )
      = ( k1_tarski @ sk_C_2 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','24'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('26',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('27',plain,(
    r2_hidden @ sk_C_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('28',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( m1_subset_1 @ X8 @ X9 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('30',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C_2 @ sk_B_1 ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X21: $i,X22: $i] :
      ( ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ X21 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X21 @ X22 ) @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('33',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ sk_B_1 @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_C_2 @ sk_B_1 ),
    inference('sup-',[status(thm)],['27','30'])).

thf('35',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ X23 )
      | ( ( k6_domain_1 @ X23 @ X24 )
        = ( k1_tarski @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('36',plain,
    ( ( ( k6_domain_1 @ sk_B_1 @ sk_C_2 )
      = ( k1_tarski @ sk_C_2 ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    r2_hidden @ sk_C_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('39',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k6_domain_1 @ sk_B_1 @ sk_C_2 )
    = ( k1_tarski @ sk_C_2 ) ),
    inference(clc,[status(thm)],['36','39'])).

thf('41',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['33','40'])).

thf('42',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('43',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ( r2_hidden @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ sk_C_2 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_tarski @ sk_C_2 ) ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['26','45'])).

thf('47',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('48',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B_1 )
    | ( r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B_1 ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('51',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X17 @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('52',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_2 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_2 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('55',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k9_subset_1 @ X16 @ X14 @ X15 )
        = ( k3_xboole_0 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_2 ) ) )
      = ( k3_xboole_0 @ X0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_2 ) ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( k3_xboole_0 @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_2 ) ) )
      = ( k1_tarski @ sk_C_2 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','49','56'])).

thf('58',plain,(
    ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 ) ) )
 != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 )
    = ( k1_tarski @ sk_C_2 ) ),
    inference(clc,[status(thm)],['6','13'])).

thf('60',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_2 )
    = ( k1_tarski @ sk_C_2 ) ),
    inference(clc,[status(thm)],['6','13'])).

thf('61',plain,(
    ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_2 ) ) )
 != ( k1_tarski @ sk_C_2 ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_2 ) ) )
      = ( k3_xboole_0 @ X0 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_2 ) ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('63',plain,(
    ( k3_xboole_0 @ sk_B_1 @ ( k2_pre_topc @ sk_A @ ( k1_tarski @ sk_C_2 ) ) )
 != ( k1_tarski @ sk_C_2 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['57','63'])).

thf('65',plain,(
    $false ),
    inference(demod,[status(thm)],['0','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ATErrn9E0g
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:30:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.62/0.85  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.62/0.85  % Solved by: fo/fo7.sh
% 0.62/0.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.62/0.85  % done 494 iterations in 0.391s
% 0.62/0.85  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.62/0.85  % SZS output start Refutation
% 0.62/0.85  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.62/0.85  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.62/0.85  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.62/0.85  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.62/0.85  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.62/0.85  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.62/0.85  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.62/0.85  thf(sk_A_type, type, sk_A: $i).
% 0.62/0.85  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.62/0.85  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.62/0.85  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.62/0.85  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.62/0.85  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.62/0.85  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.62/0.85  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.62/0.85  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.62/0.85  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.62/0.85  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.62/0.85  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.62/0.85  thf(t42_tex_2, conjecture,
% 0.62/0.85    (![A:$i]:
% 0.62/0.85     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.62/0.85       ( ![B:$i]:
% 0.62/0.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.62/0.85           ( ( v2_tex_2 @ B @ A ) =>
% 0.62/0.85             ( ![C:$i]:
% 0.62/0.85               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.62/0.85                 ( ( r2_hidden @ C @ B ) =>
% 0.62/0.85                   ( ( k9_subset_1 @
% 0.62/0.85                       ( u1_struct_0 @ A ) @ B @ 
% 0.62/0.85                       ( k2_pre_topc @
% 0.62/0.85                         A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.62/0.85                     ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.62/0.85  thf(zf_stmt_0, negated_conjecture,
% 0.62/0.85    (~( ![A:$i]:
% 0.62/0.85        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.62/0.85            ( l1_pre_topc @ A ) ) =>
% 0.62/0.85          ( ![B:$i]:
% 0.62/0.85            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.62/0.85              ( ( v2_tex_2 @ B @ A ) =>
% 0.62/0.85                ( ![C:$i]:
% 0.62/0.85                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.62/0.85                    ( ( r2_hidden @ C @ B ) =>
% 0.62/0.85                      ( ( k9_subset_1 @
% 0.62/0.85                          ( u1_struct_0 @ A ) @ B @ 
% 0.62/0.85                          ( k2_pre_topc @
% 0.62/0.85                            A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) =
% 0.62/0.85                        ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) )),
% 0.62/0.85    inference('cnf.neg', [status(esa)], [t42_tex_2])).
% 0.62/0.85  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.62/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.85  thf('1', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.62/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.85  thf(dt_k6_domain_1, axiom,
% 0.62/0.85    (![A:$i,B:$i]:
% 0.62/0.85     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.62/0.85       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.62/0.85  thf('2', plain,
% 0.62/0.85      (![X21 : $i, X22 : $i]:
% 0.62/0.85         ((v1_xboole_0 @ X21)
% 0.62/0.85          | ~ (m1_subset_1 @ X22 @ X21)
% 0.62/0.85          | (m1_subset_1 @ (k6_domain_1 @ X21 @ X22) @ (k1_zfmisc_1 @ X21)))),
% 0.62/0.85      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.62/0.85  thf('3', plain,
% 0.62/0.85      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2) @ 
% 0.62/0.85         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.62/0.85        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.62/0.85      inference('sup-', [status(thm)], ['1', '2'])).
% 0.62/0.85  thf('4', plain, ((m1_subset_1 @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.62/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.85  thf(redefinition_k6_domain_1, axiom,
% 0.62/0.85    (![A:$i,B:$i]:
% 0.62/0.85     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.62/0.85       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.62/0.85  thf('5', plain,
% 0.62/0.85      (![X23 : $i, X24 : $i]:
% 0.62/0.85         ((v1_xboole_0 @ X23)
% 0.62/0.85          | ~ (m1_subset_1 @ X24 @ X23)
% 0.62/0.85          | ((k6_domain_1 @ X23 @ X24) = (k1_tarski @ X24)))),
% 0.62/0.85      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.62/0.85  thf('6', plain,
% 0.62/0.85      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2) = (k1_tarski @ sk_C_2))
% 0.62/0.85        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.62/0.85      inference('sup-', [status(thm)], ['4', '5'])).
% 0.62/0.85  thf('7', plain, ((r2_hidden @ sk_C_2 @ sk_B_1)),
% 0.62/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.85  thf('8', plain,
% 0.62/0.85      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.62/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.85  thf(l3_subset_1, axiom,
% 0.62/0.85    (![A:$i,B:$i]:
% 0.62/0.85     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.62/0.85       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.62/0.85  thf('9', plain,
% 0.62/0.85      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.62/0.85         (~ (r2_hidden @ X11 @ X12)
% 0.62/0.85          | (r2_hidden @ X11 @ X13)
% 0.62/0.85          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.62/0.85      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.62/0.85  thf('10', plain,
% 0.62/0.85      (![X0 : $i]:
% 0.62/0.85         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.62/0.85      inference('sup-', [status(thm)], ['8', '9'])).
% 0.62/0.85  thf('11', plain, ((r2_hidden @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.62/0.85      inference('sup-', [status(thm)], ['7', '10'])).
% 0.62/0.85  thf(d1_xboole_0, axiom,
% 0.62/0.85    (![A:$i]:
% 0.62/0.85     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.62/0.85  thf('12', plain,
% 0.62/0.85      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.62/0.85      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.62/0.85  thf('13', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.62/0.85      inference('sup-', [status(thm)], ['11', '12'])).
% 0.62/0.85  thf('14', plain,
% 0.62/0.85      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2) = (k1_tarski @ sk_C_2))),
% 0.62/0.85      inference('clc', [status(thm)], ['6', '13'])).
% 0.62/0.85  thf('15', plain,
% 0.62/0.85      (((m1_subset_1 @ (k1_tarski @ sk_C_2) @ 
% 0.62/0.85         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.62/0.85        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.62/0.85      inference('demod', [status(thm)], ['3', '14'])).
% 0.62/0.85  thf('16', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.62/0.85      inference('sup-', [status(thm)], ['11', '12'])).
% 0.62/0.85  thf('17', plain,
% 0.62/0.85      ((m1_subset_1 @ (k1_tarski @ sk_C_2) @ 
% 0.62/0.85        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.62/0.85      inference('clc', [status(thm)], ['15', '16'])).
% 0.62/0.85  thf('18', plain,
% 0.62/0.85      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.62/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.85  thf(t41_tex_2, axiom,
% 0.62/0.85    (![A:$i]:
% 0.62/0.85     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.62/0.85       ( ![B:$i]:
% 0.62/0.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.62/0.85           ( ( v2_tex_2 @ B @ A ) <=>
% 0.62/0.85             ( ![C:$i]:
% 0.62/0.85               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.62/0.85                 ( ( r1_tarski @ C @ B ) =>
% 0.62/0.85                   ( ( k9_subset_1 @
% 0.62/0.85                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) =
% 0.62/0.85                     ( C ) ) ) ) ) ) ) ) ))).
% 0.62/0.85  thf('19', plain,
% 0.62/0.85      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.62/0.85         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.62/0.85          | ~ (v2_tex_2 @ X25 @ X26)
% 0.62/0.85          | ~ (r1_tarski @ X27 @ X25)
% 0.62/0.85          | ((k9_subset_1 @ (u1_struct_0 @ X26) @ X25 @ 
% 0.62/0.85              (k2_pre_topc @ X26 @ X27)) = (X27))
% 0.62/0.85          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.62/0.85          | ~ (l1_pre_topc @ X26)
% 0.62/0.85          | ~ (v2_pre_topc @ X26)
% 0.62/0.85          | (v2_struct_0 @ X26))),
% 0.62/0.85      inference('cnf', [status(esa)], [t41_tex_2])).
% 0.62/0.85  thf('20', plain,
% 0.62/0.85      (![X0 : $i]:
% 0.62/0.85         ((v2_struct_0 @ sk_A)
% 0.62/0.85          | ~ (v2_pre_topc @ sk_A)
% 0.62/0.85          | ~ (l1_pre_topc @ sk_A)
% 0.62/0.85          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.62/0.85          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.62/0.85              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.62/0.85          | ~ (r1_tarski @ X0 @ sk_B_1)
% 0.62/0.85          | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.62/0.85      inference('sup-', [status(thm)], ['18', '19'])).
% 0.62/0.85  thf('21', plain, ((v2_pre_topc @ sk_A)),
% 0.62/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.85  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.62/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.85  thf('23', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.62/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.85  thf('24', plain,
% 0.62/0.85      (![X0 : $i]:
% 0.62/0.85         ((v2_struct_0 @ sk_A)
% 0.62/0.85          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.62/0.85          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.62/0.85              (k2_pre_topc @ sk_A @ X0)) = (X0))
% 0.62/0.85          | ~ (r1_tarski @ X0 @ sk_B_1))),
% 0.62/0.85      inference('demod', [status(thm)], ['20', '21', '22', '23'])).
% 0.62/0.85  thf('25', plain,
% 0.62/0.85      ((~ (r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B_1)
% 0.62/0.85        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.62/0.85            (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_2))) = (k1_tarski @ sk_C_2))
% 0.62/0.85        | (v2_struct_0 @ sk_A))),
% 0.62/0.85      inference('sup-', [status(thm)], ['17', '24'])).
% 0.62/0.85  thf(d3_tarski, axiom,
% 0.62/0.85    (![A:$i,B:$i]:
% 0.62/0.85     ( ( r1_tarski @ A @ B ) <=>
% 0.62/0.85       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.62/0.85  thf('26', plain,
% 0.62/0.85      (![X4 : $i, X6 : $i]:
% 0.62/0.85         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.62/0.85      inference('cnf', [status(esa)], [d3_tarski])).
% 0.62/0.85  thf('27', plain, ((r2_hidden @ sk_C_2 @ sk_B_1)),
% 0.62/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.85  thf(d2_subset_1, axiom,
% 0.62/0.85    (![A:$i,B:$i]:
% 0.62/0.85     ( ( ( v1_xboole_0 @ A ) =>
% 0.62/0.85         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.62/0.85       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.62/0.85         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.62/0.85  thf('28', plain,
% 0.62/0.85      (![X8 : $i, X9 : $i]:
% 0.62/0.85         (~ (r2_hidden @ X8 @ X9)
% 0.62/0.85          | (m1_subset_1 @ X8 @ X9)
% 0.62/0.85          | (v1_xboole_0 @ X9))),
% 0.62/0.85      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.62/0.85  thf('29', plain,
% 0.62/0.85      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.62/0.85      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.62/0.85  thf('30', plain,
% 0.62/0.85      (![X8 : $i, X9 : $i]: ((m1_subset_1 @ X8 @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 0.62/0.85      inference('clc', [status(thm)], ['28', '29'])).
% 0.62/0.85  thf('31', plain, ((m1_subset_1 @ sk_C_2 @ sk_B_1)),
% 0.62/0.85      inference('sup-', [status(thm)], ['27', '30'])).
% 0.62/0.85  thf('32', plain,
% 0.62/0.85      (![X21 : $i, X22 : $i]:
% 0.62/0.85         ((v1_xboole_0 @ X21)
% 0.62/0.85          | ~ (m1_subset_1 @ X22 @ X21)
% 0.62/0.85          | (m1_subset_1 @ (k6_domain_1 @ X21 @ X22) @ (k1_zfmisc_1 @ X21)))),
% 0.62/0.85      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.62/0.85  thf('33', plain,
% 0.62/0.85      (((m1_subset_1 @ (k6_domain_1 @ sk_B_1 @ sk_C_2) @ (k1_zfmisc_1 @ sk_B_1))
% 0.62/0.85        | (v1_xboole_0 @ sk_B_1))),
% 0.62/0.85      inference('sup-', [status(thm)], ['31', '32'])).
% 0.62/0.85  thf('34', plain, ((m1_subset_1 @ sk_C_2 @ sk_B_1)),
% 0.62/0.85      inference('sup-', [status(thm)], ['27', '30'])).
% 0.62/0.85  thf('35', plain,
% 0.62/0.85      (![X23 : $i, X24 : $i]:
% 0.62/0.85         ((v1_xboole_0 @ X23)
% 0.62/0.85          | ~ (m1_subset_1 @ X24 @ X23)
% 0.62/0.85          | ((k6_domain_1 @ X23 @ X24) = (k1_tarski @ X24)))),
% 0.62/0.85      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.62/0.85  thf('36', plain,
% 0.62/0.85      ((((k6_domain_1 @ sk_B_1 @ sk_C_2) = (k1_tarski @ sk_C_2))
% 0.62/0.85        | (v1_xboole_0 @ sk_B_1))),
% 0.62/0.85      inference('sup-', [status(thm)], ['34', '35'])).
% 0.62/0.85  thf('37', plain, ((r2_hidden @ sk_C_2 @ sk_B_1)),
% 0.62/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.85  thf('38', plain,
% 0.62/0.85      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.62/0.85      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.62/0.85  thf('39', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.62/0.85      inference('sup-', [status(thm)], ['37', '38'])).
% 0.62/0.85  thf('40', plain, (((k6_domain_1 @ sk_B_1 @ sk_C_2) = (k1_tarski @ sk_C_2))),
% 0.62/0.85      inference('clc', [status(thm)], ['36', '39'])).
% 0.62/0.85  thf('41', plain,
% 0.62/0.85      (((m1_subset_1 @ (k1_tarski @ sk_C_2) @ (k1_zfmisc_1 @ sk_B_1))
% 0.62/0.85        | (v1_xboole_0 @ sk_B_1))),
% 0.62/0.85      inference('demod', [status(thm)], ['33', '40'])).
% 0.62/0.85  thf('42', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.62/0.85      inference('sup-', [status(thm)], ['37', '38'])).
% 0.62/0.85  thf('43', plain,
% 0.62/0.85      ((m1_subset_1 @ (k1_tarski @ sk_C_2) @ (k1_zfmisc_1 @ sk_B_1))),
% 0.62/0.85      inference('clc', [status(thm)], ['41', '42'])).
% 0.62/0.85  thf('44', plain,
% 0.62/0.85      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.62/0.85         (~ (r2_hidden @ X11 @ X12)
% 0.62/0.85          | (r2_hidden @ X11 @ X13)
% 0.62/0.85          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.62/0.85      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.62/0.85  thf('45', plain,
% 0.62/0.85      (![X0 : $i]:
% 0.62/0.85         ((r2_hidden @ X0 @ sk_B_1) | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_C_2)))),
% 0.62/0.85      inference('sup-', [status(thm)], ['43', '44'])).
% 0.62/0.85  thf('46', plain,
% 0.62/0.85      (![X0 : $i]:
% 0.62/0.85         ((r1_tarski @ (k1_tarski @ sk_C_2) @ X0)
% 0.62/0.85          | (r2_hidden @ (sk_C @ X0 @ (k1_tarski @ sk_C_2)) @ sk_B_1))),
% 0.62/0.85      inference('sup-', [status(thm)], ['26', '45'])).
% 0.62/0.85  thf('47', plain,
% 0.62/0.85      (![X4 : $i, X6 : $i]:
% 0.62/0.85         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.62/0.85      inference('cnf', [status(esa)], [d3_tarski])).
% 0.62/0.85  thf('48', plain,
% 0.62/0.85      (((r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B_1)
% 0.62/0.85        | (r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B_1))),
% 0.62/0.85      inference('sup-', [status(thm)], ['46', '47'])).
% 0.62/0.85  thf('49', plain, ((r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B_1)),
% 0.62/0.85      inference('simplify', [status(thm)], ['48'])).
% 0.62/0.85  thf('50', plain,
% 0.62/0.85      ((m1_subset_1 @ (k1_tarski @ sk_C_2) @ 
% 0.62/0.85        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.62/0.85      inference('clc', [status(thm)], ['15', '16'])).
% 0.62/0.85  thf(dt_k2_pre_topc, axiom,
% 0.62/0.85    (![A:$i,B:$i]:
% 0.62/0.85     ( ( ( l1_pre_topc @ A ) & 
% 0.62/0.85         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.62/0.85       ( m1_subset_1 @
% 0.62/0.85         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.62/0.85  thf('51', plain,
% 0.62/0.85      (![X17 : $i, X18 : $i]:
% 0.62/0.85         (~ (l1_pre_topc @ X17)
% 0.62/0.85          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.62/0.85          | (m1_subset_1 @ (k2_pre_topc @ X17 @ X18) @ 
% 0.62/0.85             (k1_zfmisc_1 @ (u1_struct_0 @ X17))))),
% 0.62/0.85      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.62/0.85  thf('52', plain,
% 0.62/0.85      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_2)) @ 
% 0.62/0.85         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.62/0.85        | ~ (l1_pre_topc @ sk_A))),
% 0.62/0.85      inference('sup-', [status(thm)], ['50', '51'])).
% 0.62/0.85  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.62/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.85  thf('54', plain,
% 0.62/0.85      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_2)) @ 
% 0.62/0.85        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.62/0.85      inference('demod', [status(thm)], ['52', '53'])).
% 0.62/0.85  thf(redefinition_k9_subset_1, axiom,
% 0.62/0.85    (![A:$i,B:$i,C:$i]:
% 0.62/0.85     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.62/0.85       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.62/0.85  thf('55', plain,
% 0.62/0.85      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.62/0.85         (((k9_subset_1 @ X16 @ X14 @ X15) = (k3_xboole_0 @ X14 @ X15))
% 0.62/0.85          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.62/0.85      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.62/0.85  thf('56', plain,
% 0.62/0.85      (![X0 : $i]:
% 0.62/0.85         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.62/0.85           (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_2)))
% 0.62/0.85           = (k3_xboole_0 @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_2))))),
% 0.62/0.85      inference('sup-', [status(thm)], ['54', '55'])).
% 0.62/0.85  thf('57', plain,
% 0.62/0.85      ((((k3_xboole_0 @ sk_B_1 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_2)))
% 0.62/0.85          = (k1_tarski @ sk_C_2))
% 0.62/0.85        | (v2_struct_0 @ sk_A))),
% 0.62/0.85      inference('demod', [status(thm)], ['25', '49', '56'])).
% 0.62/0.85  thf('58', plain,
% 0.62/0.85      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.62/0.85         (k2_pre_topc @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2)))
% 0.62/0.85         != (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2))),
% 0.62/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.85  thf('59', plain,
% 0.62/0.85      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2) = (k1_tarski @ sk_C_2))),
% 0.62/0.85      inference('clc', [status(thm)], ['6', '13'])).
% 0.62/0.85  thf('60', plain,
% 0.62/0.85      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_2) = (k1_tarski @ sk_C_2))),
% 0.62/0.85      inference('clc', [status(thm)], ['6', '13'])).
% 0.62/0.85  thf('61', plain,
% 0.62/0.85      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.62/0.85         (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_2))) != (k1_tarski @ sk_C_2))),
% 0.62/0.85      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.62/0.85  thf('62', plain,
% 0.62/0.85      (![X0 : $i]:
% 0.62/0.85         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.62/0.85           (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_2)))
% 0.62/0.85           = (k3_xboole_0 @ X0 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_2))))),
% 0.62/0.85      inference('sup-', [status(thm)], ['54', '55'])).
% 0.62/0.85  thf('63', plain,
% 0.62/0.85      (((k3_xboole_0 @ sk_B_1 @ (k2_pre_topc @ sk_A @ (k1_tarski @ sk_C_2)))
% 0.62/0.85         != (k1_tarski @ sk_C_2))),
% 0.62/0.85      inference('demod', [status(thm)], ['61', '62'])).
% 0.62/0.85  thf('64', plain, ((v2_struct_0 @ sk_A)),
% 0.62/0.85      inference('simplify_reflect-', [status(thm)], ['57', '63'])).
% 0.62/0.85  thf('65', plain, ($false), inference('demod', [status(thm)], ['0', '64'])).
% 0.62/0.85  
% 0.62/0.85  % SZS output end Refutation
% 0.62/0.85  
% 0.62/0.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
