%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GAFY8RfxSs

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:44 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 243 expanded)
%              Number of leaves         :   42 (  99 expanded)
%              Depth                    :   18
%              Number of atoms          : 1063 (2831 expanded)
%              Number of equality atoms :   60 ( 156 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t15_yellow19,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) )
            & ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
            & ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) )
         => ( B
            = ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_struct_0 @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) )
              & ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
              & ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) )
           => ( B
              = ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t15_yellow19])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C @ X10 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t17_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X19 ) @ ( k1_tarski @ X20 ) )
      | ( X19 = X20 ) ) ),
    inference(cnf,[status(esa)],[t17_zfmisc_1])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('3',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X17 ) @ X18 )
      | ~ ( r2_hidden @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C @ X10 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('7',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('8',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('9',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('10',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('12',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t2_yellow19,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) )
            & ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) )
            & ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) )
         => ! [C: $i] :
              ~ ( ( r2_hidden @ C @ B )
                & ( v1_xboole_0 @ C ) ) ) ) )).

thf('14',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v1_xboole_0 @ X31 )
      | ~ ( v1_subset_1 @ X31 @ ( u1_struct_0 @ ( k3_yellow_1 @ X32 ) ) )
      | ~ ( v2_waybel_0 @ X31 @ ( k3_yellow_1 @ X32 ) )
      | ~ ( v13_waybel_0 @ X31 @ ( k3_yellow_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X32 ) ) ) )
      | ~ ( r2_hidden @ X33 @ X31 )
      | ~ ( v1_xboole_0 @ X33 )
      | ( v1_xboole_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t2_yellow19])).

thf('15',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf(t4_waybel_7,axiom,(
    ! [A: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ A ) )
      = ( k9_setfam_1 @ A ) ) )).

thf('16',plain,(
    ! [X28: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X28 ) )
      = ( k9_setfam_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t4_waybel_7])).

thf('17',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('18',plain,(
    ! [X28: $i] :
      ( ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X28 ) ) )
      = ( k9_setfam_1 @ X28 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('20',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('21',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('22',plain,(
    ! [X28: $i] :
      ( ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X28 ) ) )
      = ( k9_setfam_1 @ X28 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('23',plain,(
    ! [X24: $i] :
      ( ( k9_setfam_1 @ X24 )
      = ( k1_zfmisc_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('24',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v1_xboole_0 @ X31 )
      | ~ ( v1_subset_1 @ X31 @ ( k9_setfam_1 @ X32 ) )
      | ~ ( v2_waybel_0 @ X31 @ ( k3_lattice3 @ ( k1_lattice3 @ X32 ) ) )
      | ~ ( v13_waybel_0 @ X31 @ ( k3_lattice3 @ ( k1_lattice3 @ X32 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k9_setfam_1 @ ( k9_setfam_1 @ X32 ) ) )
      | ~ ( r2_hidden @ X33 @ X31 )
      | ~ ( v1_xboole_0 @ X33 )
      | ( v1_xboole_0 @ X32 ) ) ),
    inference(demod,[status(thm)],['14','15','18','19','20','21','22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['13','24'])).

thf('26',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('27',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('29',plain,(
    ! [X28: $i] :
      ( ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X28 ) ) )
      = ( k9_setfam_1 @ X28 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('30',plain,(
    ! [X24: $i] :
      ( ( k9_setfam_1 @ X24 )
      = ( k1_zfmisc_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('31',plain,(
    m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['27','28','29','30'])).

thf('32',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['26','31'])).

thf('33',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('36',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('38',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf('40',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('43',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('45',plain,(
    ! [X28: $i] :
      ( ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X28 ) ) )
      = ( k9_setfam_1 @ X28 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('46',plain,(
    v1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['42','46'])).

thf('48',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['25','34','41','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ ( sk_C @ X0 @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ sk_B_1 @ ( k1_tarski @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( r1_xboole_0 @ sk_B_1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_xboole_0 @ sk_B_1 @ ( k1_tarski @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('54',plain,(
    ! [X26: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ sk_B_1 @ ( k1_tarski @ X0 ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ sk_B_1 @ ( k1_tarski @ X0 ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('58',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ X0 ) )
        = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    sk_B_1
 != ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t14_yellow19,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
            & ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) )
         => ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) @ B @ ( k1_tarski @ k1_xboole_0 ) )
            = ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) )).

thf('62',plain,(
    ! [X29: $i,X30: $i] :
      ( ( v1_xboole_0 @ X29 )
      | ~ ( v2_waybel_0 @ X29 @ ( k3_yellow_1 @ ( k2_struct_0 @ X30 ) ) )
      | ~ ( v13_waybel_0 @ X29 @ ( k3_yellow_1 @ ( k2_struct_0 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X30 ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X30 ) ) ) @ X29 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X30 @ ( k3_yellow19 @ X30 @ ( k2_struct_0 @ X30 ) @ X29 ) ) )
      | ~ ( l1_struct_0 @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow19])).

thf('63',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('64',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('65',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('66',plain,(
    ! [X28: $i] :
      ( ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X28 ) ) )
      = ( k9_setfam_1 @ X28 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('67',plain,(
    ! [X24: $i] :
      ( ( k9_setfam_1 @ X24 )
      = ( k1_zfmisc_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('68',plain,(
    ! [X27: $i] :
      ( ( k3_yellow_1 @ X27 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('69',plain,(
    ! [X28: $i] :
      ( ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X28 ) ) )
      = ( k9_setfam_1 @ X28 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('70',plain,(
    ! [X29: $i,X30: $i] :
      ( ( v1_xboole_0 @ X29 )
      | ~ ( v2_waybel_0 @ X29 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X30 ) ) ) )
      | ~ ( v13_waybel_0 @ X29 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X30 ) ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ X30 ) ) ) )
      | ( ( k7_subset_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ X30 ) ) @ X29 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X30 @ ( k3_yellow19 @ X30 @ ( k2_struct_0 @ X30 ) @ X29 ) ) )
      | ~ ( l1_struct_0 @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(demod,[status(thm)],['62','63','64','65','66','67','68','69'])).

thf('71',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k7_subset_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ sk_A ) ) @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['61','70'])).

thf('72',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['27','28','29','30'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('74',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ( ( k7_subset_1 @ X22 @ X21 @ X23 )
        = ( k4_xboole_0 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('75',plain,(
    ! [X24: $i] :
      ( ( k9_setfam_1 @ X24 )
      = ( k1_zfmisc_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('76',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k9_setfam_1 @ X22 ) )
      | ( ( k7_subset_1 @ X22 @ X21 @ X23 )
        = ( k4_xboole_0 @ X21 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ sk_A ) ) @ sk_B_1 @ X0 )
      = ( k4_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['27','28','29','30'])).

thf('79',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['71','72','77','78','79'])).

thf('81',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) )
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('85',plain,(
    sk_B_1
 != ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['60','84'])).

thf('86',plain,
    ( ( sk_B_1 != sk_B_1 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['59','85'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('87',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('88',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X13 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('89',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ~ ( r2_hidden @ X7 @ X5 )
      | ( X6
       != ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('90',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['91'])).

thf('93',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['87','92'])).

thf('94',plain,
    ( ( sk_B_1 != sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['86','93'])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,(
    $false ),
    inference(demod,[status(thm)],['0','97'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GAFY8RfxSs
% 0.17/0.37  % Computer   : n010.cluster.edu
% 0.17/0.37  % Model      : x86_64 x86_64
% 0.17/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.37  % Memory     : 8042.1875MB
% 0.17/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.37  % CPULimit   : 60
% 0.17/0.37  % DateTime   : Tue Dec  1 19:30:59 EST 2020
% 0.17/0.37  % CPUTime    : 
% 0.17/0.37  % Running portfolio for 600 s
% 0.17/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.37  % Number of cores: 8
% 0.17/0.37  % Python version: Python 3.6.8
% 0.17/0.38  % Running in FO mode
% 0.90/1.06  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.90/1.06  % Solved by: fo/fo7.sh
% 0.90/1.06  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.06  % done 992 iterations in 0.581s
% 0.90/1.06  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.90/1.06  % SZS output start Refutation
% 0.90/1.06  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.90/1.06  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.90/1.06  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.90/1.06  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.90/1.06  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.90/1.06  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.90/1.06  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.90/1.06  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.90/1.06  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.90/1.06  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.90/1.06  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.90/1.06  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.90/1.06  thf(sk_B_type, type, sk_B: $i > $i).
% 0.90/1.06  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.90/1.06  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.90/1.06  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.90/1.06  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.90/1.06  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.90/1.06  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.90/1.06  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.90/1.06  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.90/1.06  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.90/1.06  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.90/1.06  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.90/1.06  thf(k9_setfam_1_type, type, k9_setfam_1: $i > $i).
% 0.90/1.06  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.06  thf(t15_yellow19, conjecture,
% 0.90/1.06    (![A:$i]:
% 0.90/1.06     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.90/1.06       ( ![B:$i]:
% 0.90/1.06         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.90/1.06             ( v1_subset_1 @
% 0.90/1.06               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.90/1.06             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.90/1.06             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.90/1.06             ( m1_subset_1 @
% 0.90/1.06               B @ 
% 0.90/1.06               ( k1_zfmisc_1 @
% 0.90/1.06                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.90/1.06           ( ( B ) =
% 0.90/1.06             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.90/1.06  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.06    (~( ![A:$i]:
% 0.90/1.06        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.90/1.06          ( ![B:$i]:
% 0.90/1.06            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.90/1.06                ( v1_subset_1 @
% 0.90/1.06                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.90/1.06                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.90/1.06                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.90/1.06                ( m1_subset_1 @
% 0.90/1.06                  B @ 
% 0.90/1.06                  ( k1_zfmisc_1 @
% 0.90/1.06                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.90/1.06              ( ( B ) =
% 0.90/1.06                ( k2_yellow19 @
% 0.90/1.06                  A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.90/1.06    inference('cnf.neg', [status(esa)], [t15_yellow19])).
% 0.90/1.06  thf('0', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf(t3_xboole_0, axiom,
% 0.90/1.06    (![A:$i,B:$i]:
% 0.90/1.06     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.90/1.06            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.90/1.06       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.90/1.06            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.90/1.06  thf('1', plain,
% 0.90/1.06      (![X9 : $i, X10 : $i]:
% 0.90/1.06         ((r1_xboole_0 @ X9 @ X10) | (r2_hidden @ (sk_C @ X10 @ X9) @ X10))),
% 0.90/1.06      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.90/1.06  thf(t17_zfmisc_1, axiom,
% 0.90/1.06    (![A:$i,B:$i]:
% 0.90/1.06     ( ( ( A ) != ( B ) ) =>
% 0.90/1.06       ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.90/1.06  thf('2', plain,
% 0.90/1.06      (![X19 : $i, X20 : $i]:
% 0.90/1.06         ((r1_xboole_0 @ (k1_tarski @ X19) @ (k1_tarski @ X20))
% 0.90/1.06          | ((X19) = (X20)))),
% 0.90/1.06      inference('cnf', [status(esa)], [t17_zfmisc_1])).
% 0.90/1.06  thf(l24_zfmisc_1, axiom,
% 0.90/1.06    (![A:$i,B:$i]:
% 0.90/1.06     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.90/1.06  thf('3', plain,
% 0.90/1.06      (![X17 : $i, X18 : $i]:
% 0.90/1.06         (~ (r1_xboole_0 @ (k1_tarski @ X17) @ X18) | ~ (r2_hidden @ X17 @ X18))),
% 0.90/1.06      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.90/1.06  thf('4', plain,
% 0.90/1.06      (![X0 : $i, X1 : $i]:
% 0.90/1.06         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.90/1.06      inference('sup-', [status(thm)], ['2', '3'])).
% 0.90/1.06  thf('5', plain,
% 0.90/1.06      (![X0 : $i, X1 : $i]:
% 0.90/1.06         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.90/1.06          | ((sk_C @ (k1_tarski @ X0) @ X1) = (X0)))),
% 0.90/1.06      inference('sup-', [status(thm)], ['1', '4'])).
% 0.90/1.06  thf('6', plain,
% 0.90/1.06      (![X9 : $i, X10 : $i]:
% 0.90/1.06         ((r1_xboole_0 @ X9 @ X10) | (r2_hidden @ (sk_C @ X10 @ X9) @ X9))),
% 0.90/1.06      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.90/1.06  thf(d3_struct_0, axiom,
% 0.90/1.06    (![A:$i]:
% 0.90/1.06     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.90/1.06  thf('7', plain,
% 0.90/1.06      (![X25 : $i]:
% 0.90/1.06         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.90/1.06      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.90/1.06  thf('8', plain,
% 0.90/1.06      ((v2_waybel_0 @ sk_B_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf(d2_yellow_1, axiom,
% 0.90/1.06    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.90/1.06  thf('9', plain,
% 0.90/1.06      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.90/1.06      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.90/1.06  thf('10', plain,
% 0.90/1.06      ((v2_waybel_0 @ sk_B_1 @ 
% 0.90/1.06        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.90/1.06      inference('demod', [status(thm)], ['8', '9'])).
% 0.90/1.06  thf('11', plain,
% 0.90/1.06      (((v2_waybel_0 @ sk_B_1 @ 
% 0.90/1.06         (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.90/1.06        | ~ (l1_struct_0 @ sk_A))),
% 0.90/1.06      inference('sup+', [status(thm)], ['7', '10'])).
% 0.90/1.06  thf('12', plain, ((l1_struct_0 @ sk_A)),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf('13', plain,
% 0.90/1.06      ((v2_waybel_0 @ sk_B_1 @ 
% 0.90/1.06        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.90/1.06      inference('demod', [status(thm)], ['11', '12'])).
% 0.90/1.06  thf(t2_yellow19, axiom,
% 0.90/1.06    (![A:$i]:
% 0.90/1.06     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.90/1.06       ( ![B:$i]:
% 0.90/1.06         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.90/1.06             ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) & 
% 0.90/1.06             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.90/1.06             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.90/1.06             ( m1_subset_1 @
% 0.90/1.06               B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) ) =>
% 0.90/1.06           ( ![C:$i]: ( ~( ( r2_hidden @ C @ B ) & ( v1_xboole_0 @ C ) ) ) ) ) ) ))).
% 0.90/1.06  thf('14', plain,
% 0.90/1.06      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.90/1.06         ((v1_xboole_0 @ X31)
% 0.90/1.06          | ~ (v1_subset_1 @ X31 @ (u1_struct_0 @ (k3_yellow_1 @ X32)))
% 0.90/1.06          | ~ (v2_waybel_0 @ X31 @ (k3_yellow_1 @ X32))
% 0.90/1.06          | ~ (v13_waybel_0 @ X31 @ (k3_yellow_1 @ X32))
% 0.90/1.06          | ~ (m1_subset_1 @ X31 @ 
% 0.90/1.06               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X32))))
% 0.90/1.06          | ~ (r2_hidden @ X33 @ X31)
% 0.90/1.06          | ~ (v1_xboole_0 @ X33)
% 0.90/1.06          | (v1_xboole_0 @ X32))),
% 0.90/1.06      inference('cnf', [status(esa)], [t2_yellow19])).
% 0.90/1.06  thf('15', plain,
% 0.90/1.06      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.90/1.06      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.90/1.06  thf(t4_waybel_7, axiom,
% 0.90/1.06    (![A:$i]: ( ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) = ( k9_setfam_1 @ A ) ))).
% 0.90/1.06  thf('16', plain,
% 0.90/1.06      (![X28 : $i]: ((u1_struct_0 @ (k3_yellow_1 @ X28)) = (k9_setfam_1 @ X28))),
% 0.90/1.06      inference('cnf', [status(esa)], [t4_waybel_7])).
% 0.90/1.06  thf('17', plain,
% 0.90/1.06      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.90/1.06      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.90/1.06  thf('18', plain,
% 0.90/1.06      (![X28 : $i]:
% 0.90/1.06         ((u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X28)))
% 0.90/1.06           = (k9_setfam_1 @ X28))),
% 0.90/1.06      inference('demod', [status(thm)], ['16', '17'])).
% 0.90/1.06  thf('19', plain,
% 0.90/1.06      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.90/1.06      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.90/1.06  thf('20', plain,
% 0.90/1.06      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.90/1.06      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.90/1.06  thf('21', plain,
% 0.90/1.06      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.90/1.06      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.90/1.06  thf('22', plain,
% 0.90/1.06      (![X28 : $i]:
% 0.90/1.06         ((u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X28)))
% 0.90/1.06           = (k9_setfam_1 @ X28))),
% 0.90/1.06      inference('demod', [status(thm)], ['16', '17'])).
% 0.90/1.06  thf(redefinition_k9_setfam_1, axiom,
% 0.90/1.06    (![A:$i]: ( ( k9_setfam_1 @ A ) = ( k1_zfmisc_1 @ A ) ))).
% 0.90/1.06  thf('23', plain, (![X24 : $i]: ((k9_setfam_1 @ X24) = (k1_zfmisc_1 @ X24))),
% 0.90/1.06      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.90/1.06  thf('24', plain,
% 0.90/1.06      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.90/1.06         ((v1_xboole_0 @ X31)
% 0.90/1.06          | ~ (v1_subset_1 @ X31 @ (k9_setfam_1 @ X32))
% 0.90/1.06          | ~ (v2_waybel_0 @ X31 @ (k3_lattice3 @ (k1_lattice3 @ X32)))
% 0.90/1.06          | ~ (v13_waybel_0 @ X31 @ (k3_lattice3 @ (k1_lattice3 @ X32)))
% 0.90/1.06          | ~ (m1_subset_1 @ X31 @ (k9_setfam_1 @ (k9_setfam_1 @ X32)))
% 0.90/1.06          | ~ (r2_hidden @ X33 @ X31)
% 0.90/1.06          | ~ (v1_xboole_0 @ X33)
% 0.90/1.06          | (v1_xboole_0 @ X32))),
% 0.90/1.06      inference('demod', [status(thm)],
% 0.90/1.06                ['14', '15', '18', '19', '20', '21', '22', '23'])).
% 0.90/1.06  thf('25', plain,
% 0.90/1.06      (![X0 : $i]:
% 0.90/1.06         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.90/1.06          | ~ (v1_xboole_0 @ X0)
% 0.90/1.06          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.90/1.06          | ~ (m1_subset_1 @ sk_B_1 @ 
% 0.90/1.06               (k9_setfam_1 @ (k9_setfam_1 @ (u1_struct_0 @ sk_A))))
% 0.90/1.06          | ~ (v13_waybel_0 @ sk_B_1 @ 
% 0.90/1.06               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.90/1.06          | ~ (v1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ (u1_struct_0 @ sk_A)))
% 0.90/1.06          | (v1_xboole_0 @ sk_B_1))),
% 0.90/1.06      inference('sup-', [status(thm)], ['13', '24'])).
% 0.90/1.06  thf('26', plain,
% 0.90/1.06      (![X25 : $i]:
% 0.90/1.06         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.90/1.06      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.90/1.06  thf('27', plain,
% 0.90/1.06      ((m1_subset_1 @ sk_B_1 @ 
% 0.90/1.06        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf('28', plain,
% 0.90/1.06      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.90/1.06      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.90/1.06  thf('29', plain,
% 0.90/1.06      (![X28 : $i]:
% 0.90/1.06         ((u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X28)))
% 0.90/1.06           = (k9_setfam_1 @ X28))),
% 0.90/1.06      inference('demod', [status(thm)], ['16', '17'])).
% 0.90/1.06  thf('30', plain, (![X24 : $i]: ((k9_setfam_1 @ X24) = (k1_zfmisc_1 @ X24))),
% 0.90/1.06      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.90/1.06  thf('31', plain,
% 0.90/1.06      ((m1_subset_1 @ sk_B_1 @ 
% 0.90/1.06        (k9_setfam_1 @ (k9_setfam_1 @ (k2_struct_0 @ sk_A))))),
% 0.90/1.06      inference('demod', [status(thm)], ['27', '28', '29', '30'])).
% 0.90/1.06  thf('32', plain,
% 0.90/1.06      (((m1_subset_1 @ sk_B_1 @ 
% 0.90/1.06         (k9_setfam_1 @ (k9_setfam_1 @ (u1_struct_0 @ sk_A))))
% 0.90/1.06        | ~ (l1_struct_0 @ sk_A))),
% 0.90/1.06      inference('sup+', [status(thm)], ['26', '31'])).
% 0.90/1.06  thf('33', plain, ((l1_struct_0 @ sk_A)),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf('34', plain,
% 0.90/1.06      ((m1_subset_1 @ sk_B_1 @ 
% 0.90/1.06        (k9_setfam_1 @ (k9_setfam_1 @ (u1_struct_0 @ sk_A))))),
% 0.90/1.06      inference('demod', [status(thm)], ['32', '33'])).
% 0.90/1.06  thf('35', plain,
% 0.90/1.06      (![X25 : $i]:
% 0.90/1.06         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.90/1.06      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.90/1.06  thf('36', plain,
% 0.90/1.06      ((v13_waybel_0 @ sk_B_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf('37', plain,
% 0.90/1.06      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.90/1.06      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.90/1.06  thf('38', plain,
% 0.90/1.06      ((v13_waybel_0 @ sk_B_1 @ 
% 0.90/1.06        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.90/1.06      inference('demod', [status(thm)], ['36', '37'])).
% 0.90/1.06  thf('39', plain,
% 0.90/1.06      (((v13_waybel_0 @ sk_B_1 @ 
% 0.90/1.06         (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.90/1.06        | ~ (l1_struct_0 @ sk_A))),
% 0.90/1.06      inference('sup+', [status(thm)], ['35', '38'])).
% 0.90/1.06  thf('40', plain, ((l1_struct_0 @ sk_A)),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf('41', plain,
% 0.90/1.06      ((v13_waybel_0 @ sk_B_1 @ 
% 0.90/1.06        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.90/1.06      inference('demod', [status(thm)], ['39', '40'])).
% 0.90/1.06  thf('42', plain,
% 0.90/1.06      (![X25 : $i]:
% 0.90/1.06         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.90/1.06      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.90/1.06  thf('43', plain,
% 0.90/1.06      ((v1_subset_1 @ sk_B_1 @ 
% 0.90/1.06        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf('44', plain,
% 0.90/1.06      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.90/1.06      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.90/1.06  thf('45', plain,
% 0.90/1.06      (![X28 : $i]:
% 0.90/1.06         ((u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X28)))
% 0.90/1.06           = (k9_setfam_1 @ X28))),
% 0.90/1.06      inference('demod', [status(thm)], ['16', '17'])).
% 0.90/1.06  thf('46', plain,
% 0.90/1.06      ((v1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ (k2_struct_0 @ sk_A)))),
% 0.90/1.06      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.90/1.06  thf('47', plain,
% 0.90/1.06      (((v1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ (u1_struct_0 @ sk_A)))
% 0.90/1.06        | ~ (l1_struct_0 @ sk_A))),
% 0.90/1.06      inference('sup+', [status(thm)], ['42', '46'])).
% 0.90/1.06  thf('48', plain, ((l1_struct_0 @ sk_A)),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf('49', plain,
% 0.90/1.06      ((v1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.06      inference('demod', [status(thm)], ['47', '48'])).
% 0.90/1.06  thf('50', plain,
% 0.90/1.06      (![X0 : $i]:
% 0.90/1.06         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.90/1.06          | ~ (v1_xboole_0 @ X0)
% 0.90/1.06          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.90/1.06          | (v1_xboole_0 @ sk_B_1))),
% 0.90/1.06      inference('demod', [status(thm)], ['25', '34', '41', '49'])).
% 0.90/1.06  thf('51', plain,
% 0.90/1.06      (![X0 : $i]:
% 0.90/1.06         ((r1_xboole_0 @ sk_B_1 @ X0)
% 0.90/1.06          | (v1_xboole_0 @ sk_B_1)
% 0.90/1.06          | ~ (v1_xboole_0 @ (sk_C @ X0 @ sk_B_1))
% 0.90/1.06          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.90/1.06      inference('sup-', [status(thm)], ['6', '50'])).
% 0.90/1.06  thf('52', plain,
% 0.90/1.06      (![X0 : $i]:
% 0.90/1.06         (~ (v1_xboole_0 @ X0)
% 0.90/1.06          | (r1_xboole_0 @ sk_B_1 @ (k1_tarski @ X0))
% 0.90/1.06          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.90/1.06          | (v1_xboole_0 @ sk_B_1)
% 0.90/1.06          | (r1_xboole_0 @ sk_B_1 @ (k1_tarski @ X0)))),
% 0.90/1.06      inference('sup-', [status(thm)], ['5', '51'])).
% 0.90/1.06  thf('53', plain,
% 0.90/1.06      (![X0 : $i]:
% 0.90/1.06         ((v1_xboole_0 @ sk_B_1)
% 0.90/1.06          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.90/1.06          | (r1_xboole_0 @ sk_B_1 @ (k1_tarski @ X0))
% 0.90/1.06          | ~ (v1_xboole_0 @ X0))),
% 0.90/1.06      inference('simplify', [status(thm)], ['52'])).
% 0.90/1.06  thf(fc2_struct_0, axiom,
% 0.90/1.06    (![A:$i]:
% 0.90/1.06     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.90/1.06       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.90/1.06  thf('54', plain,
% 0.90/1.06      (![X26 : $i]:
% 0.90/1.06         (~ (v1_xboole_0 @ (u1_struct_0 @ X26))
% 0.90/1.06          | ~ (l1_struct_0 @ X26)
% 0.90/1.06          | (v2_struct_0 @ X26))),
% 0.90/1.06      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.90/1.06  thf('55', plain,
% 0.90/1.06      (![X0 : $i]:
% 0.90/1.06         (~ (v1_xboole_0 @ X0)
% 0.90/1.06          | (r1_xboole_0 @ sk_B_1 @ (k1_tarski @ X0))
% 0.90/1.06          | (v1_xboole_0 @ sk_B_1)
% 0.90/1.06          | (v2_struct_0 @ sk_A)
% 0.90/1.06          | ~ (l1_struct_0 @ sk_A))),
% 0.90/1.06      inference('sup-', [status(thm)], ['53', '54'])).
% 0.90/1.06  thf('56', plain, ((l1_struct_0 @ sk_A)),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf('57', plain,
% 0.90/1.06      (![X0 : $i]:
% 0.90/1.06         (~ (v1_xboole_0 @ X0)
% 0.90/1.06          | (r1_xboole_0 @ sk_B_1 @ (k1_tarski @ X0))
% 0.90/1.06          | (v1_xboole_0 @ sk_B_1)
% 0.90/1.06          | (v2_struct_0 @ sk_A))),
% 0.90/1.06      inference('demod', [status(thm)], ['55', '56'])).
% 0.90/1.06  thf(t83_xboole_1, axiom,
% 0.90/1.06    (![A:$i,B:$i]:
% 0.90/1.06     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.90/1.06  thf('58', plain,
% 0.90/1.06      (![X14 : $i, X15 : $i]:
% 0.90/1.06         (((k4_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_xboole_0 @ X14 @ X15))),
% 0.90/1.06      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.90/1.06  thf('59', plain,
% 0.90/1.06      (![X0 : $i]:
% 0.90/1.06         ((v2_struct_0 @ sk_A)
% 0.90/1.06          | (v1_xboole_0 @ sk_B_1)
% 0.90/1.06          | ~ (v1_xboole_0 @ X0)
% 0.90/1.06          | ((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ X0)) = (sk_B_1)))),
% 0.90/1.06      inference('sup-', [status(thm)], ['57', '58'])).
% 0.90/1.06  thf('60', plain,
% 0.90/1.06      (((sk_B_1)
% 0.90/1.06         != (k2_yellow19 @ sk_A @ 
% 0.90/1.06             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf('61', plain,
% 0.90/1.06      ((v2_waybel_0 @ sk_B_1 @ 
% 0.90/1.06        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.90/1.06      inference('demod', [status(thm)], ['8', '9'])).
% 0.90/1.06  thf(t14_yellow19, axiom,
% 0.90/1.06    (![A:$i]:
% 0.90/1.06     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.90/1.06       ( ![B:$i]:
% 0.90/1.06         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.90/1.06             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.90/1.06             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.90/1.06             ( m1_subset_1 @
% 0.90/1.06               B @ 
% 0.90/1.06               ( k1_zfmisc_1 @
% 0.90/1.06                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.90/1.06           ( ( k7_subset_1 @
% 0.90/1.06               ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) @ B @ 
% 0.90/1.06               ( k1_tarski @ k1_xboole_0 ) ) =
% 0.90/1.06             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.90/1.06  thf('62', plain,
% 0.90/1.06      (![X29 : $i, X30 : $i]:
% 0.90/1.06         ((v1_xboole_0 @ X29)
% 0.90/1.06          | ~ (v2_waybel_0 @ X29 @ (k3_yellow_1 @ (k2_struct_0 @ X30)))
% 0.90/1.06          | ~ (v13_waybel_0 @ X29 @ (k3_yellow_1 @ (k2_struct_0 @ X30)))
% 0.90/1.06          | ~ (m1_subset_1 @ X29 @ 
% 0.90/1.06               (k1_zfmisc_1 @ 
% 0.90/1.06                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X30)))))
% 0.90/1.06          | ((k7_subset_1 @ 
% 0.90/1.06              (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X30))) @ X29 @ 
% 0.90/1.06              (k1_tarski @ k1_xboole_0))
% 0.90/1.06              = (k2_yellow19 @ X30 @ 
% 0.90/1.06                 (k3_yellow19 @ X30 @ (k2_struct_0 @ X30) @ X29)))
% 0.90/1.06          | ~ (l1_struct_0 @ X30)
% 0.90/1.06          | (v2_struct_0 @ X30))),
% 0.90/1.06      inference('cnf', [status(esa)], [t14_yellow19])).
% 0.90/1.06  thf('63', plain,
% 0.90/1.06      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.90/1.06      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.90/1.06  thf('64', plain,
% 0.90/1.06      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.90/1.06      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.90/1.06  thf('65', plain,
% 0.90/1.06      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.90/1.06      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.90/1.06  thf('66', plain,
% 0.90/1.06      (![X28 : $i]:
% 0.90/1.06         ((u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X28)))
% 0.90/1.06           = (k9_setfam_1 @ X28))),
% 0.90/1.06      inference('demod', [status(thm)], ['16', '17'])).
% 0.90/1.06  thf('67', plain, (![X24 : $i]: ((k9_setfam_1 @ X24) = (k1_zfmisc_1 @ X24))),
% 0.90/1.06      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.90/1.06  thf('68', plain,
% 0.90/1.06      (![X27 : $i]: ((k3_yellow_1 @ X27) = (k3_lattice3 @ (k1_lattice3 @ X27)))),
% 0.90/1.06      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.90/1.06  thf('69', plain,
% 0.90/1.06      (![X28 : $i]:
% 0.90/1.06         ((u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X28)))
% 0.90/1.06           = (k9_setfam_1 @ X28))),
% 0.90/1.06      inference('demod', [status(thm)], ['16', '17'])).
% 0.90/1.06  thf('70', plain,
% 0.90/1.06      (![X29 : $i, X30 : $i]:
% 0.90/1.06         ((v1_xboole_0 @ X29)
% 0.90/1.06          | ~ (v2_waybel_0 @ X29 @ 
% 0.90/1.06               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X30))))
% 0.90/1.06          | ~ (v13_waybel_0 @ X29 @ 
% 0.90/1.06               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X30))))
% 0.90/1.06          | ~ (m1_subset_1 @ X29 @ 
% 0.90/1.06               (k9_setfam_1 @ (k9_setfam_1 @ (k2_struct_0 @ X30))))
% 0.90/1.06          | ((k7_subset_1 @ (k9_setfam_1 @ (k2_struct_0 @ X30)) @ X29 @ 
% 0.90/1.06              (k1_tarski @ k1_xboole_0))
% 0.90/1.06              = (k2_yellow19 @ X30 @ 
% 0.90/1.06                 (k3_yellow19 @ X30 @ (k2_struct_0 @ X30) @ X29)))
% 0.90/1.06          | ~ (l1_struct_0 @ X30)
% 0.90/1.06          | (v2_struct_0 @ X30))),
% 0.90/1.06      inference('demod', [status(thm)],
% 0.90/1.06                ['62', '63', '64', '65', '66', '67', '68', '69'])).
% 0.90/1.06  thf('71', plain,
% 0.90/1.06      (((v2_struct_0 @ sk_A)
% 0.90/1.06        | ~ (l1_struct_0 @ sk_A)
% 0.90/1.06        | ((k7_subset_1 @ (k9_setfam_1 @ (k2_struct_0 @ sk_A)) @ sk_B_1 @ 
% 0.90/1.06            (k1_tarski @ k1_xboole_0))
% 0.90/1.06            = (k2_yellow19 @ sk_A @ 
% 0.90/1.06               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.90/1.06        | ~ (m1_subset_1 @ sk_B_1 @ 
% 0.90/1.06             (k9_setfam_1 @ (k9_setfam_1 @ (k2_struct_0 @ sk_A))))
% 0.90/1.06        | ~ (v13_waybel_0 @ sk_B_1 @ 
% 0.90/1.06             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.90/1.06        | (v1_xboole_0 @ sk_B_1))),
% 0.90/1.06      inference('sup-', [status(thm)], ['61', '70'])).
% 0.90/1.06  thf('72', plain, ((l1_struct_0 @ sk_A)),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf('73', plain,
% 0.90/1.06      ((m1_subset_1 @ sk_B_1 @ 
% 0.90/1.06        (k9_setfam_1 @ (k9_setfam_1 @ (k2_struct_0 @ sk_A))))),
% 0.90/1.06      inference('demod', [status(thm)], ['27', '28', '29', '30'])).
% 0.90/1.06  thf(redefinition_k7_subset_1, axiom,
% 0.90/1.06    (![A:$i,B:$i,C:$i]:
% 0.90/1.06     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.90/1.06       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.90/1.06  thf('74', plain,
% 0.90/1.06      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.90/1.06         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 0.90/1.06          | ((k7_subset_1 @ X22 @ X21 @ X23) = (k4_xboole_0 @ X21 @ X23)))),
% 0.90/1.06      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.90/1.06  thf('75', plain, (![X24 : $i]: ((k9_setfam_1 @ X24) = (k1_zfmisc_1 @ X24))),
% 0.90/1.06      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.90/1.06  thf('76', plain,
% 0.90/1.06      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.90/1.06         (~ (m1_subset_1 @ X21 @ (k9_setfam_1 @ X22))
% 0.90/1.06          | ((k7_subset_1 @ X22 @ X21 @ X23) = (k4_xboole_0 @ X21 @ X23)))),
% 0.90/1.06      inference('demod', [status(thm)], ['74', '75'])).
% 0.90/1.06  thf('77', plain,
% 0.90/1.06      (![X0 : $i]:
% 0.90/1.06         ((k7_subset_1 @ (k9_setfam_1 @ (k2_struct_0 @ sk_A)) @ sk_B_1 @ X0)
% 0.90/1.06           = (k4_xboole_0 @ sk_B_1 @ X0))),
% 0.90/1.06      inference('sup-', [status(thm)], ['73', '76'])).
% 0.90/1.06  thf('78', plain,
% 0.90/1.06      ((m1_subset_1 @ sk_B_1 @ 
% 0.90/1.06        (k9_setfam_1 @ (k9_setfam_1 @ (k2_struct_0 @ sk_A))))),
% 0.90/1.06      inference('demod', [status(thm)], ['27', '28', '29', '30'])).
% 0.90/1.06  thf('79', plain,
% 0.90/1.06      ((v13_waybel_0 @ sk_B_1 @ 
% 0.90/1.06        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.90/1.06      inference('demod', [status(thm)], ['36', '37'])).
% 0.90/1.06  thf('80', plain,
% 0.90/1.06      (((v2_struct_0 @ sk_A)
% 0.90/1.06        | ((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 0.90/1.06            = (k2_yellow19 @ sk_A @ 
% 0.90/1.06               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.90/1.06        | (v1_xboole_0 @ sk_B_1))),
% 0.90/1.06      inference('demod', [status(thm)], ['71', '72', '77', '78', '79'])).
% 0.90/1.06  thf('81', plain, (~ (v2_struct_0 @ sk_A)),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf('82', plain,
% 0.90/1.06      (((v1_xboole_0 @ sk_B_1)
% 0.90/1.06        | ((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 0.90/1.06            = (k2_yellow19 @ sk_A @ 
% 0.90/1.06               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))),
% 0.90/1.06      inference('clc', [status(thm)], ['80', '81'])).
% 0.90/1.06  thf('83', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf('84', plain,
% 0.90/1.06      (((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0))
% 0.90/1.06         = (k2_yellow19 @ sk_A @ 
% 0.90/1.06            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.90/1.06      inference('clc', [status(thm)], ['82', '83'])).
% 0.90/1.06  thf('85', plain,
% 0.90/1.06      (((sk_B_1) != (k4_xboole_0 @ sk_B_1 @ (k1_tarski @ k1_xboole_0)))),
% 0.90/1.06      inference('demod', [status(thm)], ['60', '84'])).
% 0.90/1.06  thf('86', plain,
% 0.90/1.06      ((((sk_B_1) != (sk_B_1))
% 0.90/1.06        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.90/1.06        | (v1_xboole_0 @ sk_B_1)
% 0.90/1.06        | (v2_struct_0 @ sk_A))),
% 0.90/1.06      inference('sup-', [status(thm)], ['59', '85'])).
% 0.90/1.06  thf(d1_xboole_0, axiom,
% 0.90/1.06    (![A:$i]:
% 0.90/1.06     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.90/1.06  thf('87', plain,
% 0.90/1.06      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.90/1.06      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.90/1.06  thf(t4_boole, axiom,
% 0.90/1.06    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.90/1.06  thf('88', plain,
% 0.90/1.06      (![X13 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X13) = (k1_xboole_0))),
% 0.90/1.06      inference('cnf', [status(esa)], [t4_boole])).
% 0.90/1.06  thf(d5_xboole_0, axiom,
% 0.90/1.06    (![A:$i,B:$i,C:$i]:
% 0.90/1.06     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.90/1.06       ( ![D:$i]:
% 0.90/1.06         ( ( r2_hidden @ D @ C ) <=>
% 0.90/1.06           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.90/1.06  thf('89', plain,
% 0.90/1.06      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.90/1.06         (~ (r2_hidden @ X7 @ X6)
% 0.90/1.06          | ~ (r2_hidden @ X7 @ X5)
% 0.90/1.06          | ((X6) != (k4_xboole_0 @ X4 @ X5)))),
% 0.90/1.06      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.90/1.06  thf('90', plain,
% 0.90/1.06      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.90/1.06         (~ (r2_hidden @ X7 @ X5)
% 0.90/1.06          | ~ (r2_hidden @ X7 @ (k4_xboole_0 @ X4 @ X5)))),
% 0.90/1.06      inference('simplify', [status(thm)], ['89'])).
% 0.90/1.06  thf('91', plain,
% 0.90/1.06      (![X0 : $i, X1 : $i]:
% 0.90/1.06         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.90/1.06      inference('sup-', [status(thm)], ['88', '90'])).
% 0.90/1.06  thf('92', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.90/1.06      inference('condensation', [status(thm)], ['91'])).
% 0.90/1.06  thf('93', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.90/1.06      inference('sup-', [status(thm)], ['87', '92'])).
% 0.90/1.06  thf('94', plain,
% 0.90/1.06      ((((sk_B_1) != (sk_B_1)) | (v1_xboole_0 @ sk_B_1) | (v2_struct_0 @ sk_A))),
% 0.90/1.06      inference('demod', [status(thm)], ['86', '93'])).
% 0.90/1.06  thf('95', plain, (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ sk_B_1))),
% 0.90/1.06      inference('simplify', [status(thm)], ['94'])).
% 0.90/1.06  thf('96', plain, (~ (v2_struct_0 @ sk_A)),
% 0.90/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.06  thf('97', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.90/1.06      inference('clc', [status(thm)], ['95', '96'])).
% 0.90/1.06  thf('98', plain, ($false), inference('demod', [status(thm)], ['0', '97'])).
% 0.90/1.06  
% 0.90/1.06  % SZS output end Refutation
% 0.90/1.06  
% 0.90/1.07  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
