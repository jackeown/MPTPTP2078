%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6vWU0Mzq5n

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:40 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 251 expanded)
%              Number of leaves         :   41 ( 101 expanded)
%              Depth                    :   19
%              Number of atoms          : 1084 (2922 expanded)
%              Number of equality atoms :   58 ( 154 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(k3_lattice3_type,type,(
    k3_lattice3: $i > $i )).

thf(k1_lattice3_type,type,(
    k1_lattice3: $i > $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_yellow19_type,type,(
    k2_yellow19: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_yellow19_type,type,(
    k3_yellow19: $i > $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    ~ ( v2_struct_0 @ sk_A ) ),
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
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t17_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X25 ) @ ( k1_tarski @ X26 ) )
      | ( X25 = X26 ) ) ),
    inference(cnf,[status(esa)],[t17_zfmisc_1])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('3',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X23 ) @ X24 )
      | ~ ( r2_hidden @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('7',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('8',plain,(
    v2_waybel_0 @ sk_B_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ) )).

thf('9',plain,(
    ! [X33: $i] :
      ( ( k3_yellow_1 @ X33 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X33 ) ) ) ),
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
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( v1_xboole_0 @ X37 )
      | ~ ( v1_subset_1 @ X37 @ ( u1_struct_0 @ ( k3_yellow_1 @ X38 ) ) )
      | ~ ( v2_waybel_0 @ X37 @ ( k3_yellow_1 @ X38 ) )
      | ~ ( v13_waybel_0 @ X37 @ ( k3_yellow_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X38 ) ) ) )
      | ~ ( r2_hidden @ X39 @ X37 )
      | ~ ( v1_xboole_0 @ X39 )
      | ( v1_xboole_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t2_yellow19])).

thf('15',plain,(
    ! [X33: $i] :
      ( ( k3_yellow_1 @ X33 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf(t4_waybel_7,axiom,(
    ! [A: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ A ) )
      = ( k9_setfam_1 @ A ) ) )).

thf('16',plain,(
    ! [X34: $i] :
      ( ( u1_struct_0 @ ( k3_yellow_1 @ X34 ) )
      = ( k9_setfam_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t4_waybel_7])).

thf('17',plain,(
    ! [X33: $i] :
      ( ( k3_yellow_1 @ X33 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('18',plain,(
    ! [X34: $i] :
      ( ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X34 ) ) )
      = ( k9_setfam_1 @ X34 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X33: $i] :
      ( ( k3_yellow_1 @ X33 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('20',plain,(
    ! [X33: $i] :
      ( ( k3_yellow_1 @ X33 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('21',plain,(
    ! [X33: $i] :
      ( ( k3_yellow_1 @ X33 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('22',plain,(
    ! [X34: $i] :
      ( ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X34 ) ) )
      = ( k9_setfam_1 @ X34 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('23',plain,(
    ! [X30: $i] :
      ( ( k9_setfam_1 @ X30 )
      = ( k1_zfmisc_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('24',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( v1_xboole_0 @ X37 )
      | ~ ( v1_subset_1 @ X37 @ ( k9_setfam_1 @ X38 ) )
      | ~ ( v2_waybel_0 @ X37 @ ( k3_lattice3 @ ( k1_lattice3 @ X38 ) ) )
      | ~ ( v13_waybel_0 @ X37 @ ( k3_lattice3 @ ( k1_lattice3 @ X38 ) ) )
      | ~ ( m1_subset_1 @ X37 @ ( k9_setfam_1 @ ( k9_setfam_1 @ X38 ) ) )
      | ~ ( r2_hidden @ X39 @ X37 )
      | ~ ( v1_xboole_0 @ X39 )
      | ( v1_xboole_0 @ X38 ) ) ),
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
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('27',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X33: $i] :
      ( ( k3_yellow_1 @ X33 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('29',plain,(
    ! [X30: $i] :
      ( ( k9_setfam_1 @ X30 )
      = ( k1_zfmisc_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('30',plain,(
    m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ! [X34: $i] :
      ( ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X34 ) ) )
      = ( k9_setfam_1 @ X34 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('32',plain,(
    m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['26','32'])).

thf('34',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('37',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X33: $i] :
      ( ( k3_yellow_1 @ X33 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('39',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['36','39'])).

thf('41',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('44',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X33: $i] :
      ( ( k3_yellow_1 @ X33 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('46',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X34: $i] :
      ( ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X34 ) ) )
      = ( k9_setfam_1 @ X34 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('48',plain,(
    v1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( v1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['43','48'])).

thf('50',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['25','35','42','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ ( sk_C @ sk_B_1 @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['5','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('56',plain,(
    ! [X32: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('61',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('62',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ sk_B_1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['59','65'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('67',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k4_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ X0 ) )
        = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    sk_B_1
 != ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
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

thf('71',plain,(
    ! [X35: $i,X36: $i] :
      ( ( v1_xboole_0 @ X35 )
      | ~ ( v2_waybel_0 @ X35 @ ( k3_yellow_1 @ ( k2_struct_0 @ X36 ) ) )
      | ~ ( v13_waybel_0 @ X35 @ ( k3_yellow_1 @ ( k2_struct_0 @ X36 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X36 ) ) ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ X36 ) ) ) @ X35 @ ( k1_tarski @ k1_xboole_0 ) )
        = ( k2_yellow19 @ X36 @ ( k3_yellow19 @ X36 @ ( k2_struct_0 @ X36 ) @ X35 ) ) )
      | ~ ( l1_struct_0 @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow19])).

thf('72',plain,(
    ! [X33: $i] :
      ( ( k3_yellow_1 @ X33 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('73',plain,(
    ! [X33: $i] :
      ( ( k3_yellow_1 @ X33 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('74',plain,(
    ! [X33: $i] :
      ( ( k3_yellow_1 @ X33 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('75',plain,(
    ! [X34: $i] :
      ( ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X34 ) ) )
      = ( k9_setfam_1 @ X34 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('76',plain,(
    ! [X30: $i] :
      ( ( k9_setfam_1 @ X30 )
      = ( k1_zfmisc_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('77',plain,(
    ! [X33: $i] :
      ( ( k3_yellow_1 @ X33 )
      = ( k3_lattice3 @ ( k1_lattice3 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[d2_yellow_1])).

thf('78',plain,(
    ! [X34: $i] :
      ( ( u1_struct_0 @ ( k3_lattice3 @ ( k1_lattice3 @ X34 ) ) )
      = ( k9_setfam_1 @ X34 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('79',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('80',plain,(
    ! [X35: $i,X36: $i] :
      ( ( v1_xboole_0 @ X35 )
      | ~ ( v2_waybel_0 @ X35 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X36 ) ) ) )
      | ~ ( v13_waybel_0 @ X35 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ X36 ) ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ X36 ) ) ) )
      | ( ( k7_subset_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ X36 ) ) @ X35 @ ( k1_tarski @ o_0_0_xboole_0 ) )
        = ( k2_yellow19 @ X36 @ ( k3_yellow19 @ X36 @ ( k2_struct_0 @ X36 ) @ X35 ) ) )
      | ~ ( l1_struct_0 @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(demod,[status(thm)],['71','72','73','74','75','76','77','78','79'])).

thf('81',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k7_subset_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ sk_A ) ) @ sk_B_1 @ ( k1_tarski @ o_0_0_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['70','80'])).

thf('82',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('84',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) )
      | ( ( k7_subset_1 @ X28 @ X27 @ X29 )
        = ( k4_xboole_0 @ X27 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('85',plain,(
    ! [X30: $i] :
      ( ( k9_setfam_1 @ X30 )
      = ( k1_zfmisc_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('86',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k9_setfam_1 @ X28 ) )
      | ( ( k7_subset_1 @ X28 @ X27 @ X29 )
        = ( k4_xboole_0 @ X27 @ X29 ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ sk_A ) ) @ sk_B_1 @ X0 )
      = ( k4_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( k9_setfam_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('89',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_lattice3 @ ( k1_lattice3 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ o_0_0_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['81','82','87','88','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ o_0_0_xboole_0 ) )
      = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ o_0_0_xboole_0 ) )
    = ( k2_yellow19 @ sk_A @ ( k3_yellow19 @ sk_A @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,(
    sk_B_1
 != ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['69','94'])).

thf('96',plain,
    ( ( sk_B_1 != sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','95'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('97',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('98',plain,
    ( ( sk_B_1 != sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,(
    $false ),
    inference(demod,[status(thm)],['0','101'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6vWU0Mzq5n
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:02:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.67  % Solved by: fo/fo7.sh
% 0.46/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.67  % done 499 iterations in 0.211s
% 0.46/0.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.67  % SZS output start Refutation
% 0.46/0.67  thf(k9_setfam_1_type, type, k9_setfam_1: $i > $i).
% 0.46/0.67  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.46/0.67  thf(k3_lattice3_type, type, k3_lattice3: $i > $i).
% 0.46/0.67  thf(k1_lattice3_type, type, k1_lattice3: $i > $i).
% 0.46/0.67  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.46/0.67  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.46/0.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.67  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.46/0.67  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.46/0.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.67  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.46/0.67  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.46/0.67  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.46/0.67  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.67  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.67  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.46/0.67  thf(k2_yellow19_type, type, k2_yellow19: $i > $i > $i).
% 0.46/0.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.67  thf(k3_yellow19_type, type, k3_yellow19: $i > $i > $i > $i).
% 0.46/0.67  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.46/0.67  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.67  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.46/0.67  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.46/0.67  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.67  thf(t15_yellow19, conjecture,
% 0.46/0.67    (![A:$i]:
% 0.46/0.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.46/0.67       ( ![B:$i]:
% 0.46/0.67         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.46/0.67             ( v1_subset_1 @
% 0.46/0.67               B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.46/0.67             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.46/0.67             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.46/0.67             ( m1_subset_1 @
% 0.46/0.67               B @ 
% 0.46/0.67               ( k1_zfmisc_1 @
% 0.46/0.67                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.46/0.67           ( ( B ) =
% 0.46/0.67             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.46/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.67    (~( ![A:$i]:
% 0.46/0.67        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.46/0.67          ( ![B:$i]:
% 0.46/0.67            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.46/0.67                ( v1_subset_1 @
% 0.46/0.67                  B @ ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) & 
% 0.46/0.67                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.46/0.67                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.46/0.67                ( m1_subset_1 @
% 0.46/0.67                  B @ 
% 0.46/0.67                  ( k1_zfmisc_1 @
% 0.46/0.67                    ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.46/0.67              ( ( B ) =
% 0.46/0.67                ( k2_yellow19 @
% 0.46/0.67                  A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.46/0.67    inference('cnf.neg', [status(esa)], [t15_yellow19])).
% 0.46/0.67  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf(t3_xboole_0, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.46/0.67            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.46/0.67       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.46/0.67            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.46/0.67  thf('1', plain,
% 0.46/0.67      (![X5 : $i, X6 : $i]:
% 0.46/0.67         ((r1_xboole_0 @ X5 @ X6) | (r2_hidden @ (sk_C @ X6 @ X5) @ X5))),
% 0.46/0.67      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.46/0.67  thf(t17_zfmisc_1, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( ( A ) != ( B ) ) =>
% 0.46/0.67       ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.46/0.67  thf('2', plain,
% 0.46/0.67      (![X25 : $i, X26 : $i]:
% 0.46/0.67         ((r1_xboole_0 @ (k1_tarski @ X25) @ (k1_tarski @ X26))
% 0.46/0.67          | ((X25) = (X26)))),
% 0.46/0.67      inference('cnf', [status(esa)], [t17_zfmisc_1])).
% 0.46/0.67  thf(l24_zfmisc_1, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.46/0.67  thf('3', plain,
% 0.46/0.67      (![X23 : $i, X24 : $i]:
% 0.46/0.67         (~ (r1_xboole_0 @ (k1_tarski @ X23) @ X24) | ~ (r2_hidden @ X23 @ X24))),
% 0.46/0.67      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.46/0.67  thf('4', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['2', '3'])).
% 0.46/0.67  thf('5', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.46/0.67          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['1', '4'])).
% 0.46/0.67  thf('6', plain,
% 0.46/0.67      (![X5 : $i, X6 : $i]:
% 0.46/0.67         ((r1_xboole_0 @ X5 @ X6) | (r2_hidden @ (sk_C @ X6 @ X5) @ X6))),
% 0.46/0.67      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.46/0.67  thf(d3_struct_0, axiom,
% 0.46/0.67    (![A:$i]:
% 0.46/0.67     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.46/0.67  thf('7', plain,
% 0.46/0.67      (![X31 : $i]:
% 0.46/0.67         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.46/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.67  thf('8', plain,
% 0.46/0.67      ((v2_waybel_0 @ sk_B_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf(d2_yellow_1, axiom,
% 0.46/0.67    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k3_lattice3 @ ( k1_lattice3 @ A ) ) ))).
% 0.46/0.67  thf('9', plain,
% 0.46/0.67      (![X33 : $i]: ((k3_yellow_1 @ X33) = (k3_lattice3 @ (k1_lattice3 @ X33)))),
% 0.46/0.67      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.46/0.67  thf('10', plain,
% 0.46/0.67      ((v2_waybel_0 @ sk_B_1 @ 
% 0.46/0.67        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.46/0.67      inference('demod', [status(thm)], ['8', '9'])).
% 0.46/0.67  thf('11', plain,
% 0.46/0.67      (((v2_waybel_0 @ sk_B_1 @ 
% 0.46/0.67         (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.46/0.67        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.67      inference('sup+', [status(thm)], ['7', '10'])).
% 0.46/0.67  thf('12', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('13', plain,
% 0.46/0.67      ((v2_waybel_0 @ sk_B_1 @ 
% 0.46/0.67        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.67      inference('demod', [status(thm)], ['11', '12'])).
% 0.46/0.67  thf(t2_yellow19, axiom,
% 0.46/0.67    (![A:$i]:
% 0.46/0.67     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.46/0.67       ( ![B:$i]:
% 0.46/0.67         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.46/0.67             ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) & 
% 0.46/0.67             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.46/0.67             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.46/0.67             ( m1_subset_1 @
% 0.46/0.67               B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) ) =>
% 0.46/0.67           ( ![C:$i]: ( ~( ( r2_hidden @ C @ B ) & ( v1_xboole_0 @ C ) ) ) ) ) ) ))).
% 0.46/0.67  thf('14', plain,
% 0.46/0.67      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.46/0.67         ((v1_xboole_0 @ X37)
% 0.46/0.67          | ~ (v1_subset_1 @ X37 @ (u1_struct_0 @ (k3_yellow_1 @ X38)))
% 0.46/0.67          | ~ (v2_waybel_0 @ X37 @ (k3_yellow_1 @ X38))
% 0.46/0.67          | ~ (v13_waybel_0 @ X37 @ (k3_yellow_1 @ X38))
% 0.46/0.67          | ~ (m1_subset_1 @ X37 @ 
% 0.46/0.67               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X38))))
% 0.46/0.67          | ~ (r2_hidden @ X39 @ X37)
% 0.46/0.67          | ~ (v1_xboole_0 @ X39)
% 0.46/0.67          | (v1_xboole_0 @ X38))),
% 0.46/0.67      inference('cnf', [status(esa)], [t2_yellow19])).
% 0.46/0.67  thf('15', plain,
% 0.46/0.67      (![X33 : $i]: ((k3_yellow_1 @ X33) = (k3_lattice3 @ (k1_lattice3 @ X33)))),
% 0.46/0.67      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.46/0.67  thf(t4_waybel_7, axiom,
% 0.46/0.67    (![A:$i]: ( ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) = ( k9_setfam_1 @ A ) ))).
% 0.46/0.67  thf('16', plain,
% 0.46/0.67      (![X34 : $i]: ((u1_struct_0 @ (k3_yellow_1 @ X34)) = (k9_setfam_1 @ X34))),
% 0.46/0.67      inference('cnf', [status(esa)], [t4_waybel_7])).
% 0.46/0.67  thf('17', plain,
% 0.46/0.67      (![X33 : $i]: ((k3_yellow_1 @ X33) = (k3_lattice3 @ (k1_lattice3 @ X33)))),
% 0.46/0.67      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.46/0.67  thf('18', plain,
% 0.46/0.67      (![X34 : $i]:
% 0.46/0.67         ((u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X34)))
% 0.46/0.67           = (k9_setfam_1 @ X34))),
% 0.46/0.67      inference('demod', [status(thm)], ['16', '17'])).
% 0.46/0.67  thf('19', plain,
% 0.46/0.67      (![X33 : $i]: ((k3_yellow_1 @ X33) = (k3_lattice3 @ (k1_lattice3 @ X33)))),
% 0.46/0.67      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.46/0.67  thf('20', plain,
% 0.46/0.67      (![X33 : $i]: ((k3_yellow_1 @ X33) = (k3_lattice3 @ (k1_lattice3 @ X33)))),
% 0.46/0.67      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.46/0.67  thf('21', plain,
% 0.46/0.67      (![X33 : $i]: ((k3_yellow_1 @ X33) = (k3_lattice3 @ (k1_lattice3 @ X33)))),
% 0.46/0.67      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.46/0.67  thf('22', plain,
% 0.46/0.67      (![X34 : $i]:
% 0.46/0.67         ((u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X34)))
% 0.46/0.67           = (k9_setfam_1 @ X34))),
% 0.46/0.67      inference('demod', [status(thm)], ['16', '17'])).
% 0.46/0.67  thf(redefinition_k9_setfam_1, axiom,
% 0.46/0.67    (![A:$i]: ( ( k9_setfam_1 @ A ) = ( k1_zfmisc_1 @ A ) ))).
% 0.46/0.67  thf('23', plain, (![X30 : $i]: ((k9_setfam_1 @ X30) = (k1_zfmisc_1 @ X30))),
% 0.46/0.67      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.46/0.67  thf('24', plain,
% 0.46/0.67      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.46/0.67         ((v1_xboole_0 @ X37)
% 0.46/0.67          | ~ (v1_subset_1 @ X37 @ (k9_setfam_1 @ X38))
% 0.46/0.67          | ~ (v2_waybel_0 @ X37 @ (k3_lattice3 @ (k1_lattice3 @ X38)))
% 0.46/0.67          | ~ (v13_waybel_0 @ X37 @ (k3_lattice3 @ (k1_lattice3 @ X38)))
% 0.46/0.67          | ~ (m1_subset_1 @ X37 @ (k9_setfam_1 @ (k9_setfam_1 @ X38)))
% 0.46/0.67          | ~ (r2_hidden @ X39 @ X37)
% 0.46/0.67          | ~ (v1_xboole_0 @ X39)
% 0.46/0.67          | (v1_xboole_0 @ X38))),
% 0.46/0.67      inference('demod', [status(thm)],
% 0.46/0.67                ['14', '15', '18', '19', '20', '21', '22', '23'])).
% 0.46/0.67  thf('25', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.67          | ~ (v1_xboole_0 @ X0)
% 0.46/0.67          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.46/0.67          | ~ (m1_subset_1 @ sk_B_1 @ 
% 0.46/0.67               (k9_setfam_1 @ (k9_setfam_1 @ (u1_struct_0 @ sk_A))))
% 0.46/0.67          | ~ (v13_waybel_0 @ sk_B_1 @ 
% 0.46/0.67               (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.46/0.67          | ~ (v1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.67          | (v1_xboole_0 @ sk_B_1))),
% 0.46/0.67      inference('sup-', [status(thm)], ['13', '24'])).
% 0.46/0.67  thf('26', plain,
% 0.46/0.67      (![X31 : $i]:
% 0.46/0.67         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.46/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.67  thf('27', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_B_1 @ 
% 0.46/0.67        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('28', plain,
% 0.46/0.67      (![X33 : $i]: ((k3_yellow_1 @ X33) = (k3_lattice3 @ (k1_lattice3 @ X33)))),
% 0.46/0.67      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.46/0.67  thf('29', plain, (![X30 : $i]: ((k9_setfam_1 @ X30) = (k1_zfmisc_1 @ X30))),
% 0.46/0.67      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.46/0.67  thf('30', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_B_1 @ 
% 0.46/0.67        (k9_setfam_1 @ 
% 0.46/0.67         (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))))),
% 0.46/0.67      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.46/0.67  thf('31', plain,
% 0.46/0.67      (![X34 : $i]:
% 0.46/0.67         ((u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X34)))
% 0.46/0.67           = (k9_setfam_1 @ X34))),
% 0.46/0.67      inference('demod', [status(thm)], ['16', '17'])).
% 0.46/0.67  thf('32', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_B_1 @ 
% 0.46/0.67        (k9_setfam_1 @ (k9_setfam_1 @ (k2_struct_0 @ sk_A))))),
% 0.46/0.67      inference('demod', [status(thm)], ['30', '31'])).
% 0.46/0.67  thf('33', plain,
% 0.46/0.67      (((m1_subset_1 @ sk_B_1 @ 
% 0.46/0.67         (k9_setfam_1 @ (k9_setfam_1 @ (u1_struct_0 @ sk_A))))
% 0.46/0.67        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.67      inference('sup+', [status(thm)], ['26', '32'])).
% 0.46/0.67  thf('34', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('35', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_B_1 @ 
% 0.46/0.67        (k9_setfam_1 @ (k9_setfam_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.67      inference('demod', [status(thm)], ['33', '34'])).
% 0.46/0.67  thf('36', plain,
% 0.46/0.67      (![X31 : $i]:
% 0.46/0.67         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.46/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.67  thf('37', plain,
% 0.46/0.67      ((v13_waybel_0 @ sk_B_1 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A)))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('38', plain,
% 0.46/0.67      (![X33 : $i]: ((k3_yellow_1 @ X33) = (k3_lattice3 @ (k1_lattice3 @ X33)))),
% 0.46/0.67      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.46/0.67  thf('39', plain,
% 0.46/0.67      ((v13_waybel_0 @ sk_B_1 @ 
% 0.46/0.67        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.46/0.67      inference('demod', [status(thm)], ['37', '38'])).
% 0.46/0.67  thf('40', plain,
% 0.46/0.67      (((v13_waybel_0 @ sk_B_1 @ 
% 0.46/0.67         (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))
% 0.46/0.67        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.67      inference('sup+', [status(thm)], ['36', '39'])).
% 0.46/0.67  thf('41', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('42', plain,
% 0.46/0.67      ((v13_waybel_0 @ sk_B_1 @ 
% 0.46/0.67        (k3_lattice3 @ (k1_lattice3 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.67      inference('demod', [status(thm)], ['40', '41'])).
% 0.46/0.67  thf('43', plain,
% 0.46/0.67      (![X31 : $i]:
% 0.46/0.67         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.46/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.67  thf('44', plain,
% 0.46/0.67      ((v1_subset_1 @ sk_B_1 @ 
% 0.46/0.67        (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ sk_A))))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('45', plain,
% 0.46/0.67      (![X33 : $i]: ((k3_yellow_1 @ X33) = (k3_lattice3 @ (k1_lattice3 @ X33)))),
% 0.46/0.67      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.46/0.67  thf('46', plain,
% 0.46/0.67      ((v1_subset_1 @ sk_B_1 @ 
% 0.46/0.67        (u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A)))))),
% 0.46/0.67      inference('demod', [status(thm)], ['44', '45'])).
% 0.46/0.67  thf('47', plain,
% 0.46/0.67      (![X34 : $i]:
% 0.46/0.67         ((u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X34)))
% 0.46/0.67           = (k9_setfam_1 @ X34))),
% 0.46/0.67      inference('demod', [status(thm)], ['16', '17'])).
% 0.46/0.67  thf('48', plain,
% 0.46/0.67      ((v1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ (k2_struct_0 @ sk_A)))),
% 0.46/0.67      inference('demod', [status(thm)], ['46', '47'])).
% 0.46/0.67  thf('49', plain,
% 0.46/0.67      (((v1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.67        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.67      inference('sup+', [status(thm)], ['43', '48'])).
% 0.46/0.67  thf('50', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('51', plain,
% 0.46/0.67      ((v1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.67      inference('demod', [status(thm)], ['49', '50'])).
% 0.46/0.67  thf('52', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.67          | ~ (v1_xboole_0 @ X0)
% 0.46/0.67          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.46/0.67          | (v1_xboole_0 @ sk_B_1))),
% 0.46/0.67      inference('demod', [status(thm)], ['25', '35', '42', '51'])).
% 0.46/0.67  thf('53', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         ((r1_xboole_0 @ X0 @ sk_B_1)
% 0.46/0.67          | (v1_xboole_0 @ sk_B_1)
% 0.46/0.67          | ~ (v1_xboole_0 @ (sk_C @ sk_B_1 @ X0))
% 0.46/0.67          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['6', '52'])).
% 0.46/0.67  thf('54', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (~ (v1_xboole_0 @ X0)
% 0.46/0.67          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B_1)
% 0.46/0.67          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.67          | (v1_xboole_0 @ sk_B_1)
% 0.46/0.67          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B_1))),
% 0.46/0.67      inference('sup-', [status(thm)], ['5', '53'])).
% 0.46/0.67  thf('55', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         ((v1_xboole_0 @ sk_B_1)
% 0.46/0.67          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.46/0.67          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B_1)
% 0.46/0.67          | ~ (v1_xboole_0 @ X0))),
% 0.46/0.67      inference('simplify', [status(thm)], ['54'])).
% 0.46/0.67  thf(fc2_struct_0, axiom,
% 0.46/0.67    (![A:$i]:
% 0.46/0.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.46/0.67       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.46/0.67  thf('56', plain,
% 0.46/0.67      (![X32 : $i]:
% 0.46/0.67         (~ (v1_xboole_0 @ (u1_struct_0 @ X32))
% 0.46/0.67          | ~ (l1_struct_0 @ X32)
% 0.46/0.67          | (v2_struct_0 @ X32))),
% 0.46/0.67      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.46/0.67  thf('57', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (~ (v1_xboole_0 @ X0)
% 0.46/0.67          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B_1)
% 0.46/0.67          | (v1_xboole_0 @ sk_B_1)
% 0.46/0.67          | (v2_struct_0 @ sk_A)
% 0.46/0.67          | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.67      inference('sup-', [status(thm)], ['55', '56'])).
% 0.46/0.67  thf('58', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('59', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (~ (v1_xboole_0 @ X0)
% 0.46/0.67          | (r1_xboole_0 @ (k1_tarski @ X0) @ sk_B_1)
% 0.46/0.67          | (v1_xboole_0 @ sk_B_1)
% 0.46/0.67          | (v2_struct_0 @ sk_A))),
% 0.46/0.67      inference('demod', [status(thm)], ['57', '58'])).
% 0.46/0.67  thf('60', plain,
% 0.46/0.67      (![X5 : $i, X6 : $i]:
% 0.46/0.67         ((r1_xboole_0 @ X5 @ X6) | (r2_hidden @ (sk_C @ X6 @ X5) @ X5))),
% 0.46/0.67      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.46/0.67  thf('61', plain,
% 0.46/0.67      (![X5 : $i, X6 : $i]:
% 0.46/0.67         ((r1_xboole_0 @ X5 @ X6) | (r2_hidden @ (sk_C @ X6 @ X5) @ X6))),
% 0.46/0.67      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.46/0.67  thf('62', plain,
% 0.46/0.67      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.46/0.67         (~ (r2_hidden @ X7 @ X5)
% 0.46/0.67          | ~ (r2_hidden @ X7 @ X8)
% 0.46/0.67          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.46/0.67      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.46/0.67  thf('63', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.67         ((r1_xboole_0 @ X1 @ X0)
% 0.46/0.67          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.46/0.67          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.46/0.67      inference('sup-', [status(thm)], ['61', '62'])).
% 0.46/0.67  thf('64', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         ((r1_xboole_0 @ X0 @ X1)
% 0.46/0.67          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.46/0.67          | (r1_xboole_0 @ X0 @ X1))),
% 0.46/0.67      inference('sup-', [status(thm)], ['60', '63'])).
% 0.46/0.67  thf('65', plain,
% 0.46/0.67      (![X0 : $i, X1 : $i]:
% 0.46/0.67         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.46/0.67      inference('simplify', [status(thm)], ['64'])).
% 0.46/0.67  thf('66', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         ((v2_struct_0 @ sk_A)
% 0.46/0.67          | (v1_xboole_0 @ sk_B_1)
% 0.46/0.67          | ~ (v1_xboole_0 @ X0)
% 0.46/0.67          | (r1_xboole_0 @ sk_B_1 @ (k1_tarski @ X0)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['59', '65'])).
% 0.46/0.67  thf(t83_xboole_1, axiom,
% 0.46/0.67    (![A:$i,B:$i]:
% 0.46/0.67     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.46/0.67  thf('67', plain,
% 0.46/0.67      (![X20 : $i, X21 : $i]:
% 0.46/0.67         (((k4_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_xboole_0 @ X20 @ X21))),
% 0.46/0.67      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.46/0.67  thf('68', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         (~ (v1_xboole_0 @ X0)
% 0.46/0.67          | (v1_xboole_0 @ sk_B_1)
% 0.46/0.67          | (v2_struct_0 @ sk_A)
% 0.46/0.67          | ((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ X0)) = (sk_B_1)))),
% 0.46/0.67      inference('sup-', [status(thm)], ['66', '67'])).
% 0.46/0.67  thf('69', plain,
% 0.46/0.67      (((sk_B_1)
% 0.46/0.67         != (k2_yellow19 @ sk_A @ 
% 0.46/0.67             (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('70', plain,
% 0.46/0.67      ((v2_waybel_0 @ sk_B_1 @ 
% 0.46/0.67        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.46/0.67      inference('demod', [status(thm)], ['8', '9'])).
% 0.46/0.67  thf(t14_yellow19, axiom,
% 0.46/0.67    (![A:$i]:
% 0.46/0.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.46/0.67       ( ![B:$i]:
% 0.46/0.67         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.46/0.67             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.46/0.67             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) & 
% 0.46/0.67             ( m1_subset_1 @
% 0.46/0.67               B @ 
% 0.46/0.67               ( k1_zfmisc_1 @
% 0.46/0.67                 ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) ) ) ) =>
% 0.46/0.67           ( ( k7_subset_1 @
% 0.46/0.67               ( u1_struct_0 @ ( k3_yellow_1 @ ( k2_struct_0 @ A ) ) ) @ B @ 
% 0.46/0.67               ( k1_tarski @ k1_xboole_0 ) ) =
% 0.46/0.67             ( k2_yellow19 @ A @ ( k3_yellow19 @ A @ ( k2_struct_0 @ A ) @ B ) ) ) ) ) ))).
% 0.46/0.67  thf('71', plain,
% 0.46/0.67      (![X35 : $i, X36 : $i]:
% 0.46/0.67         ((v1_xboole_0 @ X35)
% 0.46/0.67          | ~ (v2_waybel_0 @ X35 @ (k3_yellow_1 @ (k2_struct_0 @ X36)))
% 0.46/0.67          | ~ (v13_waybel_0 @ X35 @ (k3_yellow_1 @ (k2_struct_0 @ X36)))
% 0.46/0.67          | ~ (m1_subset_1 @ X35 @ 
% 0.46/0.67               (k1_zfmisc_1 @ 
% 0.46/0.67                (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X36)))))
% 0.46/0.67          | ((k7_subset_1 @ 
% 0.46/0.67              (u1_struct_0 @ (k3_yellow_1 @ (k2_struct_0 @ X36))) @ X35 @ 
% 0.46/0.67              (k1_tarski @ k1_xboole_0))
% 0.46/0.67              = (k2_yellow19 @ X36 @ 
% 0.46/0.67                 (k3_yellow19 @ X36 @ (k2_struct_0 @ X36) @ X35)))
% 0.46/0.67          | ~ (l1_struct_0 @ X36)
% 0.46/0.67          | (v2_struct_0 @ X36))),
% 0.46/0.67      inference('cnf', [status(esa)], [t14_yellow19])).
% 0.46/0.67  thf('72', plain,
% 0.46/0.67      (![X33 : $i]: ((k3_yellow_1 @ X33) = (k3_lattice3 @ (k1_lattice3 @ X33)))),
% 0.46/0.67      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.46/0.67  thf('73', plain,
% 0.46/0.67      (![X33 : $i]: ((k3_yellow_1 @ X33) = (k3_lattice3 @ (k1_lattice3 @ X33)))),
% 0.46/0.67      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.46/0.67  thf('74', plain,
% 0.46/0.67      (![X33 : $i]: ((k3_yellow_1 @ X33) = (k3_lattice3 @ (k1_lattice3 @ X33)))),
% 0.46/0.67      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.46/0.67  thf('75', plain,
% 0.46/0.67      (![X34 : $i]:
% 0.46/0.67         ((u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X34)))
% 0.46/0.67           = (k9_setfam_1 @ X34))),
% 0.46/0.67      inference('demod', [status(thm)], ['16', '17'])).
% 0.46/0.67  thf('76', plain, (![X30 : $i]: ((k9_setfam_1 @ X30) = (k1_zfmisc_1 @ X30))),
% 0.46/0.67      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.46/0.67  thf('77', plain,
% 0.46/0.67      (![X33 : $i]: ((k3_yellow_1 @ X33) = (k3_lattice3 @ (k1_lattice3 @ X33)))),
% 0.46/0.67      inference('cnf', [status(esa)], [d2_yellow_1])).
% 0.46/0.67  thf('78', plain,
% 0.46/0.67      (![X34 : $i]:
% 0.46/0.67         ((u1_struct_0 @ (k3_lattice3 @ (k1_lattice3 @ X34)))
% 0.46/0.67           = (k9_setfam_1 @ X34))),
% 0.46/0.67      inference('demod', [status(thm)], ['16', '17'])).
% 0.46/0.67  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.46/0.67  thf('79', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.46/0.67      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.46/0.67  thf('80', plain,
% 0.46/0.67      (![X35 : $i, X36 : $i]:
% 0.46/0.67         ((v1_xboole_0 @ X35)
% 0.46/0.67          | ~ (v2_waybel_0 @ X35 @ 
% 0.46/0.67               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X36))))
% 0.46/0.67          | ~ (v13_waybel_0 @ X35 @ 
% 0.46/0.67               (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ X36))))
% 0.46/0.67          | ~ (m1_subset_1 @ X35 @ 
% 0.46/0.67               (k9_setfam_1 @ (k9_setfam_1 @ (k2_struct_0 @ X36))))
% 0.46/0.67          | ((k7_subset_1 @ (k9_setfam_1 @ (k2_struct_0 @ X36)) @ X35 @ 
% 0.46/0.67              (k1_tarski @ o_0_0_xboole_0))
% 0.46/0.67              = (k2_yellow19 @ X36 @ 
% 0.46/0.67                 (k3_yellow19 @ X36 @ (k2_struct_0 @ X36) @ X35)))
% 0.46/0.67          | ~ (l1_struct_0 @ X36)
% 0.46/0.67          | (v2_struct_0 @ X36))),
% 0.46/0.67      inference('demod', [status(thm)],
% 0.46/0.67                ['71', '72', '73', '74', '75', '76', '77', '78', '79'])).
% 0.46/0.67  thf('81', plain,
% 0.46/0.67      (((v2_struct_0 @ sk_A)
% 0.46/0.67        | ~ (l1_struct_0 @ sk_A)
% 0.46/0.67        | ((k7_subset_1 @ (k9_setfam_1 @ (k2_struct_0 @ sk_A)) @ sk_B_1 @ 
% 0.46/0.67            (k1_tarski @ o_0_0_xboole_0))
% 0.46/0.67            = (k2_yellow19 @ sk_A @ 
% 0.46/0.67               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.46/0.67        | ~ (m1_subset_1 @ sk_B_1 @ 
% 0.46/0.67             (k9_setfam_1 @ (k9_setfam_1 @ (k2_struct_0 @ sk_A))))
% 0.46/0.67        | ~ (v13_waybel_0 @ sk_B_1 @ 
% 0.46/0.67             (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))
% 0.46/0.67        | (v1_xboole_0 @ sk_B_1))),
% 0.46/0.67      inference('sup-', [status(thm)], ['70', '80'])).
% 0.46/0.67  thf('82', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('83', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_B_1 @ 
% 0.46/0.67        (k9_setfam_1 @ (k9_setfam_1 @ (k2_struct_0 @ sk_A))))),
% 0.46/0.67      inference('demod', [status(thm)], ['30', '31'])).
% 0.46/0.67  thf(redefinition_k7_subset_1, axiom,
% 0.46/0.67    (![A:$i,B:$i,C:$i]:
% 0.46/0.67     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.67       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.46/0.67  thf('84', plain,
% 0.46/0.67      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.46/0.67         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28))
% 0.46/0.67          | ((k7_subset_1 @ X28 @ X27 @ X29) = (k4_xboole_0 @ X27 @ X29)))),
% 0.46/0.67      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.46/0.67  thf('85', plain, (![X30 : $i]: ((k9_setfam_1 @ X30) = (k1_zfmisc_1 @ X30))),
% 0.46/0.67      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.46/0.67  thf('86', plain,
% 0.46/0.67      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.46/0.67         (~ (m1_subset_1 @ X27 @ (k9_setfam_1 @ X28))
% 0.46/0.67          | ((k7_subset_1 @ X28 @ X27 @ X29) = (k4_xboole_0 @ X27 @ X29)))),
% 0.46/0.67      inference('demod', [status(thm)], ['84', '85'])).
% 0.46/0.67  thf('87', plain,
% 0.46/0.67      (![X0 : $i]:
% 0.46/0.67         ((k7_subset_1 @ (k9_setfam_1 @ (k2_struct_0 @ sk_A)) @ sk_B_1 @ X0)
% 0.46/0.67           = (k4_xboole_0 @ sk_B_1 @ X0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['83', '86'])).
% 0.46/0.67  thf('88', plain,
% 0.46/0.67      ((m1_subset_1 @ sk_B_1 @ 
% 0.46/0.67        (k9_setfam_1 @ (k9_setfam_1 @ (k2_struct_0 @ sk_A))))),
% 0.46/0.67      inference('demod', [status(thm)], ['30', '31'])).
% 0.46/0.67  thf('89', plain,
% 0.46/0.67      ((v13_waybel_0 @ sk_B_1 @ 
% 0.46/0.67        (k3_lattice3 @ (k1_lattice3 @ (k2_struct_0 @ sk_A))))),
% 0.46/0.67      inference('demod', [status(thm)], ['37', '38'])).
% 0.46/0.67  thf('90', plain,
% 0.46/0.67      (((v2_struct_0 @ sk_A)
% 0.46/0.67        | ((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ o_0_0_xboole_0))
% 0.46/0.67            = (k2_yellow19 @ sk_A @ 
% 0.46/0.67               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))
% 0.46/0.67        | (v1_xboole_0 @ sk_B_1))),
% 0.46/0.67      inference('demod', [status(thm)], ['81', '82', '87', '88', '89'])).
% 0.46/0.67  thf('91', plain, (~ (v2_struct_0 @ sk_A)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('92', plain,
% 0.46/0.67      (((v1_xboole_0 @ sk_B_1)
% 0.46/0.67        | ((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ o_0_0_xboole_0))
% 0.46/0.67            = (k2_yellow19 @ sk_A @ 
% 0.46/0.67               (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1))))),
% 0.46/0.67      inference('clc', [status(thm)], ['90', '91'])).
% 0.46/0.67  thf('93', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('94', plain,
% 0.46/0.67      (((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ o_0_0_xboole_0))
% 0.46/0.67         = (k2_yellow19 @ sk_A @ 
% 0.46/0.67            (k3_yellow19 @ sk_A @ (k2_struct_0 @ sk_A) @ sk_B_1)))),
% 0.46/0.67      inference('clc', [status(thm)], ['92', '93'])).
% 0.46/0.67  thf('95', plain,
% 0.46/0.67      (((sk_B_1) != (k4_xboole_0 @ sk_B_1 @ (k1_tarski @ o_0_0_xboole_0)))),
% 0.46/0.67      inference('demod', [status(thm)], ['69', '94'])).
% 0.46/0.67  thf('96', plain,
% 0.46/0.67      ((((sk_B_1) != (sk_B_1))
% 0.46/0.67        | (v2_struct_0 @ sk_A)
% 0.46/0.67        | (v1_xboole_0 @ sk_B_1)
% 0.46/0.67        | ~ (v1_xboole_0 @ o_0_0_xboole_0))),
% 0.46/0.67      inference('sup-', [status(thm)], ['68', '95'])).
% 0.46/0.67  thf(dt_o_0_0_xboole_0, axiom, (v1_xboole_0 @ o_0_0_xboole_0)).
% 0.46/0.67  thf('97', plain, ((v1_xboole_0 @ o_0_0_xboole_0)),
% 0.46/0.67      inference('cnf', [status(esa)], [dt_o_0_0_xboole_0])).
% 0.46/0.67  thf('98', plain,
% 0.46/0.67      ((((sk_B_1) != (sk_B_1)) | (v2_struct_0 @ sk_A) | (v1_xboole_0 @ sk_B_1))),
% 0.46/0.67      inference('demod', [status(thm)], ['96', '97'])).
% 0.46/0.67  thf('99', plain, (((v1_xboole_0 @ sk_B_1) | (v2_struct_0 @ sk_A))),
% 0.46/0.67      inference('simplify', [status(thm)], ['98'])).
% 0.46/0.67  thf('100', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.46/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.67  thf('101', plain, ((v2_struct_0 @ sk_A)),
% 0.46/0.67      inference('clc', [status(thm)], ['99', '100'])).
% 0.46/0.67  thf('102', plain, ($false), inference('demod', [status(thm)], ['0', '101'])).
% 0.46/0.67  
% 0.46/0.67  % SZS output end Refutation
% 0.46/0.67  
% 0.46/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
